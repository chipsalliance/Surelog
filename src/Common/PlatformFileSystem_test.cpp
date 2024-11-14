/*
 Copyright 2022 chipsalliance

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
 */

/*
 * File:   FileSystem_test.cpp
 * Author: hs
 *
 * Created on June 1, 2022, 3:00 AM
 */

#include "Surelog/Common/PlatformFileSystem.h"

#include <gtest/gtest.h>
#include <uhdm/expr.h>

#include <cstddef>
#include <cstdint>
#include <iostream>
#include <set>
#include <string_view>
#include <utility>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/SymbolId.h"
#include "Surelog/Design/Design.h"
#include "Surelog/Library/Library.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/PreprocessFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/ExprEval.h>
#include <uhdm/design.h>
#include <uhdm/module_inst.h>
#include <uhdm/param_assign.h>
#include <uhdm/vpi_uhdm.h>
#include <uhdm/vpi_user.h>

#include <chrono>
#include <filesystem>
#include <fstream>
#include <map>
#include <regex>
#include <string>
#include <vector>

namespace SURELOG {

namespace fs = std::filesystem;

namespace {
class TestFileSystem : public PlatformFileSystem {
 public:
  explicit TestFileSystem(const fs::path &wd) : PlatformFileSystem(wd) {
    FileSystem::setInstance(this);
  }
  TestFileSystem() : TestFileSystem(fs::current_path()) {}
};

std::string getUniqueTempFileName() {
  return StrCat(::testing::UnitTest::GetInstance()->current_test_info()->name(),
                "-",
                std::chrono::steady_clock::now().time_since_epoch().count());
}

TEST(PlatformFileSystemTest, ReadWriteOperations) {
  // GTEST_SKIP() << "Temporarily skipped";
  const fs::path testdir = testing::TempDir();
  const fs::path filename = getUniqueTempFileName();
  const fs::path filepath = testdir / filename;
  const std::string_view line1 = "Line1: This file contains some bytes.";
  const std::string_view line2 = "Line2: This file contains more bytes.";
  const std::string_view line3 = "Line3: This is the last line.";

  std::unique_ptr<TestFileSystem> fileSystem(new TestFileSystem(testdir));
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);

  PathId fileId = fileSystem->toPathId(filepath.string(), symbolTable.get());

  EXPECT_FALSE(fileSystem->exists(fileId));
  EXPECT_FALSE(fileSystem->isDirectory(fileId));
  EXPECT_FALSE(fileSystem->isRegularFile(fileId));

  std::string content;
  EXPECT_FALSE(fileSystem->readContent(fileId, content));

  std::vector<std::string> lines;
  EXPECT_FALSE(fileSystem->readLines(fileId, lines));

  lines.emplace_back(line1);
  lines.emplace_back(line2);
  lines.emplace_back(line3);
  EXPECT_TRUE(fileSystem->writeLines(fileId, lines));

  EXPECT_TRUE(fileSystem->exists(fileId));
  EXPECT_FALSE(fileSystem->isDirectory(fileId));
  EXPECT_TRUE(fileSystem->isRegularFile(fileId));

  std::string actualContent;
  EXPECT_TRUE(fileSystem->readContent(fileId, actualContent));

  const std::string expectedContent =
      StrCat(line1, "\n", line2, "\n", line3, "\n");
  EXPECT_EQ(actualContent, expectedContent);

  std::vector<std::string> actualLines;
  EXPECT_TRUE(fileSystem->readLines(fileId, actualLines));

  const std::vector<std::string> &expectedLines = lines;
  EXPECT_EQ(actualLines, expectedLines);

  for (size_t i = 0, n = expectedLines.size(); i < n; ++i) {
    content.clear();
    EXPECT_TRUE(fileSystem->readLine(fileId, i + 1, content));
    EXPECT_EQ(content, expectedLines[i]);
  }
  content.clear();
  EXPECT_FALSE(fileSystem->readLine(fileId, expectedLines.size() + 1, content));
}

TEST(PlatformFileSystemTest, LoadSaveOperations) {
  // GTEST_SKIP() << "Temporarily skipped";
  const fs::path testdir = testing::TempDir();
  const fs::path filename = getUniqueTempFileName();
  const fs::path filepath = testdir / filename;
  const std::string_view lines =
      "Line1: This file contains some bytes.\n"
      "Line2: This file contains more bytes.\n"
      "Line3: This is the last line.";

  std::unique_ptr<TestFileSystem> fileSystem(new TestFileSystem(testdir));
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);

  PathId fileId = fileSystem->toPathId(filepath.string(), symbolTable.get());

  EXPECT_FALSE(fileSystem->exists(fileId));
  EXPECT_FALSE(fileSystem->isDirectory(fileId));
  EXPECT_FALSE(fileSystem->isRegularFile(fileId));

  std::vector<char> content;
  EXPECT_FALSE(fileSystem->loadContent(fileId, content));

  content.reserve(lines.length());
  std::copy(lines.begin(), lines.end(), std::back_inserter(content));
  EXPECT_TRUE(fileSystem->saveContent(fileId, content));

  EXPECT_TRUE(fileSystem->exists(fileId));
  EXPECT_FALSE(fileSystem->isDirectory(fileId));
  EXPECT_TRUE(fileSystem->isRegularFile(fileId));

  std::vector<char> actualContent;
  EXPECT_TRUE(fileSystem->loadContent(fileId, actualContent));

  const std::vector<char> &expectedContent = content;
  EXPECT_EQ(actualContent, expectedContent);
}

TEST(PlatformFileSystemTest, BasicFileOperations) {
  // GTEST_SKIP() << "Temporarily skipped";
  const fs::path testdir =
      fs::path(testing::TempDir()) / getUniqueTempFileName();
  const fs::path dirtest = testdir / "file-exist-dir";
  const std::string_view filename = "file-exists-test.txt";
  const fs::path filepath = dirtest / filename;
  const std::string_view dummy_data = "This file contains some bytes";

  std::unique_ptr<TestFileSystem> fileSystem(new TestFileSystem(testdir));
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);
  const PathId dirId =
      fileSystem->toPathId(dirtest.string(), symbolTable.get());
  const PathId fileId =
      fileSystem->toPathId(filepath.string(), symbolTable.get());

  EXPECT_FALSE(fileSystem->exists(dirId));
  EXPECT_TRUE(fileSystem->rmtree(dirId));  // not there: no error
  EXPECT_FALSE(fileSystem->isDirectory(dirId));

  EXPECT_TRUE(fileSystem->mkdirs(dirId));
  EXPECT_TRUE(fileSystem->isDirectory(dirId));
  EXPECT_FALSE(fileSystem->isRegularFile(dirId));

  EXPECT_FALSE(fileSystem->exists(fileId));
  EXPECT_TRUE(fileSystem->writeContent(fileId, dummy_data));
  EXPECT_TRUE(fileSystem->exists(fileId));
  EXPECT_FALSE(fileSystem->isDirectory(fileId));
  EXPECT_TRUE(fileSystem->isRegularFile(fileId));

  std::streamsize size = 0;
  EXPECT_TRUE(fileSystem->filesize(fileId, &size));
  EXPECT_EQ(size, dummy_data.size());

  std::string content;
  EXPECT_TRUE(fileSystem->readContent(fileId, content));
  EXPECT_EQ(content, dummy_data);

  EXPECT_FALSE(fileSystem->remove(dirId));  // Non-empty dir
  EXPECT_TRUE(fileSystem->rmtree(dirId));
  EXPECT_FALSE(fileSystem->exists(dirId));
}

TEST(PlatformFileSystemTest, LocateFile) {
  // GTEST_SKIP() << "Temporarily skipped";
  const std::string search_file = "search-file.txt";

  const fs::path testdir = FileSystem::normalize(testing::TempDir());
  const fs::path basedir = testdir / "locate-file-test";
  const fs::path path1 = basedir / "dir1";
  const fs::path path2 = basedir / "dir2";
  const fs::path actual_dir_1 = basedir / "actual-dir-1";
  const fs::path actual_dir_2 = basedir / "actual-dir-2";

  std::unique_ptr<TestFileSystem> fileSystem(new TestFileSystem(testdir));
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);

  const PathId pathId1 =
      fileSystem->toPathId(path1.string(), symbolTable.get());
  const PathId pathId2 =
      fileSystem->toPathId(path2.string(), symbolTable.get());
  const PathId dirId1 =
      fileSystem->toPathId(actual_dir_1.string(), symbolTable.get());
  const PathId dirId2 =
      fileSystem->toPathId(actual_dir_2.string(), symbolTable.get());

  EXPECT_TRUE(fileSystem->mkdirs(pathId1));
  EXPECT_TRUE(fileSystem->mkdirs(dirId1));
  EXPECT_TRUE(fileSystem->mkdirs(dirId2));

  const std::vector<PathId> directories{
      pathId1,
      pathId2,
      dirId1,
      dirId2,
  };

  // At this point, the file does not exist yet.
  const PathId not_exists =
      fileSystem->locate(search_file, directories, symbolTable.get());
  EXPECT_EQ(not_exists, BadPathId);

  const fs::path actual_loc_1 =
      FileSystem::normalize(actual_dir_1 / search_file);
  std::ofstream(actual_loc_1).close();

  PathId now_exists =
      fileSystem->locate(search_file, directories, symbolTable.get());
  EXPECT_NE(now_exists, BadPathId);
  EXPECT_EQ(fileSystem->toPlatformAbsPath(now_exists), actual_loc_1);

  PathId already_found =
      fileSystem->locate(search_file, directories, symbolTable.get());
  EXPECT_EQ(already_found, now_exists);

  const fs::path actual_loc_2 = actual_dir_2 / search_file;
  std::ofstream(actual_loc_2).close();

  PathId now_exists_1 =
      fileSystem->locate(search_file, directories, symbolTable.get());
  EXPECT_NE(now_exists_1, BadPathId);
  EXPECT_EQ(fileSystem->toPlatformAbsPath(now_exists_1), actual_loc_1);

  EXPECT_TRUE(fileSystem->remove(now_exists_1));
  EXPECT_FALSE(fileSystem->exists(now_exists_1));

  PathId now_exists_2 =
      fileSystem->locate(search_file, directories, symbolTable.get());
  EXPECT_NE(now_exists_2, BadPathId);
  EXPECT_EQ(fileSystem->toPlatformAbsPath(now_exists_2), actual_loc_2);

  EXPECT_TRUE(fileSystem->rmtree(
      fileSystem->toPathId(basedir.string(), symbolTable.get())));
}

TEST(PlatformFileSystemTest, PathRelations) {
  // GTEST_SKIP() << "Temporarily skipped";
  const fs::path testdir = FileSystem::normalize(testing::TempDir());

  std::unique_ptr<TestFileSystem> fileSystem(new TestFileSystem(testdir));
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);

  const fs::path base = FileSystem::normalize(testing::TempDir());
  PathId fileId =
      fileSystem->toPathId((base / "abc.txt").string(), symbolTable.get());
  PathId fileDirId = fileSystem->getParent(fileId, symbolTable.get());
  EXPECT_EQ(base, fileSystem->toPlatformAbsPath(fileDirId));

  PathId siblingId =
      fileSystem->getSibling(fileId, "def.txt", symbolTable.get());
  PathId siblingDirId = fileSystem->getParent(siblingId, symbolTable.get());
  EXPECT_EQ(fileDirId, siblingDirId);

  std::string_view filename =
      std::get<1>(fileSystem->getLeaf(fileId, symbolTable.get()));
  EXPECT_EQ(filename, "abc.txt");

  std::string_view extension =
      std::get<1>(fileSystem->getType(fileId, symbolTable.get()));
  EXPECT_EQ(extension, ".txt");

  PathId fileIdNoExt =
      fileSystem->toPathId((base / "abc").string(), symbolTable.get());
  std::string_view no_ext =
      std::get<1>(fileSystem->getType(fileIdNoExt, symbolTable.get()));
  EXPECT_EQ(no_ext, BadRawSymbol);
}

TEST(PlatformFileSystemTest, WorkingDirs_NonIdeal) {
  // GTEST_SKIP() << "Temporarily skipped";
  // A mock of uvm inclusion.
  // Test under third_party/tests/testname/subfolder1/subfolder2/testname.sl
  //
  // workspace
  //   tests
  //     testname
  //      subfolder_1
  //        subfolder_2
  //          testname.sl
  //        subfolder_3
  //          test_a.sv
  //      subfolder_4
  //        test_b.sv
  //      test_c.sv
  //   third_party
  //     uvm
  //       uvm_subfolder_a
  //        uvm_subfolder_b
  //          uvm_a.sv
  //        uvm_b.sv

  std::error_code ec;
  const fs::path programPath = FileSystem::getProgramPath();
  const fs::path wsdir =
      FileSystem::normalize(fs::path(testing::TempDir()) / "ws_nonideal");
  const fs::path testdir =
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_2";

  const std::vector<fs::path> dirs{
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_2",
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_3",
      wsdir / "tests" / "testname" / "subfolder_4",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a" / "uvm_subfolder_b",
  };

  const std::vector<fs::path> files{
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_3" /
          "test_a.sv",
      wsdir / "tests" / "testname" / "subfolder_4" / "test_b.sv",
      wsdir / "tests" / "testname" / "test_c.sv",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a" / "uvm_subfolder_b" /
          "uvm_a.sv",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a" / "uvm_b.sv"};

  for (const fs::path &dir : dirs) {
    fs::create_directories(dir, ec);
    EXPECT_FALSE(ec) << ec;
  }

  std::set<fs::path> expectedSourceFiles;
  for (const fs::path &file : files) {
    std::ofstream strm(file);
    EXPECT_TRUE(strm.is_open());
    strm.close();
    expectedSourceFiles.insert(file);
  }

  const std::vector<std::string> args{
      programPath.string(),
      "-nostdout",
      "../subfolder_3/test_a.sv",
      "../../subfolder_4/test_b.sv",
      "../../test_c.sv",
      "../../../../third_party/uvm/uvm_subfolder_a/uvm_subfolder_b/uvm_a.sv",
      "../../../../third_party/uvm/uvm_subfolder_a/uvm_b.sv"};

  std::vector<const char *> cargs;
  cargs.reserve(args.size());
  std::transform(args.begin(), args.end(), std::back_inserter(cargs),
                 [](const std::string &arg) { return arg.c_str(); });

  std::unique_ptr<TestFileSystem> fileSystem(new TestFileSystem(testdir));
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);
  std::unique_ptr<ErrorContainer> errors(new ErrorContainer(symbolTable.get()));
  std::unique_ptr<CommandLineParser> clp(
      new CommandLineParser(errors.get(), symbolTable.get()));
  clp->parseCommandLine(cargs.size(), cargs.data());

  fs::remove_all(wsdir, ec);
  EXPECT_FALSE(ec) << ec;

  const std::set<std::string> expectedFsWorkingDirs = {
      FileSystem::normalize(programPath.parent_path()).string(),
      FileSystem::normalize(wsdir).string(),
  };
  const std::set<std::string> actualFsWorkingDirs =
      fileSystem->getWorkingDirs();
  EXPECT_EQ(expectedFsWorkingDirs, actualFsWorkingDirs);

  const std::set<fs::path> expectedClpWorkingDirs{
      wsdir / "tests" / "testname",
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_2",
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_3",
      wsdir / "tests" / "testname" / "subfolder_4",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a" / "uvm_subfolder_b",
  };

  const PathIdVector &workingDirIds = clp->getWorkingDirs();
  std::set<fs::path> actualClpWorkingDirs;
  std::transform(
      workingDirIds.begin(), workingDirIds.end(),
      std::inserter(actualClpWorkingDirs, actualClpWorkingDirs.end()),
      [&](const PathId &id) { return fileSystem->toPath(id); });
  EXPECT_EQ(expectedClpWorkingDirs, actualClpWorkingDirs);
}

TEST(PlatformFileSystemTest, WorkingDirs_Ideal) {
  // GTEST_SKIP() << "Temporarily skipped";
  // A mock of uvm inclusion.
  // Test under third_party/tests/testname/subfolder1/subfolder2/testname.sl
  // Now with "ideal" -wd & -cd params so the output is better organized.
  //
  // workspace
  //   tests
  //     testname
  //      subfolder_1
  //        subfolder_2
  //          testname.sl
  //        subfolder_3
  //          test_a.sv
  //      subfolder_4
  //        test_b.sv
  //      test_c.sv
  //   third_party
  //     uvm
  //       uvm_subfolder_a
  //        uvm_subfolder_b
  //          uvm_a.sv
  //        uvm_b.sv

  std::error_code ec;
  const fs::path programPath = FileSystem::getProgramPath().string();
  const fs::path wsdir =
      FileSystem::normalize(fs::path(testing::TempDir()) / "ws_ideal");
  const fs::path testdir =
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_2";

  const std::vector<fs::path> dirs{
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_2",
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_3",
      wsdir / "tests" / "testname" / "subfolder_4",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a" / "uvm_subfolder_b",
  };

  const std::vector<fs::path> files{
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_3" /
          "test_a.sv",
      wsdir / "tests" / "testname" / "subfolder_4" / "test_b.sv",
      wsdir / "tests" / "testname" / "test_c.sv",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a" / "uvm_subfolder_b" /
          "uvm_a.sv",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a" / "uvm_b.sv"};

  for (const fs::path &dir : dirs) {
    fs::create_directories(dir, ec);
    EXPECT_FALSE(ec) << ec;
  }

  std::set<fs::path> expectedSourceFiles;
  for (const fs::path &file : files) {
    std::ofstream strm(file);
    EXPECT_TRUE(strm.is_open());
    strm.close();
    expectedSourceFiles.insert(file);
  }

  const std::vector<std::string> args{programPath.string(),
                                      "-nostdout",
                                      "-wd",
                                      "../..",
                                      "subfolder_1/subfolder_3/test_a.sv",
                                      "subfolder_4/test_b.sv",
                                      "test_c.sv",
                                      "-wd",
                                      "../../../../third_party",
                                      "-cd",
                                      "uvm/uvm_subfolder_a",
                                      "uvm_subfolder_b/uvm_a.sv",
                                      "uvm_b.sv"};

  std::vector<const char *> cargs;
  cargs.reserve(args.size());
  std::transform(args.begin(), args.end(), std::back_inserter(cargs),
                 [](const std::string &arg) { return arg.c_str(); });

  std::unique_ptr<TestFileSystem> fileSystem(new TestFileSystem(testdir));
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);
  std::unique_ptr<ErrorContainer> errors(new ErrorContainer(symbolTable.get()));
  std::unique_ptr<CommandLineParser> clp(
      new CommandLineParser(errors.get(), symbolTable.get()));
  clp->parseCommandLine(cargs.size(), cargs.data());

  fs::remove_all(wsdir, ec);
  EXPECT_FALSE(ec) << ec;

  const std::set<std::string> expectedFsWorkingDirs = {
      programPath.parent_path().string(),
      (wsdir / "tests" / "testname").string(),
      (wsdir / "third_party").string()};
  const std::set<std::string> actualFsWorkingDirs =
      fileSystem->getWorkingDirs();
  EXPECT_EQ(expectedFsWorkingDirs, actualFsWorkingDirs);

  const std::set<fs::path> expectedClpWorkingDirs{
      wsdir / "tests" / "testname",
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_2",
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_3",
      wsdir / "tests" / "testname" / "subfolder_4",
      wsdir / "third_party",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a" / "uvm_subfolder_b",
  };

  const PathIdVector &workingDirIds = clp->getWorkingDirs();
  std::set<fs::path> actualClpWorkingDirs;
  std::transform(
      workingDirIds.begin(), workingDirIds.end(),
      std::inserter(actualClpWorkingDirs, actualClpWorkingDirs.end()),
      [&](const PathId &id) { return fileSystem->toPath(id); });
  EXPECT_EQ(expectedClpWorkingDirs, actualClpWorkingDirs);
}

// This implementation is in no-way a complete or full-featured,
// but is a prototype to showcase the potential of FileSystem abstraction.
class InMemoryFileSystem : public TestFileSystem {
 public:
  using Files = std::map<fs::path, std::string>;
  using Directories = std::set<fs::path>;
  using OpenOutputFiles = std::map<const std::ostream *, fs::path>;

  explicit InMemoryFileSystem(const fs::path &cwd) : TestFileSystem(cwd) {
    FileSystem::setInstance(this);

    fs::path d1 = cwd;
    fs::path d2;
    while (d1 != d2) {
      m_directories.emplace(d1);
      d2 = d1;
      d1 = d1.parent_path();
    }
  }

  std::istream &openInput(const fs::path &filepath,
                          std::ios_base::openmode mode) override {
    if (!filepath.is_absolute()) {
      return m_nullInputStream;
    }

    std::scoped_lock<std::mutex> lock(m_inputStreamsMutex);
    Files::const_iterator it1 = m_files.find(filepath);
    if (it1 == m_files.end()) {
      return m_nullInputStream;
    }

    std::pair<InputStreams::iterator, bool> it2 =
        m_inputStreams.emplace(new std::istringstream(it1->second));

    return **it2.first;
  }

  bool close(std::istream &strm) override {
    std::scoped_lock<std::mutex> lock(m_inputStreamsMutex);

    InputStreams::const_iterator it =
        m_inputStreams.find((std::istringstream *)&strm);
    if (it != m_inputStreams.end()) {
      m_inputStreams.erase(it);
      return true;
    }

    return false;
  }

  std::ostream &openOutput(const fs::path &filepath,
                           std::ios_base::openmode mode) override {
    if (!filepath.is_absolute()) {
      return m_nullOutputStream;
    }

    std::scoped_lock<std::mutex> lock(m_outputStreamsMutex);

    std::string content;
    if ((mode & std::ios_base::app) == std::ios_base::app) {
      Files::const_iterator it2 = m_files.find(filepath);
      if (it2 != m_files.end()) {
        content = it2->second;
      }
    }

    std::pair<OutputStreams::iterator, bool> it =
        m_outputStreams.emplace(new std::ostringstream(content, mode));
    m_openOutputFiles.emplace(it.first->get(), filepath);

    return **it.first;
  }

  bool saveContent(PathId fileId, const char *content, std::streamsize length,
                   bool useTemp) override {
    // Can't use temporary with virtual file system
    return TestFileSystem::saveContent(fileId, content, length, false);
  }

  bool close(std::ostream &strm) override {
    std::scoped_lock<std::mutex> lock(m_outputStreamsMutex);

    std::string s = ((std::ostringstream *)&strm)->str();

    OpenOutputFiles::const_iterator it1 = m_openOutputFiles.find(&strm);
    if (it1 != m_openOutputFiles.end()) {
      m_files.insert_or_assign(it1->second,
                               ((std::ostringstream *)&strm)->str());

      OutputStreams::const_iterator it2 =
          m_outputStreams.find((std::ostringstream *)&strm);
      if (it2 != m_outputStreams.end()) {
        m_outputStreams.erase(it2);
      }

      m_openOutputFiles.erase(it1);
      return true;
    }

    return false;
  }

  PathId getProgramFile(std::string_view hint,
                        SymbolTable *symbolTable) override {
    if (!hint.empty()) {
      std::error_code ec;
      m_lastModifiedTime = fs::last_write_time(hint, ec);
    }

    return TestFileSystem::getProgramFile(hint, symbolTable);
  }

  bool rename(PathId whatId, PathId toId) override {
    if (!whatId || !toId) return false;

    const fs::path what = toPath(whatId);
    const fs::path to = toPath(toId);
    if (what.empty() || to.empty()) return false;

    std::scoped_lock<std::mutex> lock(m_mutex);

    Directories::const_iterator dirIt = m_directories.find(what);
    if (dirIt != m_directories.end()) {
      const Directories directories = m_directories;
      for (const fs::path &dir : directories) {
        if (is_subpath(what, dir)) {
          m_directories.emplace(to / dir.lexically_relative(what));
          m_directories.erase(m_directories.find(dir));
        }
      }
    } else {
      Files::const_iterator fileIt = m_files.find(what);
      if (fileIt != m_files.end()) {
        m_files.emplace(to, fileIt->second);
        m_files.erase(fileIt);
        return true;
      }
    }

    return false;
  }

  bool remove(PathId fileId) override {
    if (!fileId) return false;

    const fs::path file = toPath(fileId);
    if (file.empty()) return false;

    std::scoped_lock<std::mutex> lock(m_mutex);

    Files::const_iterator it = m_files.find(file);
    if (it != m_files.end()) {
      m_files.erase(it);
      return true;
    }

    return false;
  }

  bool mkdir(PathId dirId) override {
    if (!dirId) return false;

    const fs::path dir = toPath(dirId);
    if (dir.empty()) return false;

    std::scoped_lock<std::mutex> lock(m_mutex);
    m_directories.insert(dir);
    return true;
  }

  bool rmdir(PathId dirId) override {
    if (!dirId) return false;

    const fs::path dir = toPath(dirId);
    if (dir.empty()) return false;

    std::scoped_lock<std::mutex> lock(m_mutex);

    Directories::const_iterator it = m_directories.find(dir);
    if (it != m_directories.end()) {
      m_directories.erase(it);
      return true;
    }

    return false;
  }

  bool mkdirs(PathId dirId) override {
    if (!dirId) return false;

    const fs::path dir = toPath(dirId);
    if (dir.empty()) return false;

    std::scoped_lock<std::mutex> lock(m_mutex);

    fs::path d1 = dir;
    fs::path d2;
    while ((d1 != d2) && m_directories.insert(d1).second) {
      d2 = d1;
      d1 = d1.parent_path();
    }

    return true;
  }

  bool rmtree(PathId dirId) override {
    if (!dirId) return false;

    const fs::path dir = toPath(dirId);
    if (dir.empty()) return false;

    std::scoped_lock<std::mutex> lock(m_mutex);

    if (m_directories.find(dir) == m_directories.end()) return true;

    Directories::const_iterator it = m_directories.begin();
    const Directories::const_iterator end = m_directories.end();
    while (it != end) {
      const fs::path &existing = *it;

      if (is_subpath(dir, existing)) {
        it = m_directories.erase(it);
      } else {
        ++it;
      }
    }

    return true;
  }

  bool exists(PathId id) override {
    if (!id) return false;

    const fs::path path = toPath(id);
    if (path.empty()) return false;

    std::scoped_lock<std::mutex> lock(m_mutex);
    return (m_directories.find(path) != m_directories.end()) ||
           (m_files.find(path) != m_files.end());
  }

  bool exists(PathId parentId, std::string_view descendant) override {
    if (!parentId || descendant.empty()) return false;

    const fs::path parentPath = toPath(parentId);
    if (parentPath.empty()) return false;

    const fs::path path = parentPath / descendant;

    std::scoped_lock<std::mutex> lock(m_mutex);
    return (m_directories.find(path) != m_directories.end()) ||
           (m_files.find(path) != m_files.end());
  }

  bool isDirectory(PathId id) override {
    if (!id) return false;

    const fs::path dirpath = toPath(id);
    if (dirpath.empty()) return false;

    std::scoped_lock<std::mutex> lock(m_mutex);
    return (m_directories.find(dirpath) != m_directories.end());
  }

  bool isRegularFile(PathId id) override {
    if (!id) return false;

    const fs::path filepath = toPath(id);
    if (filepath.empty()) return false;

    std::scoped_lock<std::mutex> lock(m_mutex);
    return (m_files.find(filepath) != m_files.end());
  }

  PathId locate(std::string_view suffix, const PathIdVector &directories,
                SymbolTable *symbolTable) override {
    if (suffix.empty() || directories.empty()) return BadPathId;

    std::scoped_lock<std::mutex> lock(m_mutex);

    for (const PathId &dirId : directories) {
      const fs::path dir = toPath(dirId);
      if (!dir.empty()) {
        const fs::path file = dir / suffix;

        if (m_files.find(file) != m_files.end()) {
          return toPathId(file.string(), symbolTable);
        }
      }
    }

    return BadPathId;
  }

  bool filesize(PathId fileId, std::streamsize *result) override {
    if (!fileId) return false;

    const fs::path file = toPath(fileId);
    if (file.empty()) return false;

    std::scoped_lock<std::mutex> lock(m_mutex);

    Files::const_iterator it = m_files.find(file);
    if (it != m_files.end()) {
      if (result != nullptr) {
        *result = it->second.size();
      }
      return true;
    }

    return false;
  }

  PathIdVector &collect(PathId dirId, SymbolTable *symbolTable,
                        PathIdVector &container) override {
    if (!dirId) return container;

    const fs::path dir = toPath(dirId);
    if (dir.empty()) return container;

    std::scoped_lock<std::mutex> lock(m_mutex);

    for (Files::const_reference entry : m_files) {
      const fs::path &file = entry.first;

      if (is_subpath(dir, file)) {
        container.emplace_back(toPathId(file.string(), symbolTable));
      }
    }

    return container;
  }

  PathIdVector &collect(PathId dirId, std::string_view extension,
                        SymbolTable *symbolTable,
                        PathIdVector &container) override {
    if (!dirId || extension.empty()) return container;

    const fs::path dirpath = toPath(dirId);
    if (dirpath.empty()) return container;

    std::scoped_lock<std::mutex> lock(m_mutex);

    Directories::const_iterator it = m_directories.find(dirpath);
    if (it != m_directories.end()) {
      for (Files::const_reference &entry : m_files) {
        const fs::path &filepath = entry.first;
        if (filepath.extension() == extension) {
          container.emplace_back(toPathId(filepath.string(), symbolTable));
        }
      }
    }

    return container;
  }

  PathIdVector &matching(PathId dirId, std::string_view pattern,
                         SymbolTable *symbolTable,
                         PathIdVector &container) override {
    if (!dirId) return container;

    // ?   single character wildcard (matches any single character)
    // *   multiple character wildcard (matches any number of characters in a
    // directory/file name)
    // ... hierarchical wildcard (matches any number of hierarchical
    // directories)
    // ..  specifies the parent directory
    // .   specifies the directory containing the lib.map
    // Paths that end in / shall include all files in the specified directory.
    // Identical to / * Paths that do not begin with / are relative to the
    // directory in which the current lib.map file is located.

    std::error_code ec;
    fs::path prefix = toPath(dirId);
    if (prefix.empty()) return container;

    fs::path suffix;
    for (const fs::path &part : fs::path(pattern)) {
      if (part == ".") {
        continue;
      } else if (!suffix.empty()) {
        suffix /= part;
      } else if (part.string().find_first_of(".?*") == std::string::npos) {
        prefix /= part;
      } else {
        suffix /= part;
      }
    }

    if (suffix.empty()) {
      return collect(toPathId(prefix.string(), symbolTable), symbolTable,
                     container);
    }

    prefix = normalize(prefix);
    if (ec) return container;

    const std::string separator(1, fs::path::preferred_separator);
    const std::string escaped = "\\" + separator;

    std::string regexp = suffix.string();
    regexp = StringUtils::replaceAll(regexp, separator,
                                     escaped);  // escape separators
    regexp =
        StringUtils::replaceAll(regexp, StrCat("...", escaped),
                                StrCat(R"([a-zA-Z0-9_\-.)", escaped, R"(]+)",
                                       escaped));  // separator allowed
    regexp = StringUtils::replaceAll(
        regexp, StrCat("..", escaped),
        StrCat(R"([a-zA-Z0-9_\-.]+)", escaped, R"([a-zA-Z0-9_\-.]+)",
               escaped));  // separator NOT allowed
    regexp = StringUtils::replaceAll(regexp, ".", "\\.");  // escape it
    regexp = StringUtils::replaceAll(regexp, "?",
                                     R"([a-zA-Z0-9_\-\.])");  // at most one
    regexp = StringUtils::replaceAll(
        regexp, "*", StrCat("[^", escaped, "]*"));  // free for all

    const std::regex regex(regexp);
    for (Files::const_reference entry : m_files) {
      const fs::path &absolute = entry.first;
      const std::string relative = fs::relative(absolute, prefix, ec).string();
      std::smatch match;
      if (!ec && std::regex_match(relative, match, regex)) {
        container.emplace_back(toPathId(absolute.string(), symbolTable));
      }
    }

    return container;
  }

  fs::file_time_type modtime(PathId fileId,
                             fs::file_time_type defaultOnFail) override {
    return m_lastModifiedTime;
  }

  std::mutex m_mutex;

  Files m_files;
  Directories m_directories;
  OpenOutputFiles m_openOutputFiles;
  fs::file_time_type m_lastModifiedTime;
};

TEST(PlatformFileSystemTest, InMemoryTest) {
  // GTEST_SKIP() << "Temporarily skipped";
#if defined(_WIN32)
  const fs::path inputdir = "C:\\a\\b\\c\\input";
  const fs::path outputdir = "C:\\a\\b\\c\\output";
#else
  const fs::path inputdir = "/a/b/c/input";
  const fs::path outputdir = "/a/b/c/output";
#endif

  const fs::path programPath = FileSystem::getProgramPath();

  InMemoryFileSystem *const fileSystem = new InMemoryFileSystem(inputdir);
  SymbolTable *const symbolTable = new SymbolTable;

  fileSystem->getWorkingDir(inputdir.string(), symbolTable);

  const fs::path srcfile = inputdir / "x.sv";
  PathId srcFileId = fileSystem->getWorkingDir(srcfile.string(), symbolTable);
  std::ostream &srcstrm = fileSystem->openForWrite(srcFileId);
  srcstrm << "package pkg;" << std::endl
          << "  typedef struct packed {" << std::endl
          << "    logic [7:0] x;" << std::endl
          << "    logic z;" << std::endl
          << "  } struct_t;" << std::endl
          << "endpackage : pkg" << std::endl
          << std::endl
          << "module dut #(parameter int Width = 1) ();" << std::endl
          << "endmodule" << std::endl
          << std::endl
          << "module top(input pkg::struct_t in);" << std::endl
          << "  localparam int SyncWidth = $bits({in, in.x});" << std::endl
          << "  dut #(.Width($bits({in.x}))) dut1();" << std::endl
          << "  dut #(.Width($bits({in}))) dut2();" << std::endl
          << "  dut #(.Width($bits(in))) dut3();" << std::endl
          << "  dut #(.Width($bits({in, in.x}))) dut4();" << std::endl
          << "endmodule // top" << std::endl;
  fileSystem->close(srcstrm);

  std::vector<std::string> args{programPath.string(), "-nostdout", "-o",
                                outputdir.string(), srcfile.string()};
  std::vector<const char *> cargs;
  std::transform(args.begin(), args.end(), std::back_inserter(cargs),
                 [](const std::string &arg) { return arg.data(); });

  ErrorContainer *const errors = new ErrorContainer(symbolTable);
  CommandLineParser *const clp =
      new CommandLineParser(errors, symbolTable, false, false);
  clp->parseCommandLine(cargs.size(), cargs.data());
  clp->setCacheAllowed(false);
  clp->setParse(true);
  clp->setCompile(true);
  clp->setElabUhdm(true);
  clp->setWriteUhdm(false);
  clp->fullSVMode(true);
  clp->setWriteCache(false);

  Compiler *const compiler = new Compiler(clp, errors, symbolTable);
  compiler->compile();
  Design *design = compiler->getDesign();
  EXPECT_NE(design, nullptr);

  const auto &compileSourceFiles = design->getAllFileContents();
  EXPECT_EQ(compileSourceFiles.size(), 2);

  CompileDesign *const compileDesign = compiler->getCompileDesign();
  EXPECT_NE(compileDesign, nullptr);

  const auto &insts = design->getTopLevelModuleInstances();
  ModuleInstance *top = nullptr;
  if (!insts.empty()) {
    top = insts.front();
  }
  EXPECT_NE(top, nullptr);

  vpiHandle hdesign = compiler->getUhdmDesign();
  UHDM::design *const udesign = UhdmDesignFromVpiHandle(hdesign);
  for (auto topMod : *udesign->TopModules()) {
    for (auto passign : *topMod->Param_assigns()) {
      UHDM::expr *rhs = (UHDM::expr *)passign->Rhs();
      bool invalidValue = false;
      UHDM::ExprEval eval;
      EXPECT_EQ(eval.get_value(invalidValue, rhs), 17);
    }
    for (auto sub : *topMod->Modules()) {
      const std::string_view instName = sub->VpiName();
      for (auto passign : *sub->Param_assigns()) {
        UHDM::expr *rhs = (UHDM::expr *)passign->Rhs();
        bool invalidValue = false;
        UHDM::ExprEval eval;
        uint64_t val = eval.get_value(invalidValue, rhs);
        if (instName == "dut1") {
          EXPECT_EQ(val, 8);
        } else if (instName == "dut2") {
          EXPECT_EQ(val, 9);
        } else if (instName == "dut3") {
          EXPECT_EQ(val, 9);
        } else if (instName == "dut4") {
          EXPECT_EQ(val, 17);
        }
      }
    }
  }

  delete compiler;
  delete clp;
  delete symbolTable;
  delete errors;
  delete fileSystem;
}

TEST(PlatformFileSystemTest, PortableCacheTest) {
  // Intent: Cache should be usuable if either the
  // source or the cache is moved to a new location.
  const fs::path testdir = testing::TempDir();
  const fs::path kBaseDir = testdir / "PortableCacheTest";
  const fs::path kInputDir_run1 = kBaseDir / "input1";
  const fs::path kInputDir_run2 = kBaseDir / "input2";
  const fs::path kOutputDir_run1 = kBaseDir / "output1";
  const fs::path kOutputDir_run2 = kBaseDir / "output2";
  const fs::path kProgramPath = FileSystem::getProgramPath();
  const std::string_view kHeadersDirName = "headers";
  const std::string_view kHeaderFileName = "header.sv";
  const std::string_view kSourceFileName = "source.sv";

  // Remove any remanants from past runs and ignore any related errors!
  std::error_code ec;
  fs::remove_all(kBaseDir, ec);

  // Run 1: Create cache in kOutputDir_run1 using source at kInputDir_run1
  {
    std::unique_ptr<FileSystem> fileSystem(new TestFileSystem(kInputDir_run1));
    std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);
    std::unique_ptr<ErrorContainer> errors(
        new ErrorContainer(symbolTable.get()));
    std::unique_ptr<CommandLineParser> clp(
        new CommandLineParser(errors.get(), symbolTable.get(), false, false));

    const PathId inputDirId =
        fileSystem->toPathId(kInputDir_run1.string(), symbolTable.get());
    EXPECT_TRUE(fileSystem->mkdirs(inputDirId));

    const PathId headerDirId = fileSystem->toPathId(
        (kInputDir_run1 / kHeadersDirName).string(), symbolTable.get());
    EXPECT_TRUE(fileSystem->mkdirs(headerDirId));

    const PathId headerFileId =
        fileSystem->getChild(headerDirId, kHeaderFileName, symbolTable.get());
    EXPECT_TRUE(headerFileId);

    std::ostream &strm1 = fileSystem->openForWrite(headerFileId);
    EXPECT_TRUE(strm1.good());
    strm1 << "function automatic int get_1();" << std::endl
          << "  return 1;" << std::endl
          << "endfunction" << std::endl;
    fileSystem->close(strm1);

    const PathId sourceFileId = fileSystem->toPathId(
        (kInputDir_run1 / kSourceFileName).string(), symbolTable.get());
    EXPECT_TRUE(sourceFileId);

    std::ostream &strm2 = fileSystem->openForWrite(sourceFileId);
    EXPECT_TRUE(strm2.good());
    strm2 << "`include \"header.sv\"" << std::endl
          << std::endl
          << "module top(output int o);" << std::endl
          << "  assign o = get_1();" << std::endl
          << "endmodule" << std::endl;
    fileSystem->close(strm2);

    const std::vector<std::string> args{
        kProgramPath.string(),
        "-nostdout",
        "-parse",
        "-nobuiltin",
        std::string("-I").append(fileSystem->toPath(headerDirId)),
        std::string(fileSystem->toPath(sourceFileId)),
        std::string(fileSystem->toPath(headerFileId)),
        "-o",
        kOutputDir_run1.string()};
    std::vector<const char *> cargs;
    std::transform(args.begin(), args.end(), std::back_inserter(cargs),
                   [](const std::string &arg) { return arg.data(); });
    clp->parseCommandLine(cargs.size(), cargs.data());

    std::unique_ptr<Compiler> compiler(
        new Compiler(clp.get(), errors.get(), symbolTable.get()));
    compiler->compile();

    PathId cacheDirId =
        fileSystem->getCacheDir(clp->fileunit(), symbolTable.get());
    EXPECT_TRUE(cacheDirId);
    EXPECT_TRUE(fileSystem->isDirectory(cacheDirId));

    for (CompileSourceFile *csf : compiler->getCompileSourceFiles()) {
      PreprocessFile *const ppFile = csf->getPreprocessor();
      ParseFile *const parseFile = csf->getParser();

      SymbolId libraryNameId =
          csf->getPreprocessor()->getLibrary()->getNameId();
      EXPECT_TRUE(libraryNameId);

      PathId ppCacheFileId =
          fileSystem->getPpCacheFile(clp->fileunit(), csf->getFileId(),
                                     libraryNameId, false, symbolTable.get());
      EXPECT_TRUE(ppCacheFileId);
      EXPECT_TRUE(fileSystem->isRegularFile(ppCacheFileId));

      PathId parseCacheFileId = fileSystem->getParseCacheFile(
          clp->fileunit(), csf->getPpOutputFileId(), libraryNameId, false,
          symbolTable.get());
      EXPECT_TRUE(parseCacheFileId);
      EXPECT_TRUE(fileSystem->isRegularFile(parseCacheFileId));

      EXPECT_FALSE(ppFile->usingCachedVersion()) << PathIdPP(ppCacheFileId);
      EXPECT_FALSE(parseFile->usingCachedVersion())
          << PathIdPP(parseCacheFileId);
    }
  }

  // Move both the source and cache to new location

  fs::rename(kInputDir_run1, kInputDir_run2, ec);
  EXPECT_FALSE(ec) << ec;

  fs::rename(kOutputDir_run1, kOutputDir_run2, ec);
  EXPECT_FALSE(ec) << ec;

  // Run 2: Setup a remap from original location to new location and with that
  // setup, the cache should be loaded successfully.
  {
    std::unique_ptr<FileSystem> fileSystem(new TestFileSystem(kInputDir_run2));
    std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);
    std::unique_ptr<ErrorContainer> errors(
        new ErrorContainer(symbolTable.get()));
    std::unique_ptr<CommandLineParser> clp(
        new CommandLineParser(errors.get(), symbolTable.get(), false, false));

    const PathId headerDirId = fileSystem->toPathId(
        (kInputDir_run2 / kHeadersDirName).string(), symbolTable.get());
    EXPECT_TRUE(fileSystem->isDirectory(headerDirId));

    const PathId headerFileId =
        fileSystem->getChild(headerDirId, kHeaderFileName, symbolTable.get());
    EXPECT_TRUE(headerFileId);
    EXPECT_TRUE(fileSystem->isRegularFile(headerFileId));

    const PathId sourceFileId = fileSystem->toPathId(
        (kInputDir_run2 / kSourceFileName).string(), symbolTable.get());
    EXPECT_TRUE(sourceFileId);
    EXPECT_TRUE(fileSystem->isRegularFile(sourceFileId));

    EXPECT_TRUE(fileSystem->addMapping(kInputDir_run1.string(),
                                       kInputDir_run2.string()));

    const std::vector<std::string> args{
        FileSystem::getProgramPath().string(),
        "-nostdout",
        "-parse",
        "-nobuiltin",
        std::string("-I").append(fileSystem->toPath(headerDirId)),
        std::string(fileSystem->toPath(headerFileId)),
        std::string(fileSystem->toPath(sourceFileId)),
        "-o",
        kOutputDir_run2.string()};
    std::vector<const char *> cargs;
    std::transform(args.begin(), args.end(), std::back_inserter(cargs),
                   [](const std::string &arg) { return arg.data(); });
    clp->parseCommandLine(cargs.size(), cargs.data());

    std::unique_ptr<Compiler> compiler(
        new Compiler(clp.get(), errors.get(), symbolTable.get()));
    compiler->compile();

    PathId cacheDirId =
        fileSystem->getCacheDir(clp->fileunit(), symbolTable.get());
    EXPECT_TRUE(cacheDirId);
    EXPECT_TRUE(fileSystem->isDirectory(cacheDirId));

    for (CompileSourceFile *csf : compiler->getCompileSourceFiles()) {
      PreprocessFile *const ppFile = csf->getPreprocessor();
      ParseFile *const parseFile = csf->getParser();

      SymbolId libraryNameId =
          csf->getPreprocessor()->getLibrary()->getNameId();
      EXPECT_TRUE(libraryNameId);

      PathId ppCacheFileId =
          fileSystem->getPpCacheFile(clp->fileunit(), csf->getFileId(),
                                     libraryNameId, false, symbolTable.get());
      EXPECT_TRUE(ppCacheFileId);
      EXPECT_TRUE(fileSystem->isRegularFile(ppCacheFileId));

      PathId parseCacheFileId = fileSystem->getParseCacheFile(
          clp->fileunit(), csf->getPpOutputFileId(), libraryNameId, false,
          symbolTable.get());
      EXPECT_TRUE(parseCacheFileId);
      EXPECT_TRUE(fileSystem->isRegularFile(parseCacheFileId));

      EXPECT_TRUE(ppFile->usingCachedVersion())
          << PathIdPP(csf->getFileId()) << ", " << PathIdPP(ppCacheFileId);
      EXPECT_TRUE(parseFile->usingCachedVersion())
          << PathIdPP(csf->getPpOutputFileId()) << ", "
          << PathIdPP(parseCacheFileId);
    }
  }

  fs::remove_all(kBaseDir, ec);
  EXPECT_FALSE(ec) << ec;
}
}  // namespace
}  // namespace SURELOG
