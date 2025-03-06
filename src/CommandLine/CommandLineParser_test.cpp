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
 * File:   CommandLineParser_test.cpp
 * Author: hs
 *
 * Created on August 10, 2022, 1:16 AM
 */

#include "Surelog/CommandLine/CommandLineParser.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <memory>
#include <set>
#include <string>
#include <vector>

#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/PlatformFileSystem.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/SourceCompile/SymbolTable.h"

namespace SURELOG {

namespace fs = std::filesystem;

namespace {
class TestFileSystem final : public PlatformFileSystem {
 public:
  explicit TestFileSystem(const fs::path& wd) : PlatformFileSystem(wd) {
    FileSystem::setInstance(this);
  }
  TestFileSystem() : TestFileSystem(fs::current_path()) {}
};

TEST(CommandLineParserTest, WorkingDirectories1) {
  // Trivial case: One root working directory and many relative sub directories
  //
  // dira
  //   dirb1
  //     dirc
  //       file_a.sv
  //       file_b.sv
  //     dird
  //       file.sv
  //   dirb2
  //     dirc
  //       file_a.sv
  //       file_b.sv
  //     dird
  //       file.sv

  std::error_code ec;
  const fs::path programPath = FileSystem::getProgramPath().string();
  const fs::path testdir = FileSystem::normalize(testing::TempDir()) / "wd1";

  const std::vector<fs::path> dirs{
      testdir / "dira" / "dirb1" / "dirc",
      testdir / "dira" / "dirb1" / "dird",
      testdir / "dira" / "dirb2" / "dirc",
      testdir / "dira" / "dirb2" / "dird",
  };

  bool toggle = true;
  std::set<fs::path> expectedSourceFiles;
  for (const fs::path& dir : dirs) {
    fs::create_directories(dir, ec);
    EXPECT_FALSE(ec) << ec;

    if (toggle) {
      fs::path filepath_a = dir / "file_a.sv";
      std::ofstream strm_a(filepath_a);
      EXPECT_TRUE(strm_a.is_open());
      strm_a.close();

      fs::path filepath_b = dir / "file_b.sv";
      std::ofstream strm_b(filepath_b);
      EXPECT_TRUE(strm_b.is_open());
      strm_b.close();
      expectedSourceFiles.insert(filepath_a);
      expectedSourceFiles.insert(filepath_b);
    } else {
      fs::path filepath = dir / "file.sv";
      std::ofstream strm(filepath);
      EXPECT_TRUE(strm.is_open());
      strm.close();
      expectedSourceFiles.insert(filepath);
    }

    toggle = !toggle;
  }

  const std::vector<std::string> args{
      programPath.string(),
      "-nostdout",
      "-wd",
      "dira",
      "-cd",
      "dirb1",
      "dirc/file_a.sv",
      "dirc/file_b.sv",
      "dird/file.sv",
      "-cd",
      "dirb2",
      "dirc/file_a.sv",
      "dirc/file_b.sv",
      "dird/file.sv",
  };

  const std::set<fs::path> expectedWorkingDirs{
      testdir,
      testdir / "dira",
      testdir / "dira" / "dirb1",
      testdir / "dira" / "dirb1" / "dirc",
      testdir / "dira" / "dirb1" / "dird",
      testdir / "dira" / "dirb2",
      testdir / "dira" / "dirb2" / "dirc",
      testdir / "dira" / "dirb2" / "dird"};

  std::vector<const char*> cargs;
  cargs.reserve(args.size());
  std::transform(args.begin(), args.end(), std::back_inserter(cargs),
                 [](const std::string& arg) { return arg.c_str(); });

  std::unique_ptr<TestFileSystem> fileSystem(new TestFileSystem(testdir));
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);
  std::unique_ptr<ErrorContainer> errors(new ErrorContainer(symbolTable.get()));
  std::unique_ptr<CommandLineParser> clp(
      new CommandLineParser(errors.get(), symbolTable.get()));
  clp->parseCommandLine(cargs.size(), cargs.data());

  fs::remove_all(testdir / "dira", ec);
  EXPECT_FALSE(ec) << ec;

  const PathIdVector& workingDirIds = clp->getWorkingDirs();
  std::set<fs::path> actualWorkingDirs;
  std::transform(workingDirIds.begin(), workingDirIds.end(),
                 std::inserter(actualWorkingDirs, actualWorkingDirs.end()),
                 [&](const PathId& id) { return fileSystem->toPath(id); });
  EXPECT_EQ(expectedWorkingDirs, actualWorkingDirs);

  const PathIdVector& sourceFileIds = clp->getSourceFiles();
  std::set<fs::path> actualSourceFiles;
  std::transform(sourceFileIds.begin(), sourceFileIds.end(),
                 std::inserter(actualSourceFiles, actualSourceFiles.end()),
                 [&](const PathId& id) { return fileSystem->toPath(id); });
  EXPECT_EQ(expectedSourceFiles, actualSourceFiles);
}

TEST(CommandLineParserTest, WorkingDirectories2) {
  // Trivial case: One root working directory and many relative sub directories
  // Input source file paths are, however, all relative to each other
  //
  // dira
  //   dirb1
  //     dirc
  //       file_a.sv
  //       file_b.sv
  //     dird
  //       file.sv
  //   dirb2
  //     dirc
  //       file_a.sv
  //       file_b.sv
  //     dird
  //       file.sv

  std::error_code ec;
  const fs::path programPath = FileSystem::getProgramPath().string();
  const fs::path testdir = FileSystem::normalize(testing::TempDir()) / "wd2";

  const std::vector<fs::path> dirs{
      testdir / "dira" / "dirb1" / "dirc",
      testdir / "dira" / "dirb1" / "dird",
      testdir / "dira" / "dirb2" / "dirc",
      testdir / "dira" / "dirb2" / "dird",
  };

  bool toggle = true;
  std::set<fs::path> expectedSourceFiles;
  for (const fs::path& dir : dirs) {
    fs::create_directories(dir, ec);
    EXPECT_FALSE(ec) << ec;

    if (toggle) {
      fs::path filepath_a = dir / "file_a.sv";
      std::ofstream strm_a(filepath_a);
      EXPECT_TRUE(strm_a.is_open());
      strm_a.close();

      fs::path filepath_b = dir / "file_b.sv";
      std::ofstream strm_b(filepath_b);
      EXPECT_TRUE(strm_b.is_open());
      strm_b.close();
      expectedSourceFiles.insert(filepath_a);
      expectedSourceFiles.insert(filepath_b);
    } else {
      fs::path filepath = dir / "file.sv";
      std::ofstream strm(filepath);
      EXPECT_TRUE(strm.is_open());
      strm.close();
      expectedSourceFiles.insert(filepath);
    }

    toggle = !toggle;
  }

  const std::vector<std::string> args{
      programPath.string(),
      "-nostdout",
      "-wd",
      "dira",
      "-cd",
      "dirb1",
      "../dirb2/dirc/file_a.sv",
      "../dirb2/dirc/file_b.sv",
      "../dirb2/dird/file.sv",
      "-cd",
      "dirb2",
      "../dirb1/dirc/file_a.sv",
      "../dirb1/dirc/file_b.sv",
      "../dirb1/dird/file.sv",
  };

  const std::set<fs::path> expectedWorkingDirs{
      testdir,
      testdir / "dira",
      testdir / "dira" / "dirb1",
      testdir / "dira" / "dirb1" / "dirc",
      testdir / "dira" / "dirb1" / "dird",
      testdir / "dira" / "dirb2",
      testdir / "dira" / "dirb2" / "dirc",
      testdir / "dira" / "dirb2" / "dird"};

  std::vector<const char*> cargs;
  cargs.reserve(args.size());
  std::transform(args.begin(), args.end(), std::back_inserter(cargs),
                 [](const std::string& arg) { return arg.c_str(); });

  std::unique_ptr<TestFileSystem> fileSystem(new TestFileSystem(testdir));
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);
  std::unique_ptr<ErrorContainer> errors(new ErrorContainer(symbolTable.get()));
  std::unique_ptr<CommandLineParser> clp(
      new CommandLineParser(errors.get(), symbolTable.get()));
  clp->parseCommandLine(cargs.size(), cargs.data());

  fs::remove_all(testdir / "dira", ec);
  EXPECT_FALSE(ec) << ec;

  const PathIdVector& workingDirIds = clp->getWorkingDirs();
  std::set<fs::path> actualWorkingDirs;
  std::transform(workingDirIds.begin(), workingDirIds.end(),
                 std::inserter(actualWorkingDirs, actualWorkingDirs.end()),
                 [&](const PathId& id) { return fileSystem->toPath(id); });
  EXPECT_EQ(expectedWorkingDirs, actualWorkingDirs);

  const PathIdVector& sourceFileIds = clp->getSourceFiles();
  std::set<fs::path> actualSourceFiles;
  std::transform(sourceFileIds.begin(), sourceFileIds.end(),
                 std::inserter(actualSourceFiles, actualSourceFiles.end()),
                 [&](const PathId& id) { return fileSystem->toPath(id); });
  EXPECT_EQ(expectedSourceFiles, actualSourceFiles);
}

TEST(CommandLineParserTest, WorkingDirectories3) {
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
  const fs::path programPath = FileSystem::getProgramPath().string();
  const fs::path wsdir =
      FileSystem::normalize(fs::path(testing::TempDir()) / "ws3");
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

  for (const fs::path& dir : dirs) {
    fs::create_directories(dir, ec);
    EXPECT_FALSE(ec) << ec;
  }

  std::set<fs::path> expectedSourceFiles;
  for (const fs::path& file : files) {
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

  const std::set<fs::path> expectedWorkingDirs{
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_2",
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_3",
      wsdir / "tests" / "testname" / "subfolder_4",
      wsdir / "tests" / "testname",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a" / "uvm_subfolder_b",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a"};

  std::vector<const char*> cargs;
  cargs.reserve(args.size());
  std::transform(args.begin(), args.end(), std::back_inserter(cargs),
                 [](const std::string& arg) { return arg.c_str(); });

  std::unique_ptr<TestFileSystem> fileSystem(new TestFileSystem(testdir));
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);
  std::unique_ptr<ErrorContainer> errors(new ErrorContainer(symbolTable.get()));
  std::unique_ptr<CommandLineParser> clp(
      new CommandLineParser(errors.get(), symbolTable.get()));
  clp->parseCommandLine(cargs.size(), cargs.data());

  fs::remove_all(wsdir, ec);
  EXPECT_FALSE(ec) << ec;

  const PathIdVector& workingDirIds = clp->getWorkingDirs();
  std::set<fs::path> actualWorkingDirs;
  std::transform(workingDirIds.begin(), workingDirIds.end(),
                 std::inserter(actualWorkingDirs, actualWorkingDirs.end()),
                 [&](const PathId& id) { return fileSystem->toPath(id); });
  EXPECT_EQ(expectedWorkingDirs, actualWorkingDirs);

  const PathIdVector& sourceFileIds = clp->getSourceFiles();
  std::set<fs::path> actualSourceFiles;
  std::transform(sourceFileIds.begin(), sourceFileIds.end(),
                 std::inserter(actualSourceFiles, actualSourceFiles.end()),
                 [&](const PathId& id) { return fileSystem->toPath(id); });
  EXPECT_EQ(expectedSourceFiles, actualSourceFiles);
}

TEST(CommandLineParserTest, WorkingDirectories4) {
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
      FileSystem::normalize(fs::path(testing::TempDir()) / "ws4");
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

  for (const fs::path& dir : dirs) {
    fs::create_directories(dir, ec);
    EXPECT_FALSE(ec) << ec;
  }

  std::set<fs::path> expectedSourceFiles;
  for (const fs::path& file : files) {
    std::ofstream strm(file);
    EXPECT_TRUE(strm.is_open());
    strm.close();
    expectedSourceFiles.insert(file);
  }

  const std::vector<std::string> args{
      programPath.string(),
      "-nostdout",
      "-wd",
      "../..",
      "subfolder_1/subfolder_3/test_a.sv",
      "subfolder_4/test_b.sv",
      "test_c.sv",
      "-wd",
      "../../../../third_party",
      "uvm/uvm_subfolder_a/uvm_subfolder_b/uvm_a.sv",
      "uvm/uvm_subfolder_a/uvm_b.sv"};

  const std::set<fs::path> expectedWorkingDirs{
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_2",
      wsdir / "tests" / "testname" / "subfolder_1" / "subfolder_3",
      wsdir / "tests" / "testname" / "subfolder_4",
      wsdir / "tests" / "testname",
      wsdir / "third_party",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a",
      wsdir / "third_party" / "uvm" / "uvm_subfolder_a" / "uvm_subfolder_b"};

  std::vector<const char*> cargs;
  cargs.reserve(args.size());
  std::transform(args.begin(), args.end(), std::back_inserter(cargs),
                 [](const std::string& arg) { return arg.c_str(); });

  std::unique_ptr<TestFileSystem> fileSystem(new TestFileSystem(testdir));
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);
  std::unique_ptr<ErrorContainer> errors(new ErrorContainer(symbolTable.get()));
  std::unique_ptr<CommandLineParser> clp(
      new CommandLineParser(errors.get(), symbolTable.get()));
  clp->parseCommandLine(cargs.size(), cargs.data());

  fs::remove_all(wsdir, ec);
  EXPECT_FALSE(ec) << ec;

  const PathIdVector& workingDirIds = clp->getWorkingDirs();
  std::set<fs::path> actualWorkingDirs;
  std::transform(workingDirIds.begin(), workingDirIds.end(),
                 std::inserter(actualWorkingDirs, actualWorkingDirs.end()),
                 [&](const PathId& id) { return fileSystem->toPath(id); });
  EXPECT_EQ(expectedWorkingDirs, actualWorkingDirs);

  const PathIdVector& sourceFileIds = clp->getSourceFiles();
  std::set<fs::path> actualSourceFiles;
  std::transform(sourceFileIds.begin(), sourceFileIds.end(),
                 std::inserter(actualSourceFiles, actualSourceFiles.end()),
                 [&](const PathId& id) { return fileSystem->toPath(id); });
  EXPECT_EQ(expectedSourceFiles, actualSourceFiles);
}
}  // namespace
}  // namespace SURELOG
