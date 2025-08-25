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

#include <gtest/gtest.h>

#include <algorithm>
#include <filesystem>
#include <iostream>
#include <iterator>
#include <memory>
#include <string>
#include <system_error>
#include <vector>

#if defined(__APPLE__)
#include <chrono>
#include <thread>
#endif

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/PlatformFileSystem.h"
#include "Surelog/Design/Design.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"

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

TEST(PPCacheTest, IncludeChangeTolerance) {
  // GTEST_SKIP() << "Temporarily skipped";

  // All sources are in independent folders
  //
  // Run 1
  //   * source.sv includes header2.sv
  //   * header2.sv includes header1.sv
  //   * include list: header1, header2
  //
  // Run 2
  //   * source.sv includes header3.sv
  //   * header3.sv includes header2.sv
  //   * header2.sv includes header1.sv
  //   * include list: header1, header2, header3
  //
  // Expect header1.sv & header2.sv cache to be loaded successfully
  // in the second run.

  const fs::path kTestDir = fs::path(testing::TempDir()) / "change_tolerance";
  const fs::path kBaseDir = kTestDir / "PrecompileLoadsSuccessfully";
  const fs::path kProgramFile = FileSystem::getProgramPath();

  const fs::path kInputDir = kBaseDir / "input";
  const fs::path kOutputDir = kBaseDir / "output";

  // Remove any remanants from past runs and ignore any related errors!
  std::error_code ec;
  fs::remove_all(kBaseDir, ec);

  std::unique_ptr<FileSystem> fileSystem(new TestFileSystem(kInputDir));
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);

  const PathId kInputDirId =
      fileSystem->toPathId(kInputDir.string(), symbolTable.get());
  EXPECT_TRUE(kInputDirId);
  EXPECT_TRUE(fileSystem->mkdirs(kInputDirId));

  const PathId include1DirId =
      fileSystem->getChild(kInputDirId, "include1", symbolTable.get());
  EXPECT_TRUE(include1DirId);
  EXPECT_TRUE(fileSystem->mkdirs(include1DirId));

  const PathId header1FileId =
      fileSystem->getChild(include1DirId, "header1.sv", symbolTable.get());
  EXPECT_TRUE(header1FileId);

  std::ostream &strm1 = fileSystem->openForWrite(header1FileId);
  EXPECT_TRUE(strm1.good());
  strm1 << "function automatic int get_0();" << std::endl
        << "  return 0;" << std::endl
        << "endfunction" << std::endl;
  fileSystem->close(strm1);

  const PathId include2DirId =
      fileSystem->getChild(kInputDirId, "include2", symbolTable.get());
  EXPECT_TRUE(include2DirId);
  EXPECT_TRUE(fileSystem->mkdirs(include2DirId));

  const PathId header2FileId =
      fileSystem->getChild(include2DirId, "header2.sv", symbolTable.get());
  EXPECT_TRUE(header2FileId);

  std::ostream &strm2 = fileSystem->openForWrite(header2FileId);
  EXPECT_TRUE(strm2.good());
  strm2 << "`include \"header1.sv\"" << std::endl
        << std::endl
        << "function automatic int get_1();" << std::endl
        << "  return 1;" << std::endl
        << "endfunction" << std::endl;
  fileSystem->close(strm2);

  const PathId include3DirId =
      fileSystem->getChild(kInputDirId, "include3", symbolTable.get());
  EXPECT_TRUE(include3DirId);
  EXPECT_TRUE(fileSystem->mkdirs(include3DirId));

  const PathId header3FileId =
      fileSystem->getChild(include3DirId, "header3.sv", symbolTable.get());
  EXPECT_TRUE(header3FileId);

  std::ostream &strm3 = fileSystem->openForWrite(header3FileId);
  EXPECT_TRUE(strm3.good());
  strm3 << "`include \"header2.sv\"" << std::endl
        << std::endl
        << "function automatic int get_sum();" << std::endl
        << "  return get_0() + get_1();" << std::endl
        << "endfunction" << std::endl;
  fileSystem->close(strm3);

  const PathId sourceFileId =
      fileSystem->getChild(kInputDirId, "source.sv", symbolTable.get());
  EXPECT_TRUE(sourceFileId);

  std::ostream &strm4 = fileSystem->openForWrite(sourceFileId);
  EXPECT_TRUE(strm4.good());
  strm4 << "`include \"header2.sv\"" << std::endl
        << std::endl
        << "module top(output int o);" << std::endl
        << "  assign o0 = get_0();" << std::endl
        << "  assign o1 = get_1();" << std::endl
        << "endmodule" << std::endl;
  fileSystem->close(strm4);

  // Run 1
  {
    std::unique_ptr<ErrorContainer> errors(
        new ErrorContainer(symbolTable.get()));
    std::unique_ptr<CommandLineParser> clp(
        new CommandLineParser(errors.get(), symbolTable.get(), false, false));

    const std::vector<std::string> args{
        kProgramFile.string(),
        "-nostdout",
        "-nobuiltin",
        "-parse",
        std::string("-I").append(fileSystem->toPath(include1DirId)),
        std::string("-I").append(fileSystem->toPath(include2DirId)),
        std::string(fileSystem->toPath(sourceFileId)),
        std::string(fileSystem->toPath(header1FileId)),
        std::string(fileSystem->toPath(header2FileId)),
        "-o",
        kOutputDir.string()};
    std::vector<const char *> cargs;
    std::transform(args.begin(), args.end(), std::back_inserter(cargs),
                   [](const std::string &arg) { return arg.data(); });
    clp->parseCommandLine(cargs.size(), cargs.data());

    std::unique_ptr<Compiler> compiler(
        new Compiler(clp.get(), errors.get(), symbolTable.get()));
    compiler->compile();

    const auto &compileSourceFiles = compiler->getCompileSourceFiles();
    for (CompileSourceFile *csf : compileSourceFiles) {
      EXPECT_FALSE(csf->getPreprocessor()->usingCachedVersion())
          << PathIdPP(csf->getFileId());
    }
  }

#if defined(__APPLE__)
  // On OSX (or more specifically, HFS+ filesystem) the file timestamp
  // has a granularity of one second - yes, in this age of nanoseconds!
  // The granularity is a problem for this test because we are specifically
  // testing for cache's to be invalidated because they are older than the
  // source. Horrible solution to sleep for a second to force a change in
  // file's last modified time stamp.
  // Here are a few references for the interested brain -
  //   https://arstechnica.com/gadgets/2011/07/mac-os-x-10-7/12/
  //   https://stackoverflow.com/questions/943503/python-getting-file-modification-times-with-greater-resolution-than-a-second
  //   https://github.com/haskell/unix/pull/67/files/d6dea008a97bfde6a4c9ffe15e132b05ea2339c1
  std::this_thread::sleep_for(std::chrono::seconds(1));
#endif

  // Touch the source.sv but not the headers
  std::ostream &strm5 = fileSystem->openForWrite(sourceFileId);
  EXPECT_TRUE(strm5.good());
  strm5 << "`include \"header3.sv\"" << std::endl
        << std::endl
        << "module top(output int o);" << std::endl
        << "  assign o = get_sum();" << std::endl
        << "endmodule" << std::endl;
  fileSystem->close(strm5);

  // Run 2
  {
    std::unique_ptr<ErrorContainer> errors(
        new ErrorContainer(symbolTable.get()));
    std::unique_ptr<CommandLineParser> clp(
        new CommandLineParser(errors.get(), symbolTable.get(), false, false));

    const std::vector<std::string> args{
        kProgramFile.string(),
        "-nostdout",
        "-nobuiltin",
        "-parse",
        std::string("-I").append(fileSystem->toPath(include1DirId)),
        std::string("-I").append(fileSystem->toPath(include2DirId)),
        std::string("-I").append(fileSystem->toPath(include3DirId)),
        std::string(fileSystem->toPath(sourceFileId)),
        std::string(fileSystem->toPath(header1FileId)),
        std::string(fileSystem->toPath(header2FileId)),
        std::string(fileSystem->toPath(header3FileId)),
        "-o",
        kOutputDir.string()};
    std::vector<const char *> cargs;
    std::transform(args.begin(), args.end(), std::back_inserter(cargs),
                   [](const std::string &arg) { return arg.data(); });
    clp->parseCommandLine(cargs.size(), cargs.data());

    std::unique_ptr<Compiler> compiler(
        new Compiler(clp.get(), errors.get(), symbolTable.get()));
    compiler->compile();

    const auto &compileSourceFiles = compiler->getCompileSourceFiles();
    for (CompileSourceFile *csf : compileSourceFiles) {
      const PathId fileId = csf->getFileId();
      if ((fileId == header3FileId) || (fileId == sourceFileId)) {
        EXPECT_FALSE(csf->getPreprocessor()->usingCachedVersion())
            << "fileid:" << fileId << " is " << PathIdPP(fileId);
      } else {
        EXPECT_TRUE(csf->getPreprocessor()->usingCachedVersion())
            << "fileid:" << fileId << " is " << PathIdPP(fileId);
      }
    }
  }

  fs::remove_all(kBaseDir, ec);
  EXPECT_FALSE(ec) << ec;
}
}  // namespace
}  // namespace SURELOG
