/*
 Copyright 2019 Alain Dargelas

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
 * File:   main.cpp
 * Author: alain
 *
 * Created on January 15, 2017, 12:15 AM
 */

#if defined(_MSC_VER)
#include <direct.h>
#include <process.h>

#include <string_view>
#include <utility>
#else
#include <sys/param.h>
#include <unistd.h>
#endif

#include <string.h>
#include <sys/stat.h>

#include <fstream>
#include <iostream>
#include <string>
#include <vector>

#if defined(_MSC_VER) && defined(_DEBUG)
#include <Windows.h>
#endif

#include "Surelog/API/PythonAPI.h"
#include "Surelog/API/Surelog.h"
#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/PlatformFileSystem.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/Report.h"
#include "Surelog/ErrorReporting/Waiver.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Utils/StringUtils.h"

namespace fs = std::filesystem;

constexpr std::string_view cd_opt = "-cd";
constexpr std::string_view diff_unit_opt = "-diffcompunit";
constexpr std::string_view nopython_opt = "-nopython";
constexpr std::string_view parseonly_opt = "-parseonly";
constexpr std::string_view batch_opt = "-batch";
constexpr std::string_view nostdout_opt = "-nostdout";
constexpr std::string_view output_folder_opt = "-o";

uint32_t executeCompilation(
    int32_t argc, const char** argv, bool diffCompMode, bool fileUnit,
    SURELOG::ErrorContainer::Stats* overallStats = nullptr) {
  SURELOG::FileSystem* const fileSystem = SURELOG::FileSystem::getInstance();
  bool success = true;
  bool noFatalErrors = true;
  uint32_t codedReturn = 0;
  SURELOG::SymbolTable* symbolTable = new SURELOG::SymbolTable();
  SURELOG::ErrorContainer* errors = new SURELOG::ErrorContainer(symbolTable);
  SURELOG::CommandLineParser* clp = new SURELOG::CommandLineParser(
      errors, symbolTable, diffCompMode, fileUnit);
  success = clp->parseCommandLine(argc, argv);
  bool parseOnly = clp->parseOnly();
  errors->printMessages(clp->muteStdout());
  if (success && (!clp->help())) {
    // Load Python scripts in the interpreter
    if (clp->pythonListener() || clp->pythonEvalScriptPerFile() ||
        clp->pythonEvalScript()) {
      SURELOG::PythonAPI::loadScripts();

      if (!SURELOG::PythonAPI::isListenerLoaded()) {
        SURELOG::Location loc(SURELOG::BadSymbolId);
        SURELOG::Error err(
            SURELOG::ErrorDefinition::PY_NO_PYTHON_LISTENER_FOUND, loc);
        errors->addError(err);
      }
    }

    SURELOG::scompiler* compiler = SURELOG::start_compiler(clp);
    if (!compiler) codedReturn |= 1;
    SURELOG::shutdown_compiler(compiler);
  }
  SURELOG::ErrorContainer::Stats stats;
  if (!clp->help()) {
    stats = errors->getErrorStats();
    if (overallStats) (*overallStats) += stats;
    if (stats.nbFatal) codedReturn |= 1;
    if (stats.nbSyntax) codedReturn |= 2;
    if (stats.nbError) codedReturn |= 4;
  }
  bool noFErrors = true;
  if (!clp->help()) noFErrors = errors->printStats(stats, clp->muteStdout());
  if (noFErrors == false) {
    noFatalErrors = false;
  }

  std::string ext_command = clp->getExeCommand();
  if (!ext_command.empty()) {
    SURELOG::PathId fileId = fileSystem->getChild(
        clp->getCompileDirId(), "file.lst", clp->getSymbolTable());
    fs::path fileList = fileSystem->toPath(fileId);
    std::string command = ext_command + " " + fileList.string();
    int32_t result = system(command.c_str());
    codedReturn |= result;
    std::cout << "Command result: " << result << std::endl;
  }
  clp->logFooter();
  if (diffCompMode && fileUnit) {
    SURELOG::Report* report = new SURELOG::Report();
    std::pair<bool, bool> results =
        report->makeDiffCompUnitReport(clp, symbolTable);
    success = results.first;
    noFatalErrors = results.second;
    delete report;
  }
  clp->cleanCache();  // only if -nocache
  delete clp;
  delete symbolTable;
  delete errors;
  if ((!noFatalErrors) || (!success)) codedReturn |= 1;
  if (parseOnly)
    return 0;
  else
    return codedReturn;
}

enum COMP_MODE {
  NORMAL,
  DIFF,
  BATCH,
};

int32_t batchCompilation(const char* argv0, const fs::path& batchFile,
                         const fs::path& outputDir, bool nostdout) {
  int32_t returnCode = 0;

  std::error_code ec;
  const fs::path cwd = fs::current_path(ec);
  if (ec) returnCode |= 1;

  std::ifstream stream;
  stream.open(batchFile);
  if (!stream.good()) {
    returnCode |= 1;
    return returnCode;
  }

  std::string line;
  int32_t count = 0;
  SURELOG::ErrorContainer::Stats overallStats;
  while (std::getline(stream, line)) {
    if (line.empty()) continue;
    if (!nostdout)
      std::cout << "Processing: " << line << std::endl << std::flush;

    std::vector<std::string> args;
    SURELOG::StringUtils::tokenize(line, " \r\t", args);

    if (!outputDir.empty()) {
      fs::path cd;
      int32_t odirIndex = -1;
      for (size_t i = 0, n = args.size() - 1; i < n; i++) {
        if (args[i] == cd_opt) {
          cd = SURELOG::StringUtils::unquoted(args[++i]);
        } else if (args[i] == output_folder_opt) {
          odirIndex = ++i;
        }
      }

      if (odirIndex >= 0) {
        fs::path odir = args[odirIndex];
        if (odir.is_relative()) {
          odir = outputDir / odir;
        }
        args[odirIndex] = odir.string();
      } else {
        args.push_back("-o");
        args.push_back(outputDir.string());
      }
    }

    std::vector<const char*> argv;
    argv.reserve(args.size());
    argv.push_back(argv0);
    for (const std::string& arg : args) {
      if (!arg.empty()) {
        argv.push_back(arg.c_str());
      }
    }
    if (argv.size() < 2) continue;

    returnCode |= executeCompilation(argv.size(), argv.data(), false, false,
                                     &overallStats);
    count++;
    fs::current_path(cwd, ec);
    if (ec) {
      std::cerr << "FATAL: Could not change directory to " << cwd << std::endl;
      std::cerr << "       " << ec.message() << std::endl;
      returnCode |= 1;
    }
  }
  if (!nostdout)
    std::cout << "Processed " << count << " tests." << std::endl << std::flush;

  SURELOG::SymbolTable* symbolTable = new SURELOG::SymbolTable();
  SURELOG::ErrorContainer* errors = new SURELOG::ErrorContainer(symbolTable);
  if (!nostdout) errors->printStats(overallStats);
  delete errors;
  delete symbolTable;
  stream.close();
  return returnCode;
}

int main(int argc, const char** argv) {
#if defined(_MSC_VER) && defined(_DEBUG)
  // Redirect cout to file
  std::streambuf* cout_rdbuf = nullptr;
  std::streambuf* cerr_rdbuf = nullptr;
  std::ofstream file;
  if (IsDebuggerPresent() != 0) {
    file.open("cout.txt");
    cout_rdbuf = std::cout.rdbuf(file.rdbuf());
    cerr_rdbuf = std::cerr.rdbuf(file.rdbuf());
  }
#endif
  SURELOG::FileSystem::setInstance(
      new SURELOG::PlatformFileSystem(fs::current_path()));

  SURELOG::Waiver::initWaivers();

  SURELOG::FileSystem* const fileSystem = SURELOG::FileSystem::getInstance();
  const fs::path workingDir = fileSystem->getWorkingDir();

  uint32_t codedReturn = 0;
  COMP_MODE mode = NORMAL;
  bool python_mode = true;
  bool nostdout = false;
  fs::path batchFile;
  fs::path outputDir;
  for (int32_t i = 1; i < argc; i++) {
    if (parseonly_opt == argv[i]) {
    } else if (diff_unit_opt == argv[i]) {
      mode = DIFF;
    } else if (nopython_opt == argv[i]) {
      python_mode = false;
    } else if (batch_opt == argv[i]) {
      batchFile = SURELOG::StringUtils::unquoted(argv[++i]);
      mode = BATCH;
    } else if (nostdout_opt == argv[i]) {
      nostdout = true;
    } else if (output_folder_opt == argv[i]) {
      outputDir = SURELOG::StringUtils::unquoted(argv[++i]);
    }
  }

  if (!outputDir.empty() && outputDir.is_relative()) {
    outputDir = workingDir / outputDir;
  }

  if (python_mode) SURELOG::PythonAPI::init(argc, argv);

  switch (mode) {
    case DIFF: {
#if (defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
      // REVISIT: Windows doesn't have the concept of forks!
      // Implement it sequentially for now and optimize it if this
      // proves to be a bottleneck (preferably, implemented as a
      // cross platform solution).
      executeCompilation(argc, argv, true, false);
      codedReturn = executeCompilation(argc, argv, true, true);
#else
      pid_t pid = fork();
      if (pid == 0) {
        // child process
        executeCompilation(argc, argv, true, false);
      } else if (pid > 0) {
        // parent process
        codedReturn = executeCompilation(argc, argv, true, true);
      } else {
        // fork failed
        printf("fork() failed!\n");
        return 1;
      }
#endif
      break;
    }
    case NORMAL:
      codedReturn = executeCompilation(argc, argv, false, false);
      break;
    case BATCH:
      codedReturn = batchCompilation(argv[0], batchFile, outputDir, nostdout);
      break;
  }

  if (python_mode) SURELOG::PythonAPI::shutdown();
#if defined(_MSC_VER) && defined(_DEBUG)
  // Redirect cout back to screen
  if (cout_rdbuf != nullptr) {
    std::cout.rdbuf(cout_rdbuf);
  }
  if (cerr_rdbuf != nullptr) {
    std::cerr.rdbuf(cerr_rdbuf);
  }
  if (file.is_open()) {
    file.flush();
    file.close();
  }
#endif
  return codedReturn;
}
