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
 * File:   Report.cpp
 * Author: alain
 *
 * Created on April 10, 2017, 8:56 PM
 */

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/FileSystem.h>
#include <Surelog/ErrorReporting/Report.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/StringUtils.h>

#include <chrono>
#include <filesystem>
#include <iostream>
#include <regex>
#include <thread>

#if !(defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
#include <unistd.h>
#endif

#include <Surelog/ErrorReporting/ErrorContainer.h>

namespace SURELOG {

namespace fs = std::filesystem;

struct Result {
  std::string m_nbFatal;
  std::string m_nbSyntax;
  std::string m_nbError;
  std::string m_nbWarning;
  std::string m_nbNote;
  std::string m_nbInfo;
};

bool parseReportFile(PathId logFileId, Result& result) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  bool ret = false;
  std::istream& ifs = fileSystem->openForRead(logFileId);
  if (ifs.good()) {
    std::string line;
    while (std::getline(ifs, line)) {
      if (ifs.bad()) break;
      line = StringUtils::rtrim(line);
      if (line.find("[  FATAL] : ") == 0) {
        result.m_nbFatal = line.substr(12);
      }
      if (line.find("[ SYNTAX] : ") == 0) {
        result.m_nbSyntax = line.substr(12);
      }
      if (line.find("[  ERROR] : ") == 0) {
        result.m_nbError = line.substr(12);
      }
      if (line.find("[WARNING] : ") == 0) {
        result.m_nbWarning = line.substr(12);
      }
      if (line.find("[   NOTE] : ") == 0) {
        result.m_nbNote = line.substr(12);
        ret = true;
      }
      if (line.find("[   INFO] : ") == 0) {
        result.m_nbInfo = line.substr(12);
        ret = true;
      }
    }
  }
  fileSystem->close(ifs);
  return ret;
}

std::pair<bool, bool> Report::makeDiffCompUnitReport(CommandLineParser* clp,
                                                     SymbolTable* st) {
  // std::mutex m;
  // m.lock();
  FileSystem* const fileSystem = FileSystem::getInstance();
  fs::path odir = fileSystem->toPath(clp->getOutputDirId());
  fs::path alldir = fileSystem->toPath(clp->getCompileAllDirId());
  fs::path unitdir = fileSystem->toPath(clp->getCompileUnitDirId());
  fs::path log = st->getSymbol(clp->getDefaultLogFileId());
  fs::path alllog = odir / alldir / log;
  fs::path unitlog = odir / unitdir / log;
  bool readAll = false;
  bool readUnit = false;
  Result readAllResult;
  Result readUnitResult;

  while ((!readAll) || (!readUnit)) {
    std::this_thread::sleep_for(std::chrono::microseconds(1000));
    if (!readAll) {
      readAll =
          parseReportFile(fileSystem->toPathId(alllog, st), readAllResult);
    }
    if (!readUnit) {
      readUnit =
          parseReportFile(fileSystem->toPathId(unitlog, st), readUnitResult);
    }
  }

  std::cout << "|-------|------------------|-------------------|" << std::endl;
  std::cout << "|       |  FILE UNIT COMP  |  ALL COMPILATION  |" << std::endl;
  std::cout << "|-------|------------------|-------------------|" << std::endl;
  std::cout << "| FATAL | " << std::setw(9) << readUnitResult.m_nbFatal
            << "        | " << std::setw(9) << readAllResult.m_nbFatal
            << "         |" << std::endl;
  std::cout << "|SYNTAX | " << std::setw(9) << readUnitResult.m_nbSyntax
            << "        | " << std::setw(9) << readAllResult.m_nbSyntax
            << "         |" << std::endl;
  std::cout << "| ERROR | " << std::setw(9) << readUnitResult.m_nbError
            << "        | " << std::setw(9) << readAllResult.m_nbError
            << "         |" << std::endl;
  std::cout << "|WARNING| " << std::setw(9) << readUnitResult.m_nbWarning
            << "        | " << std::setw(9) << readAllResult.m_nbWarning
            << "         |" << std::endl;
  std::cout << "| INFO  | " << std::setw(9) << readUnitResult.m_nbInfo
            << "        | " << std::setw(9) << readAllResult.m_nbInfo
            << "         |" << std::endl;
  std::cout << "| NOTE  | " << std::setw(9) << readUnitResult.m_nbNote
            << "        | " << std::setw(9) << readAllResult.m_nbNote
            << "         |" << std::endl;
  std::cout << "|-------|------------------|-------------------|" << std::endl;
  std::cout << std::endl;
  std::cout << "FILE UNIT LOG: " << unitlog << std::endl;
  std::cout << "ALL FILES LOG: " << alllog << std::endl;

  fs::path diffFile = odir / unitdir / "diff.log";

  std::string diffCmd = "diff -r " + (odir / unitdir).string() + " " +
                        (odir / alldir).string() +
                        " --exclude cache --brief > " + diffFile.string();
  int retval = system(diffCmd.c_str());

  std::istream& ifs =
      fileSystem->openForRead(fileSystem->toPathId(diffFile, st));
  if (ifs.good()) {
    std::cout << "\nDIFFS:" << std::endl;
    std::string line;
    while (std::getline(ifs, line)) {
      if (line.find("diff.log") != std::string::npos) {
        continue;
      }
      if (line.find(log.string()) != std::string::npos) {
        continue;
      }

      line = std::regex_replace(line, std::regex("Files "), "");
      line = std::regex_replace(line, std::regex("differ"), "");
      std::cout << line << std::endl;
    }
  }
  fileSystem->close(ifs);

  int nbFatal =
      std::stoi(readUnitResult.m_nbFatal) + std::stoi(readAllResult.m_nbFatal);
  int nbSyntax = std::stoi(readUnitResult.m_nbSyntax) +
                 std::stoi(readAllResult.m_nbSyntax);

  // m.unlock();
  return std::make_pair(retval != -1, (!nbFatal) && (!nbSyntax));
}
}  // namespace SURELOG
