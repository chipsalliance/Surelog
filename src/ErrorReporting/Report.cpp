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
#include "Surelog/ErrorReporting/Report.h"

#include <chrono>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <mutex>
#include <regex>
#include <thread>

#if !(defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
#include <unistd.h>
#endif

#include "Surelog/ErrorReporting/ErrorContainer.h"

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

bool parseReportFile(const fs::path& logFile, Result& result) {
  bool ret = false;
  std::ifstream ifs(logFile);
  if (!ifs.bad()) {
    std::string line;
    while (std::getline(ifs, line)) {
      if (ifs.bad()) break;
      if (line.find("[  FATAL] : ") != std::string::npos) {
        result.m_nbFatal = line.substr(12, line.size() - 11);
      }
      if (line.find("[ SYNTAX] : ") != std::string::npos) {
        result.m_nbSyntax = line.substr(12, line.size() - 11);
      }
      if (line.find("[  ERROR] : ") != std::string::npos) {
        result.m_nbError = line.substr(12, line.size() - 11);
      }
      if (line.find("[WARNING] : ") != std::string::npos) {
        result.m_nbWarning = line.substr(12, line.size() - 11);
      }
      if (line.find("[   NOTE] : ") != std::string::npos) {
        result.m_nbNote = line.substr(12, line.size() - 11);
        ret = true;
      }
      if (line.find("[   INFO] : ") != std::string::npos) {
        result.m_nbInfo = line.substr(12, line.size() - 11);
        ret = true;
      }
    }
  }

  ifs.close();
  return ret;
}

std::pair<bool, bool> Report::makeDiffCompUnitReport(CommandLineParser* clp,
                                                     SymbolTable* st) {
  // std::mutex m;
  // m.lock();
  fs::path odir = st->getSymbol(clp->getOutputDir());
  fs::path alldir = st->getSymbol(clp->getCompileAllDir());
  fs::path unitdir = st->getSymbol(clp->getCompileUnitDir());
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
      readAll = parseReportFile(alllog, readAllResult);
    }
    if (!readUnit) {
      readUnit = parseReportFile(unitlog, readUnitResult);
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

  std::string diffCmd = "diff -r " + odir.string() + unitdir.string() + " " +
                        odir.string() + alldir.string() +
                        " --exclude cache --brief > " + diffFile.string();
  int retval = system(diffCmd.c_str());

  std::ifstream ifs(diffFile.c_str());
  if (!ifs.bad()) {
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

  int nbFatal = atoi(readUnitResult.m_nbFatal.c_str()) +
                atoi(readAllResult.m_nbFatal.c_str());
  int nbSyntax = atoi(readUnitResult.m_nbSyntax.c_str()) +
                 atoi(readAllResult.m_nbSyntax.c_str());

  // m.unlock();
  return std::make_pair(retval != -1, (!nbFatal) && (!nbSyntax));
}
}  // namespace SURELOG
