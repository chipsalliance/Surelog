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
 * File:   ErrorContainer.cpp
 * Author: alain
 *
 * Created on March 5, 2017, 11:12 PM
 */

#include "Surelog/ErrorReporting/ErrorContainer.h"

#include <cstdint>
#include <cstdio>
#include <iostream>
#include <map>
#include <string>
#include <string_view>
#include <tuple>
#include <utility>
#include <vector>

#include "Surelog/API/PythonAPI.h"
#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/ErrorReporting/LogListener.h"
#include "Surelog/ErrorReporting/Waiver.h"
#include "Surelog/SourceCompile/SymbolTable.h"

namespace SURELOG {
ErrorContainer::ErrorContainer(SymbolTable* symbolTable,
                               LogListener* logListener /* = nullptr */)
    : m_clp(nullptr),
      m_reportedFatalErrorLogFile(false),
      m_symbolTable(symbolTable),
      m_interpState(nullptr),
      m_logListener(logListener ? logListener : new LogListener()),
      m_listenerOwned(logListener == nullptr) {
  m_interpState = PythonAPI::getMainInterp();
  /* Do nothing here */
}

ErrorContainer::~ErrorContainer() {
  if (m_listenerOwned) delete m_logListener;
}

void ErrorContainer::init() {
  if (ErrorDefinition::init()) {
    FileSystem* const fileSystem = FileSystem::getInstance();
    if (LogListener::failed(m_logListener->initialize(m_clp->getLogFileId()))) {
      std::cerr << "[FTL:LG0001] Cannot create log file \""
                << fileSystem->toPath(m_clp->getLogFileId()) << "\""
                << std::endl;
    }
  }
}

Error& ErrorContainer::addError(Error& error, bool showDuplicates,
                                bool reentrantPython) {
  std::tuple<std::string, bool, bool> textStatus =
      createErrorMessage(error, reentrantPython);
  if (std::get<2>(textStatus))  // filter Message
    return error;

  FileSystem* const fileSystem = FileSystem::getInstance();
  std::multimap<ErrorDefinition::ErrorType, Waiver::WaiverData>& waivers =
      Waiver::getWaivers();
  std::pair<
      std::multimap<ErrorDefinition::ErrorType, Waiver::WaiverData>::iterator,
      std::multimap<ErrorDefinition::ErrorType, Waiver::WaiverData>::iterator>
      ret = waivers.equal_range(error.m_errorId);
  for (std::multimap<ErrorDefinition::ErrorType, Waiver::WaiverData>::iterator
           it = ret.first;
       it != ret.second; ++it) {
    if ((((*it).second.m_fileName.empty()) ||
         (fileSystem->toPath(error.m_locations[0].m_fileId) ==
          (*it).second.m_fileName)) &&
        (((*it).second.m_line == 0) ||
         (error.m_locations[0].m_line == (*it).second.m_line)) &&
        (((*it).second.m_objectId.empty()) ||
         (m_symbolTable->getSymbol(error.m_locations[0].m_object) ==
          (*it).second.m_objectId))) {
      error.m_waived = true;
      break;
    }
  }

  // Copy the PathId into our local SymbolTable!
  for (Location& loc : error.m_locations) {
    if (loc.m_fileId) {
      loc.m_fileId = fileSystem->copy(loc.m_fileId, m_symbolTable);
    }
  }

  if (showDuplicates) {
    m_errors.emplace_back(error);
  } else {
    if (m_errorSet.find(std::get<0>(textStatus)) == m_errorSet.end()) {
      m_errors.emplace_back(error);
      m_errorSet.insert(std::get<0>(textStatus));
    }
  }
  return m_errors.back();
}

void ErrorContainer::appendErrors(ErrorContainer& rhs) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  for (uint32_t i = 0; i < rhs.m_errors.size(); i++) {
    Error err = rhs.m_errors[i];
    if (!err.m_reported) {
      // Translate IDs to master symbol table
      for (auto& loc : err.m_locations) {
        if (loc.m_fileId)
          loc.m_fileId = fileSystem->copy(loc.m_fileId, m_symbolTable);
        if (loc.m_object) {
          loc.m_object =
              m_symbolTable->copyFrom(loc.m_object, rhs.m_symbolTable);
        }
      }
      addError(err);
    }
  }
}

std::tuple<std::string, bool, bool> ErrorContainer::createErrorMessage(
    const Error& msg, bool reentrantPython) const {
  FileSystem* const fileSystem = FileSystem::getInstance();
  const std::map<ErrorDefinition::ErrorType, ErrorDefinition::ErrorInfo>&
      infoMap = ErrorDefinition::getErrorInfoMap();
  std::string tmp;
  bool reportFatalError = false;
  bool filterMessage = false;
  if ((!msg.m_reported) && (!msg.m_waived)) {
    ErrorDefinition::ErrorType type = msg.m_errorId;
    std::map<ErrorDefinition::ErrorType,
             ErrorDefinition::ErrorInfo>::const_iterator itr =
        infoMap.find(type);
    if (itr != infoMap.end()) {
      ErrorDefinition::ErrorInfo info = (*itr).second;
      std::string severity;
      switch (info.m_severity) {
        case ErrorDefinition::FATAL:
          severity = "FTL";
          reportFatalError = true;
          break;
        case ErrorDefinition::SYNTAX:
          severity = "SNT";
          break;
        case ErrorDefinition::ERROR:
          severity = "ERR";
          break;
        case ErrorDefinition::WARNING:
          severity = "WRN";
          if (m_clp->filterWarning()) filterMessage = true;
          break;
        case ErrorDefinition::INFO:
          severity = "INF";
          if (m_clp->filterInfo() &&
              (type != ErrorDefinition::PP_PROCESSING_SOURCE_FILE))
            filterMessage = true;
          break;
        case ErrorDefinition::NOTE:
          severity = "NTE";
          if (m_clp->filterNote()) filterMessage = true;
          break;
      }
      std::string category = ErrorDefinition::getCategoryName(info.m_category);

      const Location& loc = msg.m_locations[0];
      /* Object */
      std::string text = info.m_errorText;
      const std::string_view objectName =
          m_symbolTable->getSymbol(loc.m_object);
      if (objectName != SymbolTable::getBadSymbol()) {
        size_t objectOffset = text.find("%s");
        if (objectOffset != std::string::npos) {
          text = text.replace(objectOffset, 2, objectName);
        }
      }

      /* Location */
      std::string location;
      if (loc.m_fileId) {
        location = fileSystem->toPath(loc.m_fileId);
        if (loc.m_line > 0) {
          location += ":" + std::to_string(loc.m_line) + ":";
          if (loc.m_column > 0) location += std::to_string(loc.m_column) + ":";
        }
        location += " ";
      }

      /* Extra locations */
      bool extraTextAppended = false;
      uint32_t nbExtraLoc = msg.m_locations.size();
      for (uint32_t i = 1; i < nbExtraLoc; i++) {
        const Location& extraLoc = msg.m_locations[i];
        if (extraLoc.m_fileId) {
          std::string extraLocation(fileSystem->toPath(extraLoc.m_fileId));
          if (extraLoc.m_line > 0) {
            extraLocation += ":" + std::to_string(extraLoc.m_line) + ":";
            if (extraLoc.m_column > 0)
              extraLocation += std::to_string(extraLoc.m_column) + ":";
          }
          size_t objectOffset = text.find("%exloc");
          if ((objectOffset == std::string::npos) &&
              !info.m_extraText.empty()) {
            if (!extraTextAppended) {
              text += ",\n             " + info.m_extraText;
              extraTextAppended = true;
            }
            objectOffset = text.find("%exloc");
          }
          if (objectOffset != std::string::npos) {
            text = text.replace(objectOffset, 6, extraLocation);
          }
        } else {
          if (!info.m_extraText.empty()) {
            if ((i == 1) && !extraLoc.m_fileId) {
              if (!extraTextAppended) {
                text += ",\n" + info.m_extraText;
                extraTextAppended = true;
              }
            } else {
              if (!extraTextAppended) {
                text += ",\n             " + info.m_extraText;
                extraTextAppended = true;
              }
            }
          }
        }
        if (extraLoc.m_object) {
          const std::string_view objString =
              m_symbolTable->getSymbol(extraLoc.m_object);
          size_t objectOffset = text.find("%exobj");
          if (objectOffset != std::string::npos) {
            text = text.replace(objectOffset, 6, objString);
          }
        }
      }
      text += ".";
      std::string padding;
      if (msg.m_errorId < 10)
        padding = "000";
      else if (msg.m_errorId < 100)
        padding = "00";
      else if (msg.m_errorId < 1000)
        padding = "0";
      if ((reentrantPython == false) || (!m_clp->pythonAllowed())) {
        tmp = "[" + severity + ":" + category + padding +
              std::to_string(msg.m_errorId) + "] " + location + text + "\n";
      } else {
        std::vector<std::string> args;
        args.push_back(severity);
        args.push_back(category);
        args.push_back(padding + std::to_string(msg.m_errorId));
        args.push_back(location);
        args.push_back(text);
        tmp = PythonAPI::evalScript("__main__", "SLformatMsg", args,
                                    (PyThreadState*)m_interpState);
      }
    }
  }
  return std::make_tuple(tmp, reportFatalError, filterMessage);
}

bool ErrorContainer::hasFatalErrors() const {
  const std::map<ErrorDefinition::ErrorType, ErrorDefinition::ErrorInfo>&
      infoMap = ErrorDefinition::getErrorInfoMap();
  bool reportFatalError = false;
  for (const Error& msg : m_errors) {
    ErrorDefinition::ErrorType type = msg.m_errorId;
    std::map<ErrorDefinition::ErrorType,
             ErrorDefinition::ErrorInfo>::const_iterator itr =
        infoMap.find(type);
    if (itr != infoMap.end()) {
      ErrorDefinition::ErrorInfo info = (*itr).second;
      std::string severity;
      switch (info.m_severity) {
        case ErrorDefinition::FATAL:
          reportFatalError = true;
          break;
        default:
          break;
      }
    }
  }
  return reportFatalError;
}

std::pair<std::string, bool> ErrorContainer::createReport_() const {
  std::string report;
  bool reportFatalError = false;
  for (const Error& msg : m_errors) {
    std::tuple<std::string, bool, bool> textStatus = createErrorMessage(msg);
    if (std::get<1>(textStatus)) reportFatalError = true;
    if (std::get<2>(textStatus))  // Filtered
      continue;
    report += std::get<0>(textStatus);
  }
  return std::make_pair(report, reportFatalError);
}

std::pair<std::string, bool> ErrorContainer::createReport_(
    const Error& error) const {
  std::string report;
  bool reportFatalError = false;
  const Error& msg = error;
  std::tuple<std::string, bool, bool> textStatus = createErrorMessage(msg);
  if (std::get<1>(textStatus)) reportFatalError = true;
  if (!std::get<2>(textStatus))  // Filtered
    report += std::get<0>(textStatus);
  return std::make_pair(report, reportFatalError);
}

bool ErrorContainer::printStats(ErrorContainer::Stats stats, bool muteStdout) {
  std::string report;
  report += "[  FATAL] : " + std::to_string(stats.nbFatal) + "\n";
  report += "[ SYNTAX] : " + std::to_string(stats.nbSyntax) + "\n";
  report += "[  ERROR] : " + std::to_string(stats.nbError) + "\n";
  report += "[WARNING] : " + std::to_string(stats.nbWarning) + "\n";
  // BOGUS NUMBER IN CACHED MODE  report += "[   INFO] : " +
  // std::to_string(stats.nbInfo) + "\n";
  report += "[   NOTE] : " + std::to_string(stats.nbNote) + "\n";
  if (!muteStdout) {
    std::cout << report << std::flush;
  }
  bool successLogFile = printToLogFile(report);
  return (successLogFile && (!stats.nbFatal) && (!stats.nbSyntax));
}

ErrorContainer::Stats ErrorContainer::getErrorStats() const {
  const std::map<ErrorDefinition::ErrorType, ErrorDefinition::ErrorInfo>&
      infoMap = ErrorDefinition::getErrorInfoMap();
  ErrorContainer::Stats stats;
  for (const auto& msg : m_errors) {
    if (!msg.m_waived) {
      ErrorDefinition::ErrorType type = msg.m_errorId;
      std::map<ErrorDefinition::ErrorType,
               ErrorDefinition::ErrorInfo>::const_iterator itr =
          infoMap.find(type);
      if (itr != infoMap.end()) {
        ErrorDefinition::ErrorInfo info = (*itr).second;
        switch (info.m_severity) {
          case ErrorDefinition::FATAL:
            stats.nbFatal++;
            break;
          case ErrorDefinition::SYNTAX:
            stats.nbSyntax++;
            break;
          case ErrorDefinition::ERROR:
            stats.nbError++;
            break;
          case ErrorDefinition::WARNING:
            stats.nbWarning++;
            break;
          case ErrorDefinition::INFO:
            stats.nbInfo++;
            break;
          case ErrorDefinition::NOTE:
            stats.nbNote++;
            break;
        }
      }
    }
  }
  return stats;
}

bool ErrorContainer::printToLogFile(std::string_view report) {
  LogListener::LogResult result;
  if (LogListener::failed(result = m_logListener->log(report))) {
    if (!m_reportedFatalErrorLogFile &&
        (result == LogListener::LogResult::FailedToOpenFileForWrite)) {
      FileSystem* const fileSystem = FileSystem::getInstance();
      std::cerr << "[FTL:LG0002] Cannot open log file \""
                << fileSystem->toPath(m_logListener->getLogFileId())
                << "\" in append mode" << std::endl;
      m_reportedFatalErrorLogFile = true;
    }
    return false;
  }
  return true;
}

bool ErrorContainer::printMessage(Error& error, bool muteStdout) {
  if (error.m_reported) return false;
  std::pair<std::string, bool> report = createReport_(error);

  if (!muteStdout) {
    std::cout << report.first << std::flush;
  }
  bool successLogFile = printToLogFile(report.first);
  if (successLogFile) error.m_reported = true;
  return (successLogFile && (!report.second));
}

bool ErrorContainer::printMessages(bool muteStdout) {
  std::pair<std::string, bool> report = createReport_();
  if (!muteStdout) {
    std::cout << report.first << std::flush;
  }
  bool successLogFile = printToLogFile(report.first);
  if (successLogFile) {
    for (auto& err : m_errors) {
      err.m_reported = true;
    }
  }
  return (successLogFile && (!report.second));
}
}  // namespace SURELOG
