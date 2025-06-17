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
 * File:   ErrorContainer.h
 * Author: alain
 *
 * Created on March 5, 2017, 11:12 PM
 */

#ifndef SURELOG_ERRORCONTAINER_H
#define SURELOG_ERRORCONTAINER_H
#pragma once

#include <Surelog/ErrorReporting/Error.h>

#include <cstdint>
#include <set>
#include <string>
#include <string_view>
#include <tuple>
#include <utility>
#include <vector>

namespace SURELOG {
class LogListener;
class Session;

class ErrorContainer final {
 public:
  class Stats {
   public:
    Stats& operator+=(const Stats& r) {
      nbFatal += r.nbFatal;
      nbSyntax += r.nbSyntax;
      nbError += r.nbError;
      nbWarning += r.nbWarning;
      nbNote += r.nbNote;
      nbInfo += r.nbInfo;
      return *this;
    }

    int32_t nbFatal = 0;
    int32_t nbSyntax = 0;
    int32_t nbError = 0;
    int32_t nbWarning = 0;
    int32_t nbNote = 0;
    int32_t nbInfo = 0;
  };

  explicit ErrorContainer(Session* session);
  ErrorContainer(const ErrorContainer& orig) = delete;
  virtual ~ErrorContainer() = default;

  Session* getSession() { return m_session; }

  void init();
  Error& addError(Error& error, bool showDuplicates = false,
                  bool reentrantPython = true);
  void addError(ErrorDefinition::ErrorType errorId, const Location& loc,
                bool showDuplicates = false, bool reentrantPython = true);
  void addError(ErrorDefinition::ErrorType errorId, const Location& loc,
                const Location& extra, bool showDuplicates = false,
                bool reentrantPython = true);
  void addError(ErrorDefinition::ErrorType errorId,
                const std::vector<Location>& locations,
                bool showDuplicates = false, bool reentrantPython = true);

  const std::vector<Error>& getErrors() const { return m_errors; }
  bool printMessages(bool muteStdout = false);
  bool printMessage(Error& error, bool muteStdout = false);
  bool printStats(Stats stats, bool muteStdout = false);
  bool printToLogFile(std::string_view report);
  bool hasFatalErrors() const;
  Stats getErrorStats() const;
  void appendErrors(ErrorContainer&);
  void setPythonInterp(void* interpState) { m_interpState = interpState; }

 private:
  std::tuple<std::string, bool, bool> createErrorMessage(
      ErrorDefinition::ErrorType errorId,
      const std::vector<Location>& locations,
      bool reentrantPython = true) const;
  Error& addError(Error& error, const std::string& message,
                  bool reportFatalError, bool showDuplicates);

  std::pair<std::string, bool> createReport_() const;
  std::pair<std::string, bool> createReport_(const Error& error) const;
  std::vector<Error> m_errors;
  std::set<std::string> m_errorSet;

  Session* const m_session = nullptr;
  bool m_reportedFatalErrorLogFile = false;
  void* m_interpState = nullptr;
};

};  // namespace SURELOG

#endif /* SURELOG_ERRORCONTAINER_H */
