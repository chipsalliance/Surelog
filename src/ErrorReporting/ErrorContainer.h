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

#ifndef ERRORCONTAINER_H
#define ERRORCONTAINER_H
#include <set>
#include <string>
#include <vector>

#include "ErrorReporting/Error.h"
#include "ErrorReporting/ErrorDefinition.h"

namespace SURELOG {

class CommandLineParser;
class LogListener;

class ErrorContainer {
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

    int nbFatal = 0;
    int nbSyntax = 0;
    int nbError = 0;
    int nbWarning = 0;
    int nbNote = 0;
    int nbInfo = 0;
  };

  explicit ErrorContainer(SymbolTable* symbolTable,
                          LogListener* logListener = nullptr);
  virtual ~ErrorContainer();

  void registerCmdLine(CommandLineParser* clp) { m_clp = clp; }
  void init();
  Error& addError(Error& error, bool showDuplicates = false,
                  bool reentrantPython = true);

  const std::vector<Error>& getErrors() const { return m_errors; }
  bool printMessages(bool muteStdout = false);
  bool printMessage(Error& error, bool muteStdout = false);
  bool printStats(Stats stats, bool muteStdout = false);
  bool printToLogFile(const std::string& report);
  bool hasFatalErrors() const;
  Stats getErrorStats() const;
  void appendErrors(ErrorContainer&);
  SymbolTable* getSymbolTable() { return m_symbolTable; }
  std::tuple<std::string, bool, bool> createErrorMessage(
      const Error& error, bool reentrantPython = true) const;
  void setPythonInterp(void* interpState) { m_interpState = interpState; }

 private:
  ErrorContainer(const ErrorContainer& orig) = delete;

  std::pair<std::string, bool> createReport_() const;
  std::pair<std::string, bool> createReport_(const Error& error) const;
  std::vector<Error> m_errors;
  std::set<std::string> m_errorSet;

  CommandLineParser* m_clp;
  bool m_reportedFatalErrorLogFile;
  SymbolTable* const m_symbolTable;
  void* m_interpState;

  LogListener* const m_logListener;
  // TODO: Ownership of passed log listener not very well defined.
  // For now, just delete our listener if we own it.
  const bool m_listenerOwned;
};

};  // namespace SURELOG

#endif /* ERRORCONTAINER_H */
