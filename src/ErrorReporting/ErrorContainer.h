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
#include <string>
#include <vector>
#include <set>
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/Error.h"

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

  ErrorContainer(SymbolTable* symbolTable, LogListener *const logListener = nullptr);
  void regiterCmdLine(CommandLineParser* clp) { m_clp = clp; }
  void init();
  Error& addError(Error& error, bool showDuplicates = false,
                  bool reentrantPython = true);
  ErrorContainer(const ErrorContainer& orig);
  virtual ~ErrorContainer();
  std::vector<Error>& getErrors() { return m_errors; }
  bool printMessages(bool muteStdout = false);
  bool printMessage(Error& error, bool muteStdout = false);
  bool printStats(Stats stats, bool muteStdout = false);
  bool printToLogFile(const std::string &report);
  bool hasFatalErrors();
  Stats getErrorStats();
  void appendErrors(ErrorContainer&);
  SymbolTable* getSymbolTable() { return m_symbolTable; }
  std::tuple<std::string, bool, bool> createErrorMessage(
      Error& error, bool reentrantPython = true);
  void setPythonInterp(void* interpState) {
    m_interpState = interpState;
  }

 private:
  std::pair<std::string, bool> createReport_();
  std::pair<std::string, bool> createReport_(Error& error);
  std::vector<Error> m_errors;
  std::set<std::string> m_errorSet;
  CommandLineParser* m_clp;
  bool m_reportedFatalErrorLogFile;
  SymbolTable* m_symbolTable;
  void* m_interpState;
  LogListener* m_logListener;
};

};  // namespace SURELOG

#endif /* ERRORCONTAINER_H */
