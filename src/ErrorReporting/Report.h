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
 * File:   Report.h
 * Author: alain
 *
 * Created on April 10, 2017, 8:56 PM
 */

#ifndef REPORT_H
#define REPORT_H

#include <utility>

#include "CommandLine/CommandLineParser.h"
#include "SourceCompile/SymbolTable.h"

namespace SURELOG {

class Report final {
 public:
  Report() {}
  std::pair<bool, bool> makeDiffCompUnitReport(CommandLineParser* clp,
                                               SymbolTable* st);

 private:
  Report(const Report& orig) = delete;
};

}  // namespace SURELOG
#endif /* REPORT_H */
