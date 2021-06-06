/*
  Copyright 2021 Alain Dargelas

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
 * File:   CompilerHarness.cpp
 * Author: alain
 *
 * Created on June 05, 2021, 90:03 AM
 */
#include "DesignCompile/CompilerHarness.h"

namespace SURELOG {

CompileDesign* CompilerHarness::getCompileDesign() {
  SymbolTable* symbols = new SymbolTable();
  ErrorContainer* errors = new ErrorContainer(symbols);
  CommandLineParser* clp = new CommandLineParser(errors, symbols, false, false);
  Compiler* compiler = new Compiler(clp, errors, symbols);
  CompileDesign* compileDesign = new CompileDesign(compiler);
  return compileDesign;
}

}  // namespace SURELOG
