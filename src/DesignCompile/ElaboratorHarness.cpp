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
 * File:   ElaboratorHarness.cpp
 * Author: alain
 *
 * Created on June 08, 2021, 10:03 PM
 */
#include "DesignCompile/ElaboratorHarness.h"

namespace SURELOG {

std::tuple<Design*, FileContent*, CompileDesign*> ElaboratorHarness::elaborate(
    const std::string& content) {
  std::tuple<Design*, FileContent*, CompileDesign*> result;
  Design* design = nullptr;
  CompilationUnit* unit = new CompilationUnit(false);
  SymbolTable* symbols = new SymbolTable();
  ErrorContainer* errors = new ErrorContainer(symbols);
  CommandLineParser* clp = new CommandLineParser(errors, symbols, false, false);
  clp->setCacheAllowed(false);
  Library* lib = new Library("work", symbols);
  Compiler* compiler = new Compiler(clp, errors, symbols);
  CompileSourceFile* csf =
      new CompileSourceFile(0, clp, errors, compiler, symbols, unit, lib);
  ParseFile* pf = new ParseFile(content, csf, unit, lib);
  if (!pf->parse()) {
    return result;
  }
  FileContent* fC = pf->getFileContent();
  CompileDesign* compileDesign = new CompileDesign(compiler);
  design = compileDesign->getCompiler()->getDesign();
  compileDesign->compile();
  compileDesign->elaborate();
  result = std::make_tuple(design, fC, compileDesign);
  return result;
}

}  // namespace SURELOG
