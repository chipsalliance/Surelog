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

#include "CommandLine/CommandLineParser.h"
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "ErrorReporting/ErrorContainer.h"
#include "ErrorReporting/Report.h"
#include "ErrorReporting/Waiver.h"
#include "Surelog.h"


SURELOG::scompiler* SURELOG::start_compiler (SURELOG::CommandLineParser* clp) {
  Compiler* the_compiler = new SURELOG::Compiler(clp, clp->getErrorContainer(),
						 clp->mutableSymbolTable());
  bool status = the_compiler->compile();
  if (!status)
    return nullptr;
  return (SURELOG::scompiler*) the_compiler;
}

SURELOG::Design* SURELOG::get_design(SURELOG::scompiler* the_compiler) {
  if (the_compiler)
    return ((SURELOG::Compiler*) the_compiler)->getDesign();
  return nullptr;
}

void SURELOG::shutdown_compiler(SURELOG::scompiler* the_compiler) {
  delete (SURELOG::Compiler*) the_compiler;
}

vpiHandle SURELOG::get_uhdm_design(SURELOG::scompiler* compiler) {
  vpiHandle design_handle = 0;
  SURELOG::Compiler* the_compiler = (SURELOG::Compiler*) compiler;
  if (the_compiler) {
    design_handle = the_compiler->getUhdmDesign();
  }
  return design_handle;
}
