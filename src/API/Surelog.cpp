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

#include <Surelog/API/Surelog.h>
#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Design/Design.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/SourceCompile/Compiler.h>

namespace SURELOG {

scompiler* start_compiler(CommandLineParser* clp) {
  Compiler* the_compiler =
      new Compiler(clp, clp->getErrorContainer(), clp->mutableSymbolTable());
  bool status = the_compiler->compile();
  if (!status) return nullptr;
  return (scompiler*)the_compiler;
}

Design* get_design(scompiler* the_compiler) {
  if (the_compiler) return ((Compiler*)the_compiler)->getDesign();
  return nullptr;
}

void shutdown_compiler(scompiler* the_compiler) {
  if (the_compiler == nullptr) return;
  Compiler* compiler = (Compiler*)the_compiler;
  if (CompileDesign* comp = compiler->getCompileDesign()) {
    comp->getSerializer().Purge();
  }
  delete (Compiler*)the_compiler;
}

vpiHandle get_uhdm_design(scompiler* compiler) {
  vpiHandle design_handle = 0;
  Compiler* the_compiler = (Compiler*)compiler;
  if (the_compiler) {
    design_handle = the_compiler->getUhdmDesign();
  }
  return design_handle;
}

}  // namespace SURELOG
