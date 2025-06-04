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

#include "Surelog/API/Surelog.h"

#include <vector>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Design/Design.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/AstListener.h"

namespace SURELOG {

scompiler* start_compiler(Session* session) {
  Compiler* the_compiler = new Compiler(session);
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
    comp->getSerializer().purge();
  }
  delete (Compiler*)the_compiler;
}

uhdm::Design* get_uhdm_design(scompiler* compiler) {
  if (Design* design = get_design(compiler)) {
    return design->getUhdmDesign();
  }
  return nullptr;
}

vpiHandle get_vpi_design(scompiler* compiler) {
  vpiHandle design_handle = nullptr;
  Compiler* the_compiler = (Compiler*)compiler;
  if (the_compiler) {
    design_handle = the_compiler->getVpiDesign();
  }
  return design_handle;
}

void walk(scompiler* compiler, AstListener* listener) {
  if (!compiler || !listener) return;
  Compiler* the_compiler = (Compiler*)compiler;
  for (const CompileSourceFile* csf : the_compiler->getCompileSourceFiles()) {
    ParseFile* const parser = csf->getParser();
    FileContent* const fC = parser->getFileContent();
    if (listener->shouldWalkSourceFile(fC->getSession(), fC->getFileId())) {
      const std::vector<VObject>& objects = fC->getVObjects();
      listener->listen(fC->getSession(), fC->getFileId(),
                       parser->getSourceText(), objects.data(), objects.size());
    }
  }
}

}  // namespace SURELOG
