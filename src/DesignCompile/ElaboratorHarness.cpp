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

#include "Surelog/DesignCompile/ElaboratorHarness.h"

#include <string_view>
#include <tuple>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Design/Design.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"

namespace SURELOG {

ElaboratorHarness::ElaboratorHarness(Session* session) : m_session(session) {}
std::tuple<Design*, FileContent*, CompileDesign*> ElaboratorHarness::elaborate(
    std::string_view content) {
  std::tuple<Design*, FileContent*, CompileDesign*> result;
  CommandLineParser* clp = m_session->getCommandLineParser();
  clp->setCacheAllowed(false);
  clp->setParse(true);
  clp->setCompile(true);
  clp->setElabUhdm(true);
  clp->setWriteUhdm(false);
  clp->fullSVMode(true);
  Compiler* compiler = new Compiler(m_session, content);
  compiler->compile();
  Design* design = compiler->getDesign();
  FileContent* fC = nullptr;
  if (!design->getAllFileContents().empty()) {
    fC = design->getAllFileContents()[0].second;
  }
  result = std::make_tuple(design, fC, compiler->getCompileDesign());
  return result;
}

}  // namespace SURELOG
