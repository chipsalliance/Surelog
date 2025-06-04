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

#include "Surelog/DesignCompile/CompilerHarness.h"

#include <memory>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/Session.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/SymbolTable.h"

namespace SURELOG {

CompilerHarness::CompilerHarness(Session* session) : m_session(session) {}

struct CompilerHarness::Holder {
  explicit Holder(Session* session)
      : m_session(session), compiler(new Compiler(m_session)) {
    session->getCommandLineParser()->setCacheAllowed(false);
  }
  Session* const m_session = nullptr;
  std::unique_ptr<Compiler> compiler;
};

std::unique_ptr<CompileDesign> CompilerHarness::createCompileDesign() {
  delete m_h;
  m_h = new Holder(m_session);
  return std::make_unique<CompileDesign>(m_session, m_h->compiler.get());
}

CompilerHarness::~CompilerHarness() { delete m_h; }

}  // namespace SURELOG
