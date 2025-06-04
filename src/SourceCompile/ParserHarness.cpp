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
 * File:   ParserHarness.cpp
 * Author: alain
 *
 * Created on June 05, 2021, 90:03 AM
 */

#include "Surelog/SourceCompile/ParserHarness.h"

#include <memory>
#include <string_view>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/Library/Library.h"
#include "Surelog/SourceCompile/CompilationUnit.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"

namespace SURELOG {

struct ParserHarness::Holder {
  std::unique_ptr<CompilationUnit> m_unit;
  std::unique_ptr<Library> m_lib;
  std::unique_ptr<Compiler> m_compiler;
  std::unique_ptr<CompileSourceFile> m_csf;
  std::unique_ptr<ParseFile> m_pf;
};

ParserHarness::ParserHarness() : m_ownsSession(true) {}

ParserHarness::ParserHarness(Session* session)
    : m_session(session), m_ownsSession(false) {}

ParserHarness::~ParserHarness() {
  if (m_ownsSession) delete m_session;
  delete m_h;
}

std::unique_ptr<FileContent> ParserHarness::parse(std::string_view content) {
  delete m_h;
  m_h = new Holder;

  if (m_ownsSession) {
    delete m_session;
    m_session = new Session;
  }

  CommandLineParser* const clp = m_session->getCommandLineParser();
  clp->setCacheAllowed(false);

  m_h->m_unit = std::make_unique<CompilationUnit>(false);
  m_h->m_lib = std::make_unique<Library>(m_session, "work");
  m_h->m_compiler = std::make_unique<Compiler>(m_session);
  m_h->m_csf = std::make_unique<CompileSourceFile>(
      m_session, BadPathId, m_h->m_compiler.get(), m_h->m_unit.get(),
      m_h->m_lib.get());
  m_h->m_pf.reset(new ParseFile(m_session, content, m_h->m_csf.get(),
                                m_h->m_unit.get(), m_h->m_lib.get()));
  std::unique_ptr<FileContent> file_content_result(
      std::make_unique<FileContent>(m_session, BadPathId, m_h->m_lib.get(),
                                    nullptr, BadPathId));
  m_h->m_pf->setFileContent(file_content_result.get());
  if (!m_h->m_pf->parse()) file_content_result.reset(nullptr);
  return file_content_result;
}

FileContent* ParserHarness::parse(std::string_view content, Compiler* compiler,
                                  PathId fileId) {
  if (m_ownsSession) {
    delete m_session;
    m_session = new Session;
  }

  CompilationUnit* const unit = new CompilationUnit(false);
  Library* const lib = new Library(m_session, "work");
  CompileSourceFile* const csf =
      new CompileSourceFile(m_session, fileId, compiler, unit, lib);
  ParseFile* const pf = new ParseFile(m_session, content, csf, unit, lib);
  FileContent* file_content_result =
      new FileContent(m_session, fileId, lib, nullptr, BadPathId);
  pf->setFileContent(file_content_result);
  if (!pf->parse()) file_content_result = nullptr;
  return file_content_result;
}

}  // namespace SURELOG
