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
 * File:   PreprocessHarness.cpp
 * Author: alain
 *
 * Created on June 1, 2021, 8:37 PM
 */

#include "Surelog/SourceCompile/PreprocessHarness.h"

#include "Surelog/Common/Session.h"
#include "Surelog/Library/Library.h"
#include "Surelog/SourceCompile/CompilationUnit.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/PreprocessFile.h"

namespace SURELOG {

PreprocessHarness::PreprocessHarness() : m_ownsSession(true) {}

PreprocessHarness::PreprocessHarness(Session* session)
    : m_session(session), m_ownsSession(false) {}

PreprocessHarness::~PreprocessHarness() {
  if (m_ownsSession) delete m_session;
}

std::string PreprocessHarness::preprocess(std::string_view content,
                                          CompilationUnit* compUnit,
                                          PathId fileId) {
  PreprocessFile::SpecialInstructions instructions(
      PreprocessFile::SpecialInstructions::DontMute,
      PreprocessFile::SpecialInstructions::DontMark,
      PreprocessFile::SpecialInstructions::DontFilter,
      PreprocessFile::SpecialInstructions::CheckLoop,
      PreprocessFile::SpecialInstructions::ComplainUndefinedMacro,
      PreprocessFile::SpecialInstructions::Evaluate,
      compUnit ? PreprocessFile::SpecialInstructions::Persist
               : PreprocessFile::SpecialInstructions::DontPersist);
  if (m_session == nullptr) m_session = new Session;
  CompilationUnit unit(false);
  Library lib(m_session, "work");
  Compiler compiler(m_session);
  CompileSourceFile csf(m_session, BadPathId, &compiler,
                        compUnit ? compUnit : &unit, &lib);
  PreprocessFile pp(m_session, BadSymbolId, &csf, instructions,
                    compUnit ? compUnit : &unit, &lib, nullptr, 0, content,
                    nullptr, fileId, BadPathId, 0);

  std::string result;
  if (!pp.preprocess()) {
    result = "ERROR_PP";
  }

  ErrorContainer* const errors = m_session->getErrorContainer();
  if (errors->hasFatalErrors()) {
    result = "ERROR_PP";
  }
  errors->printMessages();
  if (result.empty()) result = std::get<0>(pp.getPreProcessedFileContent());
  return result;
}

const ErrorContainer& PreprocessHarness::collectedErrors() const {
  return *m_session->getErrorContainer();
}
}  // namespace SURELOG
