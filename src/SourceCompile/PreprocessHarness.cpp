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

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Library/Library.h>
#include <Surelog/SourceCompile/CompilationUnit.h>
#include <Surelog/SourceCompile/CompileSourceFile.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/PreprocessHarness.h>

namespace SURELOG {

PreprocessHarness::PreprocessHarness() : m_errors(&m_symbols) {}

std::string PreprocessHarness::preprocess(std::string_view content,
                                          CompilationUnit* compUnit) {
  std::string result;
  PreprocessFile::SpecialInstructions instructions(
      PreprocessFile::SpecialInstructions::DontMute,
      PreprocessFile::SpecialInstructions::DontMark,
      PreprocessFile::SpecialInstructions::DontFilter,
      PreprocessFile::SpecialInstructions::CheckLoop,
      PreprocessFile::SpecialInstructions::ComplainUndefinedMacro,
      PreprocessFile::SpecialInstructions::Evaluate,
      compUnit ? PreprocessFile::SpecialInstructions::Persist
               : PreprocessFile::SpecialInstructions::DontPersist);
  CompilationUnit unit(false);
  CommandLineParser clp(&m_errors, &m_symbols, false, false);
  Library lib("work", &m_symbols);
  Compiler compiler(&clp, &m_errors, &m_symbols);
  CompileSourceFile csf(0, &clp, &m_errors, &compiler, &m_symbols,
                        compUnit ? compUnit : &unit, &lib);
  PreprocessFile pp(0, nullptr, 0, &csf, instructions,
                    compUnit ? compUnit : &unit, &lib, content, nullptr, 0, 0);

  if (!pp.preprocess()) {
    result = "ERROR_PP";
  }
  if (m_errors.hasFatalErrors()) {
    result = "ERROR_PP";
  }
  m_errors.printMessages();
  if (result.empty()) result = pp.getPreProcessedFileContent();
  return result;
}

}  // namespace SURELOG
