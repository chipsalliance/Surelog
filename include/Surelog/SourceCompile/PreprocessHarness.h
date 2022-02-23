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
 * File:   PreprocessHarness.h
 * Author: alain
 *
 * Created on June 1, 2021, 8:37 PM
 */

#ifndef SURELOG_PREPROCESSHARNESS_H
#define SURELOG_PREPROCESSHARNESS_H
#pragma once

#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/SourceCompile/CompilationUnit.h>

namespace SURELOG {

class PreprocessHarness {
 public:
  PreprocessHarness();
  std::string preprocess(std::string_view content, CompilationUnit* compUnit = nullptr);

  const ErrorContainer &collected_errors() const { return m_errors; }

 private:
  SymbolTable m_symbols;
  ErrorContainer m_errors;
};

};  // namespace SURELOG

#endif /* SURELOG_PREPROCESSHARNESS_H */
