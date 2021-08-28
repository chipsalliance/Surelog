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

#ifndef PREPROCESSHARNESS_H
#define PREPROCESSHARNESS_H

#include <map>
#include <set>
#include <string>
#include <string_view>
#include <thread>

#include "Config/ConfigSet.h"
#include "Design/Design.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Library/LibrarySet.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/SymbolTable.h"
#include "sv_vpi_user.h"

namespace SURELOG {

class PreprocessHarness {
 public:
  PreprocessHarness();
  std::string preprocess(std::string_view content);

  const ErrorContainer &collected_errors() const { return m_errors; }

 private:
  SymbolTable m_symbols;
  ErrorContainer m_errors;
};

};  // namespace SURELOG

#endif /* PREPROCESSHARNESS_H */
