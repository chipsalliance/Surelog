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

/*
 * File:   ExprBuilder.h
 * Author: alain
 *
 * Created on November 2, 2017, 9:45 PM
 */

#ifndef EXPRBUILDER_H
#define EXPRBUILDER_H

#include "Design/FileContent.h"
#include "Design/ValuedComponentI.h"
#include "Expression/Value.h"
#include "Library/Library.h"
#include "SourceCompile/SymbolTable.h"

namespace SURELOG {

class ErrorContainer;
class Design;

class ExprBuilder final {
 public:
  ExprBuilder() {}
  Value* evalExpr(const FileContent*, NodeId id,
                  ValuedComponentI* instance = nullptr,
                  bool muteErrors = false);
  Value* fromVpiValue(const std::string& value, unsigned short size);
  Value* fromString(const std::string& value);
  Value* clone(Value* val);
  void seterrorReporting(ErrorContainer* errors, SymbolTable* symbols) {
    m_errors = errors;
    m_symbols = symbols;
  }
  void setDesign(Design* design) { m_design = design; }
  void deleteValue(Value* value) { m_valueFactory.deleteValue(value); }
  ValueFactory& getValueFactory() { return m_valueFactory; }

 private:
  ExprBuilder(const ExprBuilder& orig) = delete;

  ValueFactory m_valueFactory;
  ErrorContainer* m_errors = nullptr;
  SymbolTable* m_symbols = nullptr;
  Design* m_design = nullptr;
};

}  // namespace SURELOG

#endif /* EXPRBUILDER_H */
