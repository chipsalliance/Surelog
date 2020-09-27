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
 * File:   CompileClass.h
 * Author: alain
 *
 * Created on June 7, 2018, 10:26 PM
 */

#ifndef COMPILECLASS_H
#define COMPILECLASS_H

#include "DesignCompile/CompileHelper.h"

namespace SURELOG {

struct FunctorCompileClass {
  FunctorCompileClass(CompileDesign* compiler, ClassDefinition* classDef,
                      Design* design, SymbolTable* symbols,
                      ErrorContainer* errors)
      : m_compileDesign(compiler),
        m_class(classDef),
        m_design(design),
        m_symbols(symbols),
        m_errors(errors) {}

  int operator()() const;

 private:
  CompileDesign* m_compileDesign;
  ClassDefinition* m_class;
  Design* m_design;
  SymbolTable* m_symbols;
  ErrorContainer* m_errors;
};

class CompileClass final {
 public:
  CompileClass(CompileDesign* compiler, ClassDefinition* classDef,
               Design* design, SymbolTable* symbols, ErrorContainer* errors)
      : m_compileDesign(compiler),
        m_class(classDef),
        m_design(design),
        m_symbols(symbols),
        m_errors(errors) {
    m_helper.seterrorReporting(errors, symbols);
  }

  bool compile();

 private:
  CompileClass(const CompileClass &) = delete;

  CompileDesign* const m_compileDesign;
  ClassDefinition* const m_class;
  Design* const m_design;
  SymbolTable* const m_symbols;
  ErrorContainer* const m_errors;

  CompileHelper m_helper;

  bool compile_class_parameters_(const FileContent* fC, NodeId id);
  bool compile_class_property_(const FileContent* fC, NodeId id);
  bool compile_class_method_(const FileContent* fC, NodeId id);
  bool compile_class_constraint_(const FileContent* fC, NodeId id);
  bool compile_class_declaration_(const FileContent* fC, NodeId id);
  bool compile_covergroup_declaration_(const FileContent* fC, NodeId id);
  bool compile_local_parameter_declaration_(const FileContent* fC, NodeId id);
  bool compile_parameter_declaration_(const FileContent* fC, NodeId id);
  bool compile_class_type_(const FileContent* fC, NodeId id);
};

}  // namespace SURELOG

#endif /* COMPILECLASS_H */
