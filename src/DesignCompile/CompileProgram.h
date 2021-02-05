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
 * File:   CompileProgram.h
 * Author: alain
 *
 * Created on June 6, 2018, 10:43 PM
 */

#ifndef COMPILEPROGRAM_H
#define COMPILEPROGRAM_H

#include "DesignCompile/CompileToolbox.h"
#include "DesignCompile/CompileHelper.h"

namespace SURELOG {

struct FunctorCompileProgram {
  FunctorCompileProgram(CompileDesign* compiler, Program* program,
                        Design* design, SymbolTable* symbols,
                        ErrorContainer* errors)
      : m_compileDesign(compiler),
        m_program(program),
        m_design(design),
        m_symbols(symbols),
        m_errors(errors) {}
  int operator()() const;

 private:
  CompileDesign* m_compileDesign;
  Program* m_program;
  Design* m_design;
  SymbolTable* m_symbols;
  ErrorContainer* m_errors;
};

class CompileProgram : public CompileToolbox {
public:
  CompileProgram(CompileDesign* compiler, Program* program, Design* design,
                 SymbolTable* symbols, ErrorContainer* errors)
      : m_compileDesign(compiler),
        m_program(program),
        m_design(design),
        m_symbols(symbols),
        m_errors(errors) {
    m_helper.seterrorReporting(errors, symbols);
  }

  bool compile();

  ~CompileProgram() override;

private:
  enum CollectType { FUNCTION, DEFINITION, OTHER };
  bool collectObjects_(CollectType collectType);
  
  CompileDesign* const m_compileDesign;
  Program* const m_program;
  Design* const m_design;
  SymbolTable* const m_symbols;
  ErrorContainer* const m_errors;

  CompileHelper m_helper;
};

}  // namespace SURELOG

#endif /* COMPILEPROGRAM_H */
