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
 * File:   CompilePackage.h
 * Author: alain
 *
 * Created on March 22, 2018, 9:57 PM
 */

#ifndef SURELOG_COMPILEPACKAGE_H
#define SURELOG_COMPILEPACKAGE_H
#pragma once

#include <Surelog/DesignCompile/CompileHelper.h>

namespace SURELOG {

class CompileDesign;
class Design;
class ErrorContainer;
class Package;
class SymbolTable;

struct FunctorCompilePackage {
  FunctorCompilePackage(CompileDesign* compiler, Package* package,
                        Design* design, SymbolTable* symbols,
                        ErrorContainer* errors)
      : m_compileDesign(compiler),
        m_package(package),
        m_design(design),
        m_symbols(symbols),
        m_errors(errors) {}
  int operator()() const;

 private:
  CompileDesign* const m_compileDesign;
  Package* const m_package;
  Design* const m_design;
  SymbolTable* const m_symbols;
  ErrorContainer* const m_errors;
};

class CompilePackage final {
 public:
  CompilePackage(CompileDesign* compiler, Package* package, Design* design,
                 SymbolTable* symbols, ErrorContainer* errors)
      : m_compileDesign(compiler),
        m_package(package),
        m_design(design),
        m_symbols(symbols),
        m_errors(errors) {
    m_helper.seterrorReporting(errors, symbols);
  }

  bool compile();

 private:
  enum CollectType { FUNCTION, DEFINITION, OTHER };
  bool collectObjects_(CollectType collectType);

  CompileDesign* const m_compileDesign;
  Package* const m_package;
  Design* const m_design;
  SymbolTable* const m_symbols;
  ErrorContainer* const m_errors;
  CompileHelper m_helper;
};

}  // namespace SURELOG

#endif /* SURELOG_COMPILEPACKAGE_H */
