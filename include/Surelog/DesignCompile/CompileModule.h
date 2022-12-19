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
 * File:   CompileModule.h
 * Author: alain
 *
 * Created on March 22, 2018, 9:43 PM
 */

#ifndef SURELOG_COMPILEMODULE_H
#define SURELOG_COMPILEMODULE_H
#pragma once

#include <Surelog/DesignCompile/CompileHelper.h>

namespace SURELOG {

class CompileDesign;
class Design;
class ErrorContainer;
class ModuleDefinition;
class SymbolTable;
class ValuedComponentI;

struct FunctorCompileModule {
  FunctorCompileModule(CompileDesign* compiler, ModuleDefinition* mdl,
                       Design* design, SymbolTable* symbols,
                       ErrorContainer* errors,
                       ValuedComponentI* instance = nullptr)
      : m_compileDesign(compiler),
        m_module(mdl),
        m_design(design),
        m_symbols(symbols),
        m_errors(errors),
        m_instance(instance) {}
  int operator()() const;

 private:
  CompileDesign* const m_compileDesign;
  ModuleDefinition* const m_module;
  Design* const m_design;
  SymbolTable* const m_symbols;
  ErrorContainer* const m_errors;
  ValuedComponentI* const m_instance;
};

class CompileModule final {
 public:
  CompileModule(CompileDesign* compiler, ModuleDefinition* mdl,
                Design* design, SymbolTable* symbols, ErrorContainer* errors,
                ValuedComponentI* instance = nullptr)
      : m_compileDesign(compiler),
        m_module(mdl),
        m_design(design),
        m_symbols(symbols),
        m_errors(errors),
        m_instance(instance) {
    m_helper.seterrorReporting(errors, symbols);
  }

  bool compile();

 private:
  CompileModule(const CompileModule&) = delete;
  enum CollectType { FUNCTION, DEFINITION, OTHER };
  bool collectModuleObjects_(CollectType collectType);
  bool checkModule_();
  bool collectInterfaceObjects_(CollectType collectType);
  bool checkInterface_();
  bool collectUdpObjects_();
  void compileClockingBlock_(const FileContent* fC, NodeId id);

  CompileDesign* const m_compileDesign;
  ModuleDefinition* const m_module;
  Design* const m_design;
  SymbolTable* const m_symbols;
  ErrorContainer* const m_errors;
  CompileHelper m_helper;
  ValuedComponentI* const m_instance;
  uint32_t m_nbPorts = 0;
  bool m_hasNonNullPort = false;
  UHDM::VectorOfattribute* m_attributes = nullptr;
};

}  // namespace SURELOG

#endif /* SURELOG_COMPILEMODULE_H */
