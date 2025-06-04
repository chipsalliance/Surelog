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

#include <cstdint>

// UHDM
#include <uhdm/containers.h>

namespace SURELOG {

class CompileDesign;
class Design;
class ErrorContainer;
class ModuleDefinition;
class Session;
class SymbolTable;
class ValuedComponentI;

struct FunctorCompileModule {
  FunctorCompileModule(Session* session, CompileDesign* compiler,
                       ModuleDefinition* mdl, Design* design,
                       ValuedComponentI* instance = nullptr)
      : m_session(session),
        m_compileDesign(compiler),
        m_module(mdl),
        m_design(design),
        m_instance(instance) {}
  FunctorCompileModule(const FunctorCompileModule&) = delete;
  int32_t operator()() const;

 private:
  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  ModuleDefinition* const m_module = nullptr;
  Design* const m_design = nullptr;
  ValuedComponentI* const m_instance = nullptr;
};

class CompileModule final {
 public:
  CompileModule(Session* session, CompileDesign* compiler,
                ModuleDefinition* mdl, Design* design,
                ValuedComponentI* instance = nullptr)
      : m_session(session),
        m_compileDesign(compiler),
        m_module(mdl),
        m_design(design),
        m_helper(session),
        m_instance(instance) {}
  CompileModule(const CompileModule&) = delete;

  bool compile(Elaborate elaborate, Reduce reduce);

 private:
  enum CollectType { FUNCTION, DEFINITION, GENERATE_REGIONS, OTHER };
  bool collectModuleObjects_(CollectType collectType);
  bool checkModule_();
  bool collectInterfaceObjects_(CollectType collectType);
  bool checkInterface_();
  bool collectUdpObjects_();
  void compileClockingBlock_(const FileContent* fC, NodeId id);

  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  ModuleDefinition* const m_module = nullptr;
  Design* const m_design = nullptr;
  CompileHelper m_helper;
  ValuedComponentI* const m_instance = nullptr;
  uint32_t m_nbPorts = 0;
  bool m_hasNonNullPort = false;
  uhdm::AttributeCollection* m_attributes = nullptr;
};

}  // namespace SURELOG

#endif /* SURELOG_COMPILEMODULE_H */
