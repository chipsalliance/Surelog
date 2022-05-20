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
 * File:   UhdmWriter.h
 * Author: alain
 *
 * Created on January 17, 2020, 9:12 PM
 */

#ifndef SURELOG_UHDMWRITER_H
#define SURELOG_UHDMWRITER_H
#pragma once

#include <Surelog/DesignCompile/CompileHelper.h>
#include <Surelog/SourceCompile/VObjectTypes.h>

// UHDM
#include <uhdm/uhdm_forward_decl.h>

#include <string>

namespace SURELOG {

class CompileDesign;
class Design;
class DesignComponent;
class ExprBuilder;
class ModPort;
class ModuleDefinition;
class ModuleInstance;
class Signal;

class UhdmWriter final {
 public:
  typedef std::map<ModPort*, UHDM::modport*> ModPortMap;
  typedef std::map<const DesignComponent*, UHDM::BaseClass*> ComponentMap;
  typedef std::map<Signal*, UHDM::BaseClass*> SignalBaseClassMap;
  typedef std::map<std::string, Signal*> SignalMap;
  typedef std::map<ModuleInstance*, UHDM::BaseClass*> InstanceMap;
  typedef std::map<std::string, UHDM::BaseClass*> VpiSignalMap;

  UhdmWriter(CompileDesign* compiler, Design* design);

  vpiHandle write(const std::string& uhdmFile);

  static unsigned int getVpiDirection(VObjectType type);

  static unsigned int getVpiNetType(VObjectType type);

  static unsigned int getVpiOpType(VObjectType type);

  static unsigned int getStrengthType(VObjectType type);

 private:
  void writeModule(ModuleDefinition* mod, UHDM::module* m, UHDM::Serializer& s,
                   ComponentMap& componentMap, ModPortMap& modPortMap,
                   ModuleInstance* instance = nullptr);
  void writeInterface(ModuleDefinition* mod, UHDM::interface* m,
                      UHDM::Serializer& s, ComponentMap& componentMap,
                      ModPortMap& modPortMap,
                      ModuleInstance* instance = nullptr);
  bool writeElabInterface(UHDM::Serializer& s, ModuleInstance* instance,
                          UHDM::interface* m, ExprBuilder& exprBuilder);
  void writeInstance(ModuleDefinition* mod, ModuleInstance* instance,
                     UHDM::any* m, CompileDesign* compileDesign,
                     ComponentMap& componentMap, ModPortMap& modPortMap,
                     InstanceMap& instanceMap, ExprBuilder& exprBuilder);
  bool writeElabModule(UHDM::Serializer& s, ModuleInstance* instance,
                       UHDM::module* m, ExprBuilder& exprBuilder);
  bool writeElabProgram(UHDM::Serializer& s, ModuleInstance* instance,
                        UHDM::program* m);
  bool writeElabGenScope(UHDM::Serializer& s, ModuleInstance* instance,
                         UHDM::gen_scope* m, ExprBuilder& exprBuilder);
  void writePackage(Package* pack, UHDM::package* p, UHDM::Serializer& s,
                  UhdmWriter::ComponentMap& componentMap);

  void lateBinding(UHDM::Serializer& s, DesignComponent* mod, UHDM::scope* m, UhdmWriter::ComponentMap& componentMap);

  CompileDesign* const m_compileDesign;
  Design* const m_design;
  CompileHelper m_helper;
};

}  // namespace SURELOG

#endif /* SURELOG_UHDMWRITER_H */
