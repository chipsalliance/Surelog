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

#include <Surelog/Design/DesignComponent.h>
#include <Surelog/DesignCompile/CompileHelper.h>
#include <Surelog/SourceCompile/VObjectTypes.h>

// UHDM
#include <uhdm/uhdm_forward_decl.h>

#include <string>

namespace SURELOG {

class CompileDesign;
class Design;
class ExprBuilder;
class ModPort;
class ModuleDefinition;
class ModuleInstance;
class Netlist;
class Signal;

class UhdmWriter final {
 public:
  typedef std::map<ModPort*, UHDM::modport*> ModPortMap;
  typedef std::map<const ValuedComponentI*, UHDM::BaseClass*> ComponentMap;
  typedef std::map<std::string_view, UHDM::BaseClass*> ModuleMap;
  typedef std::map<Signal*, UHDM::BaseClass*> SignalBaseClassMap;
  typedef std::map<std::string, Signal*, std::less<>> SignalMap;
  typedef std::map<ModuleInstance*, UHDM::BaseClass*> InstanceMap;
  typedef std::map<std::string, UHDM::BaseClass*> VpiSignalMap;

  UhdmWriter(CompileDesign* compiler, Design* design);

  vpiHandle write(PathId uhdmFileId);

  static uint32_t getVpiDirection(VObjectType type);

  static uint32_t getVpiNetType(VObjectType type);

  static uint32_t getVpiOpType(VObjectType type);

  static uint32_t getStrengthType(VObjectType type);

  static std::string builtinGateName(VObjectType type);

 private:
  void writePorts(std::vector<Signal*>& orig_ports, UHDM::BaseClass* parent,
                  UHDM::VectorOfport* dest_ports, UHDM::VectorOfnet* dest_nets,
                  UHDM::Serializer& s, ModPortMap& modPortMap,
                  SignalBaseClassMap& signalBaseMap, SignalMap& signalMap,
                  ModuleInstance* instance = nullptr,
                  ModuleDefinition* mod = nullptr);
  void writeNets(DesignComponent* mod, std::vector<Signal*>& orig_nets,
                 UHDM::BaseClass* parent, UHDM::VectorOfnet* dest_nets,
                 UHDM::Serializer& s, SignalBaseClassMap& signalBaseMap,
                 SignalMap& signalMap, SignalMap& portMap,
                 ModuleInstance* instance = nullptr);
  void writeVariables(const DesignComponent::VariableMap& orig_vars,
                      UHDM::BaseClass* parent,
                      UHDM::VectorOfvariables* dest_vars, UHDM::Serializer& s);
  void writeModule(ModuleDefinition* mod, UHDM::module_inst* m,
                   UHDM::Serializer& s, ModuleMap& moduleMap,
                   ModPortMap& modPortMap, ModuleInstance* instance = nullptr);
  void writeInterface(ModuleDefinition* mod, UHDM::interface_inst* m,
                      UHDM::Serializer& s, ModPortMap& modPortMap,
                      ModuleInstance* instance = nullptr);
  bool writeElabInterface(UHDM::Serializer& s, ModuleInstance* instance,
                          UHDM::interface_inst* m, ExprBuilder& exprBuilder);
  void writeInstance(ModuleDefinition* mod, ModuleInstance* instance,
                     UHDM::any* m, CompileDesign* compileDesign,
                     ModPortMap& modPortMap, InstanceMap& instanceMap,
                     ExprBuilder& exprBuilder);
  bool writeElabModule(UHDM::Serializer& s, ModuleInstance* instance,
                       UHDM::module_inst* m, ExprBuilder& exprBuilder);
  bool writeElabProgram(UHDM::Serializer& s, ModuleInstance* instance,
                        UHDM::program* m, ModPortMap& modPortMap);
  bool writeElabGenScope(UHDM::Serializer& s, ModuleInstance* instance,
                         UHDM::gen_scope* m, ExprBuilder& exprBuilder);
  void writePackage(Package* pack, UHDM::package* p, UHDM::Serializer& s,
                    bool elaborated);

  void writeClasses(ClassNameClassDefinitionMultiMap& orig_classes,
                    UHDM::VectorOfclass_defn* dest_classes, UHDM::Serializer& s,
                    UHDM::BaseClass* parent);
  void writeClass(ClassDefinition* classDef,
                  UHDM::VectorOfclass_defn* dest_classes, UHDM::Serializer& s,
                  UHDM::BaseClass* parent);
  void writeProgram(Program* mod, UHDM::program* m, UHDM::Serializer& s,
                    ModPortMap& modPortMap, ModuleInstance* instance = nullptr);
  void writeCont_assign(Netlist* netlist, UHDM::Serializer& s,
                        DesignComponent* mod, UHDM::any* scope,
                        std::vector<UHDM::cont_assign*>* assigns);

  void lateBinding(UHDM::Serializer& s, DesignComponent* mod, UHDM::scope* m);
  void lateTypedefBinding(UHDM::Serializer& s, DesignComponent* mod,
                          UHDM::scope* m);

  CompileDesign* const m_compileDesign;
  Design* const m_design;
  ComponentMap m_componentMap;
  CompileHelper m_helper;
};

}  // namespace SURELOG

#endif /* SURELOG_UHDMWRITER_H */
