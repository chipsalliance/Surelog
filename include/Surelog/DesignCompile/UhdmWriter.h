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

#include <Surelog/Common/Containers.h>
#include <Surelog/Common/PathId.h>
#include <Surelog/Design/DesignComponent.h>
#include <Surelog/DesignCompile/CompileHelper.h>
#include <Surelog/SourceCompile/VObjectTypes.h>

#include <cstdint>
#include <functional>
#include <map>
#include <string_view>
#include <vector>

// UHDM
#include <uhdm/Serializer.h>
#include <uhdm/containers.h>
#include <uhdm/uhdm_forward_decl.h>

#include <string>

namespace SURELOG {

class CompileDesign;
class Design;
class ExprBuilder;
class Modport;
class ModuleDefinition;
class ModuleInstance;
class Netlist;
class Session;
class Signal;

class UhdmWriter final {
 public:
  using ModportMap = std::map<Modport*, uhdm::Modport*>;
  using ComponentMap = std::map<const ValuedComponentI*, uhdm::BaseClass*>;
  using ModuleMap = std::map<std::string_view, uhdm::BaseClass*>;
  using SignalBaseClassMap = std::map<Signal*, uhdm::BaseClass*>;
  using SignalMap = std::map<std::string, Signal*, std::less<>>;
  using VpiSignalMap = std::map<std::string, uhdm::BaseClass*>;
  using ModuleInstanceMap = std::map<ModuleInstance*, uhdm::Module*>;
  using InstanceDefinitionMap = std::map<std::string_view, uhdm::Instance*>;

  UhdmWriter(Session* session, CompileDesign* compiler, Design* design);

  bool write(PathId uhdmFileId);

  static uint32_t getVpiDirection(VObjectType type);

  static uint32_t getVpiNetType(VObjectType type);

  static uint32_t getVpiOpType(VObjectType type);

  static uint32_t getStrengthType(VObjectType type);

  static std::string builtinGateName(VObjectType type);

 private:
  void writePorts(const std::vector<Signal*>& orig_ports,
                  uhdm::BaseClass* parent, uhdm::Serializer& s,
                  ModportMap& modPortMap, SignalBaseClassMap& signalBaseMap,
                  SignalMap& signalMap, ModuleInstance* instance = nullptr,
                  DesignComponent* mod = nullptr);
  void writeNets(DesignComponent* mod, const std::vector<Signal*>& orig_nets,
                 uhdm::BaseClass* parent, uhdm::Serializer& s,
                 SignalBaseClassMap& signalBaseMap, SignalMap& signalMap,
                 SignalMap& portMap, ModuleInstance* instance = nullptr);
  void writeDataTypes(const DesignComponent::DataTypeMap& datatypeMap,
                      uhdm::BaseClass* parent,
                      uhdm::TypespecCollection* dest_typespecs,
                      uhdm::Serializer& s, bool setParent);
  void writeImportedSymbols(DesignComponent* mod, uhdm::Serializer& s,
                            uhdm::TypespecCollection* typespecs);
  void writeVariables(const DesignComponent::VariableMap& orig_vars,
                      uhdm::BaseClass* parent, uhdm::Serializer& s);
  void writeModule(ModuleDefinition* mod, uhdm::Module* m, uhdm::Serializer& s,
                   InstanceDefinitionMap& instanceDefinitionMap,
                   ModportMap& modPortMap, ModuleInstance* instance = nullptr);
  void writeInterface(ModuleDefinition* mod, uhdm::Interface* m,
                      uhdm::Serializer& s, ModportMap& modPortMap,
                      ModuleInstance* instance = nullptr);
  bool writeElabInterface(uhdm::Serializer& s, ModuleInstance* instance,
                          uhdm::Interface* m, ExprBuilder& exprBuilder);
  void writeInstance(ModuleDefinition* mod, ModuleInstance* instance,
                     uhdm::Any* m, CompileDesign* compileDesign,
                     ModportMap& modPortMap,
                     ModuleInstanceMap& moduleInstanceMap,
                     ExprBuilder& exprBuilder);
  bool writeElabModule(uhdm::Serializer& s, ModuleInstance* instance,
                       uhdm::Module* m, ExprBuilder& exprBuilder);
  bool writeElabProgram(uhdm::Serializer& s, ModuleInstance* instance,
                        uhdm::Program* m, ModportMap& modPortMap);
  bool writeElabGenScope(uhdm::Serializer& s, ModuleInstance* instance,
                         uhdm::GenScope* m, ExprBuilder& exprBuilder);
  void writePackage(Package* pack, uhdm::Package* p, uhdm::Serializer& s,
                    bool elaborated);

  void writeClasses(ClassNameClassDefinitionMultiMap& orig_classes,
                    uhdm::Serializer& s, uhdm::BaseClass* parent);
  void writeClass(ClassDefinition* classDef, uhdm::Serializer& s,
                  uhdm::BaseClass* parent);
  void writeProgram(Program* mod, uhdm::Program* m, uhdm::Serializer& s,
                    ModportMap& modPortMap, ModuleInstance* instance = nullptr);
  void writeContAssign(Netlist* netlist, uhdm::Serializer& s,
                       DesignComponent* mod, uhdm::Any* scope,
                       std::vector<uhdm::ContAssign*>* assigns);

  uhdm::Any* swapForSpecifiedVar(uhdm::Serializer& s, DesignComponent* mod,
                                 uhdm::Any* tmp,
                                 uhdm::VariablesCollection* lvariables,
                                 uhdm::Variables* lvariable,
                                 std::string_view name, const uhdm::Any* var,
                                 const uhdm::Any* parent);
  void bind(uhdm::Serializer& s, const std::vector<vpiHandle>& designs);

 private:
  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  Design* const m_design = nullptr;
  ComponentMap m_componentMap;
  CompileHelper m_helper;
};

}  // namespace SURELOG

#endif /* SURELOG_UHDMWRITER_H */
