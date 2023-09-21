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
 * File:   ModuleDefinition.h
 * Author: alain
 *
 * Created on October 20, 2017, 10:29 PM
 */

#ifndef SURELOG_MODULEDEFINITION_H
#define SURELOG_MODULEDEFINITION_H
#pragma once

#include <Surelog/Common/ClockingBlockHolder.h>
#include <Surelog/Common/Containers.h>
#include <Surelog/Common/SymbolId.h>
#include <Surelog/Design/DesignComponent.h>
#include <Surelog/Design/ModPort.h>

// UHDM
#include <uhdm/containers.h>

#include <string_view>
#include <vector>

namespace SURELOG {

class CompileModule;
class FileContent;

class ModuleDefinition : public DesignComponent, public ClockingBlockHolder {
  SURELOG_IMPLEMENT_RTTI(ModuleDefinition, DesignComponent)
  friend CompileModule;

 public:
  ModuleDefinition(const FileContent* fileContent, NodeId nodeId,
                   std::string_view name);

  ~ModuleDefinition() override = default;

  std::string_view getName() const override { return m_name; }
  VObjectType getType() const override;
  bool isInstance() const override;
  uint32_t getSize() const override;

  typedef std::map<std::string, ClockingBlock> ClockingBlockMap;
  typedef std::map<std::string, ModPort, std::less<>> ModPortSignalMap;
  typedef std::map<std::string, std::vector<ClockingBlock>, std::less<>>
      ModPortClockingBlockMap;

  ModPortSignalMap& getModPortSignalMap() { return m_modportSignalMap; }
  ModPortClockingBlockMap& getModPortClockingBlockMap() {
    return m_modportClockingBlockMap;
  }
  void insertModPort(std::string_view modport, const Signal& signal,
                     NodeId nodeId);
  void insertModPort(std::string_view modport, ClockingBlock& block);
  const Signal* getModPortSignal(std::string_view modport, NodeId port) const;
  ModPort* getModPort(std::string_view modport);

  const ClockingBlock* getModPortClockingBlock(std::string_view modport,
                                               NodeId port) const;

  ClassNameClassDefinitionMultiMap& getClassDefinitions() {
    return m_classDefinitions;
  }
  void addClassDefinition(std::string_view className,
                          ClassDefinition* classDef) {
    m_classDefinitions.emplace(className, classDef);
  }
  ClassDefinition* getClassDefinition(std::string_view name);

  void setGenBlockId(NodeId id) { m_gen_block_id = id; }
  NodeId getGenBlockId() const { return m_gen_block_id; }
  UHDM::udp_defn* getUdpDefn() { return m_udpDefn; }

  UHDM::VectorOfattribute* Attributes() const { return attributes_; }

  bool Attributes(UHDM::VectorOfattribute* data) {
    attributes_ = data;
    return true;
  }
  std::vector<UHDM::module_array*>* getModuleArrays() { return m_moduleArrays; }
  void setModuleArrays(std::vector<UHDM::module_array*>* modules) {
    m_moduleArrays = modules;
  }

  std::vector<UHDM::ref_module*>* getRefModules() { return m_ref_modules; }
  void setRefModules(std::vector<UHDM::ref_module*>* modules) {
    m_ref_modules = modules;
  }

  UHDM::VectorOfprimitive* getPrimitives() { return m_subPrimitives; }
  UHDM::VectorOfprimitive_array* getPrimitiveArrays() {
    return m_subPrimitiveArrays;
  }
  UHDM::VectorOfgen_scope_array* getGenScopeArrays() {
    return m_subGenScopeArrays;
  }
  std::vector<UHDM::gen_stmt*>* getGenStmts() { return m_genStmts; }
  void setPrimitives(UHDM::VectorOfprimitive* primitives) {
    m_subPrimitives = primitives;
  }
  void setPrimitiveArrays(UHDM::VectorOfprimitive_array* primitives) {
    m_subPrimitiveArrays = primitives;
  }
  void setGenScopeArrays(UHDM::VectorOfgen_scope_array* gen_arrays) {
    m_subGenScopeArrays = gen_arrays;
  }
  void setGenStmts(std::vector<UHDM::gen_stmt*>* gen_stmts) {
    m_genStmts = gen_stmts;
  }
  std::string_view getEndLabel() const { return m_endLabel; }
  void setEndLabel(std::string_view endLabel) { m_endLabel = endLabel; }

 private:
  const std::string m_name;
  std::string m_endLabel;
  ModPortSignalMap m_modportSignalMap;
  ModPortClockingBlockMap m_modportClockingBlockMap;
  ClassNameClassDefinitionMultiMap m_classDefinitions;
  NodeId m_gen_block_id;
  UHDM::udp_defn* m_udpDefn;

  UHDM::VectorOfattribute* attributes_ = nullptr;
  std::vector<UHDM::module_array*>* m_moduleArrays = nullptr;
  std::vector<UHDM::ref_module*>* m_ref_modules = nullptr;
  UHDM::VectorOfprimitive* m_subPrimitives = nullptr;
  UHDM::VectorOfprimitive_array* m_subPrimitiveArrays = nullptr;
  UHDM::VectorOfgen_scope_array* m_subGenScopeArrays = nullptr;
  std::vector<UHDM::gen_stmt*>* m_genStmts = nullptr;
};

class ModuleDefinitionFactory {
 public:
  ModuleDefinition* newModuleDefinition(const FileContent* fileContent,
                                        NodeId nodeId, std::string_view name);
};

};  // namespace SURELOG

#endif /* SURELOG_MODULEDEFINITION_H */
