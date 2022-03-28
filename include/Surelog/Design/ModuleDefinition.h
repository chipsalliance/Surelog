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

  ~ModuleDefinition() override;

  const std::string& getName() const override { return m_name; }
  VObjectType getType() const override;
  bool isInstance() const override;
  unsigned int getSize() const override;

  typedef std::map<std::string, ClockingBlock> ClockingBlockMap;
  typedef std::map<std::string, ModPort> ModPortSignalMap;
  typedef std::map<std::string, std::vector<ClockingBlock>>
      ModPortClockingBlockMap;

  ModPortSignalMap& getModPortSignalMap() { return m_modportSignalMap; }
  ModPortClockingBlockMap& getModPortClockingBlockMap() {
    return m_modportClockingBlockMap;
  }
  void insertModPort(const std::string& modport, const Signal& signal, NodeId nodeId);
  void insertModPort(const std::string& modport, ClockingBlock& block);
  const Signal* getModPortSignal(const std::string& modport, NodeId port) const;
  ModPort* getModPort(const std::string& modport);

  ClockingBlock* getModPortClockingBlock(const std::string& modport,
                                         NodeId port);

  ClassNameClassDefinitionMultiMap& getClassDefinitions() {
    return m_classDefinitions;
  }
  void addClassDefinition(const std::string& className,
                          ClassDefinition* classDef) {
    m_classDefinitions.insert(std::make_pair(className, classDef));
  }
  ClassDefinition* getClassDefinition(const std::string& name);

  void setGenBlockId(NodeId id) { m_gen_block_id = id; }
  NodeId getGenBlockId() const { return m_gen_block_id; }
  UHDM::udp_defn* getUdpDefn() { return m_udpDefn; }

  UHDM::VectorOfattribute* Attributes() const { return attributes_; }

  bool Attributes(UHDM::VectorOfattribute* data) {
    attributes_ = data;
    return true;
  }

 private:
  const std::string m_name;
  ModPortSignalMap m_modportSignalMap;
  ModPortClockingBlockMap m_modportClockingBlockMap;
  ClassNameClassDefinitionMultiMap m_classDefinitions;
  NodeId m_gen_block_id;
  UHDM::udp_defn* m_udpDefn;

  UHDM::VectorOfattribute* attributes_ = nullptr;
};

class ModuleDefinitionFactory {
 public:
  ModuleDefinition* newModuleDefinition(const FileContent* fileContent,
                                        NodeId nodeId, std::string_view name);
};

};  // namespace SURELOG

#endif /* SURELOG_MODULEDEFINITION_H */
