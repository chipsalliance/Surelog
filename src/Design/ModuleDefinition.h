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

#ifndef MODULEDEFINITION_H
#define MODULEDEFINITION_H
#include <vector>
#include "Design/DesignComponent.h"
#include "Design/ValuedComponentI.h"
#include "Design/Signal.h"
#include "Design/ClockingBlock.h"
#include "Design/DataType.h"
#include "Common/ClockingBlockHolder.h"
#include "Common/PortNetHolder.h"
#include "ModPort.h"

namespace SURELOG {
class CompileModule;

class ModuleDefinition : public DesignComponent, public ClockingBlockHolder,
   public PortNetHolder {
  friend CompileModule;

 public:
  ModuleDefinition(FileContent* fileContent, NodeId nodeId, std::string& name);

  virtual ~ModuleDefinition();

  std::string getName() { return m_name; }
  VObjectType getType() {
    return (m_fileContents.size()) ? m_fileContents[0]->Type(m_nodeIds[0])
                                   : VObjectType::slN_input_gate_instance;
  }
  bool isInstance();
  unsigned int getSize();

  typedef std::map<std::string, ClockingBlock> ClockingBlockMap;
  typedef std::map<std::string, ModPort> ModPortSignalMap;
  typedef std::map<std::string, std::vector<ClockingBlock>>
      ModPortClockingBlockMap;

  ModPortSignalMap& getModPortSignalMap() { return m_modportSignalMap; }
  ModPortClockingBlockMap& getModPortClockingBlockMap() {
    return m_modportClockingBlockMap;
  }
  void insertModPort(const std::string& modport, Signal& signal);
  void insertModPort(const std::string& modport, ClockingBlock& block);
  Signal* getModPortSignal(const std::string& modport, NodeId port);
  ModPort* getModPort(const std::string& modport);
  
  ClockingBlock* getModPortClockingBlock(const std::string& modport, NodeId port);

  ClassNameClassDefinitionMultiMap& getClassDefinitions() {
    return m_classDefinitions;
  }
  void addClassDefinition(std::string className, ClassDefinition* classDef) {
    m_classDefinitions.insert(std::make_pair(className, classDef));
  }
  ClassDefinition* getClassDefinition(const std::string& name);

 private:
  std::string m_name;
  ModPortSignalMap m_modportSignalMap;
  ModPortClockingBlockMap m_modportClockingBlockMap;
  ClassNameClassDefinitionMultiMap m_classDefinitions;
  
};

class ModuleDefinitionFactory {
 public:
  ModuleDefinition* newModuleDefinition(FileContent* fileContent, NodeId nodeId,
                                        std::string name);
};

};  // namespace SURELOG

#endif /* MODULEDEFINITION_H */
