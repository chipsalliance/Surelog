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
#include "DesignComponent.h"
#include "ValuedComponentI.h"
#include "Signal.h"
#include "ClockingBlock.h"
#include "DataType.h"
#include "../Common/ClockingBlockHolder.h"

namespace SURELOG {
class CompileModule;

class ModuleDefinition : public DesignComponent, public ClockingBlockHolder {
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

  typedef std::map<SymbolId, ClockingBlock> ClockingBlockMap;
  typedef std::map<SymbolId, std::vector<Signal>> ModPortSignalMap;
  typedef std::map<SymbolId, std::vector<ClockingBlock>>
      ModPortClockingBlockMap;

  ModPortSignalMap& getModPortSignalMap() { return m_modportSignalMap; }
  ModPortClockingBlockMap& getModPortClockingBlockMap() {
    return m_modportClockingBlockMap;
  }
  void insertModPort(SymbolId modport, Signal& signal);
  void insertModPort(SymbolId modport, ClockingBlock& block);
  Signal* getModPortSignal(SymbolId modport, NodeId port);
  ClockingBlock* getModPortClockingBlock(SymbolId modport, NodeId port);

  ClassNameClassDefinitionMultiMap& getClassDefinitions() {
    return m_classDefinitions;
  }
  void addClassDefinition(std::string className, ClassDefinition* classDef) {
    m_classDefinitions.insert(std::make_pair(className, classDef));
  }
  ClassDefinition* getClassDefinition(const std::string& name);

  std::vector<Signal>& getPorts() { return m_ports; }
  std::vector<Signal>& getSignals() { return m_signals; }

 private:
  std::string m_name;
  std::vector<Signal> m_ports;
  std::vector<Signal> m_signals;
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
