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
 * File:   Signal.h
 * Author: alain
 *
 * Created on May 6, 2018, 5:32 PM
 */

#ifndef SIGNAL_H
#define SIGNAL_H

#include "FileContent.h"

namespace SURELOG {

class Signal {
 public:
  Signal(FileContent* fileContent, NodeId node, VObjectType type,
         VObjectType direction);
  Signal(FileContent* fileContent, NodeId interfaceDef, NodeId interfaceName);
  virtual ~Signal();

  VObjectType getType() { return m_type; }
  VObjectType getDirection() { return m_direction; }
  FileContent* getFileContent() { return m_fileContent; }
  NodeId getNodeId() { return m_nodeId; }
  std::string getName() { return m_fileContent->SymName(m_nodeId); }

  std::string getInterfaceTypeName() {
    return m_fileContent->SymName(m_nodeId);
  }
  std::string getInterfaceName() {
    return m_fileContent->SymName(m_interfaceNameId);
  }
  ModuleDefinition* getInterfaceDef() { return m_interfaceDef; }
  void setInterfaceDef(ModuleDefinition* interfaceDef) {
    m_interfaceDef = interfaceDef;
  }
  void setDirection(VObjectType direction) { m_direction = direction; }
  void setType(VObjectType type) { m_type = type; }
  bool isInterface() { return (m_interfaceNameId != 0); }

 private:
  FileContent* m_fileContent;
  NodeId m_nodeId;
  VObjectType m_type;
  VObjectType m_direction;
  ModuleDefinition* m_interfaceDef;
  NodeId m_interfaceNameId;
};

}  // namespace SURELOG

#endif /* SIGNAL_H */
