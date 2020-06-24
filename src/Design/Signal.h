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

#include "Design/FileContent.h"

namespace SURELOG {
class ModPort;
class ModuleDefinition;

class Signal {
 public:
  Signal(FileContent* fileContent, NodeId node, VObjectType type, VObjectType direction, NodeId range);
  Signal(FileContent* fileContent, NodeId node, VObjectType type, NodeId range, VObjectType direction, NodeId arrayDimension);
  Signal(FileContent* fileContent, NodeId node, VObjectType type, VObjectType direction, NodeId typeSpecId, NodeId range);       
  Signal(FileContent* fileContent, NodeId node, NodeId interfaceTypeName, VObjectType subnettype, NodeId range);
  virtual ~Signal();

  VObjectType getType() { return m_type; }
  VObjectType getDirection() { return m_direction; }
  FileContent* getFileContent() { return m_fileContent; }
  NodeId getNodeId() { return m_nodeId; }
  std::string getName() { return m_fileContent->SymName(m_nodeId); }

  std::string getInterfaceTypeName() {
    std::string type_name = m_fileContent->SymName(m_interfaceTypeNameId);
    NodeId constant_select = m_fileContent->Sibling(m_interfaceTypeNameId);
    if (constant_select) {
      if (m_fileContent->Type(constant_select) == slStringConst) {
        type_name += "." + m_fileContent->SymName(constant_select);
      } else {
        NodeId selector = m_fileContent->Child(constant_select);
        if (m_fileContent->Type(selector) == slStringConst)
          type_name += "." + m_fileContent->SymName(selector);
      }
    }
    return type_name;
  }
 
  ModuleDefinition* getInterfaceDef() { return m_interfaceDef; }
  void setInterfaceDef(ModuleDefinition* interfaceDef) {
    m_interfaceDef = interfaceDef;
  }
  ModPort* getModPort() { return m_modPort; }
  void setModPort(ModPort* modport) { m_modPort = modport; }
  void setDirection(VObjectType direction) { m_direction = direction; }
  void setType(VObjectType type) { m_type = type; }
  void setDataType(DataType* dtype) { m_dataType = dtype; } 
  bool isInterface() { return (m_interfaceTypeNameId != 0); }
  void setLowConn(Signal* sig) { m_lowConn = sig; }
  Signal* getLowConn() { return m_lowConn; }
  NodeId getRange() { return m_range; }
  NodeId getArrayDimension() { return m_arrayDimension; }
  NodeId getModPortId() { return m_fileContent->Sibling(m_interfaceTypeNameId);}
  NodeId getInterfaceTypeNameId() { return m_interfaceTypeNameId; }
  NodeId getTypeSpecId() { return m_typeSpecId; }
  DataType* getDataType() { return m_dataType; }
 private:
  FileContent* m_fileContent;
  NodeId m_nodeId;
  VObjectType m_type;
  VObjectType m_direction;
  ModuleDefinition* m_interfaceDef;
  ModPort*          m_modPort;
  DataType*         m_dataType;
  Signal*           m_lowConn; // for ports
  NodeId m_interfaceTypeNameId;
  NodeId m_range;
  NodeId m_typeSpecId;
  NodeId m_arrayDimension;
};

}  // namespace SURELOG

#endif /* SIGNAL_H */
