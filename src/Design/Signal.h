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

class Signal final {
 public:
  Signal(const FileContent* fileContent, NodeId node, VObjectType type,
         VObjectType direction, NodeId packedDimension, bool is_signed);
  Signal(const FileContent* fileContent, NodeId node, VObjectType type,
         NodeId packedDimension, VObjectType direction,
         NodeId unpackedDimension, bool is_signed);
  Signal(const FileContent* fileContent, NodeId node, VObjectType type,
         NodeId packedDimension, VObjectType direction, NodeId typeSpecId,
         NodeId unpackedDimension, bool is_signed);
  Signal(const FileContent* fileContent, NodeId node, NodeId interfaceTypeName,
         VObjectType subnettype, NodeId unpackedDimension, bool is_signed);

  VObjectType getType() const { return m_type; }
  VObjectType getDirection() const { return m_direction; }
  const FileContent* getFileContent() const { return m_fileContent; }
  NodeId getNodeId() const { return m_nodeId; }
  std::string getName() const { return m_fileContent->SymName(m_nodeId); }
  std::string getInterfaceTypeName() const;

  ModuleDefinition* getInterfaceDef() { return m_interfaceDef; }
  void setInterfaceDef(ModuleDefinition* interfaceDef) {
    m_interfaceDef = interfaceDef;
  }
  ModPort* getModPort() { return m_modPort; }
  void setModPort(ModPort* modport) { m_modPort = modport; }
  void setDirection(VObjectType direction) { m_direction = direction; }
  void setType(VObjectType type) { m_type = type; }
  void setDataType(const DataType* dtype) { m_dataType = dtype; }
  void setPackedDimension(NodeId id) { m_packedDimension = id; }
  void setUnpackedDimension(NodeId id) { m_unpackedDimension = id; }
  void setTypespecId(NodeId id) { m_typeSpecId = id; }
  bool isInterface() { return (m_interfaceTypeNameId != 0); }
  void setLowConn(Signal* sig) { m_lowConn = sig; }
  void setConst() { m_const = true; }
  void setVar() { m_var = true; }
  void setLocal() { m_local = true; }
  void setStatic() { m_static = true; }
  void setProtected() { m_protected = true; }
  void setRand() { m_rand = true; }
  void setRandc() { m_randc = true; }
  void setSigned() { m_signed = true; }
  bool isConst() { return m_const; }
  bool isVar() { return m_var; }
  bool isSigned() { return m_signed; }
  bool isLocal() { return m_local; }
  bool isStatic() { return m_static; }
  bool isProtected() { return m_protected; }
  bool isRand() { return m_rand; }
  bool isRandc() { return m_randc; }
  void setDelay(NodeId id) { m_delay = id; }
  void setDriveStrength(NodeId id) { m_drive_strength = id; }
  void setDefaultValue(NodeId id) { m_default_value = id; }

  Signal* getLowConn() { return m_lowConn; }
  NodeId getPackedDimension() const { return m_packedDimension; }
  NodeId getUnpackedDimension() const { return m_unpackedDimension; }
  NodeId getModPortId() const {
    return m_fileContent->Sibling(m_interfaceTypeNameId);
  }
  NodeId getInterfaceTypeNameId() const { return m_interfaceTypeNameId; }
  NodeId getTypeSpecId() const { return m_typeSpecId; }
  NodeId getDelay() const { return m_delay; }
  NodeId getDriveStrength() const { return m_drive_strength; }
  NodeId getDefaultValue() const { return m_default_value; }
  const DataType* getDataType() { return m_dataType; }

 private:
  const FileContent* m_fileContent = nullptr;
  NodeId m_nodeId = 0;
  VObjectType m_type = VObjectType::slNoType;
  VObjectType m_direction = VObjectType::slNoType;
  ModuleDefinition* m_interfaceDef = nullptr;
  ModPort* m_modPort = nullptr;
  const DataType* m_dataType = nullptr;
  Signal* m_lowConn = nullptr;  // for ports
  NodeId m_interfaceTypeNameId = 0;
  NodeId m_packedDimension = 0;
  NodeId m_typeSpecId = 0;
  NodeId m_unpackedDimension = 0;
  NodeId m_delay = 0;
  NodeId m_drive_strength = 0;
  NodeId m_default_value = 0;
  bool m_const = false;
  bool m_var = false;
  bool m_signed = false;
  bool m_local = false;
  bool m_static = false;
  bool m_protected = false;
  bool m_rand = false;
  bool m_randc = false;
};

}  // namespace SURELOG

#endif /* SIGNAL_H */
