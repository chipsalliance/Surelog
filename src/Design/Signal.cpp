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
 * File:   Signal.cpp
 * Author: alain
 *
 * Created on May 6, 2018, 5:32 PM
 */
#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"
#include "Design/Signal.h"

using namespace SURELOG;

Signal::Signal(const FileContent* fileContent, NodeId nodeId, VObjectType type,
               VObjectType direction, NodeId packedDimension, bool is_signed)
    : m_fileContent(fileContent),
      m_nodeId(nodeId),
      m_type(type),
      m_direction(direction),
      m_interfaceDef(NULL),
      m_modPort(NULL),
      m_dataType(NULL),
      m_lowConn(NULL),
      m_interfaceTypeNameId(0),
      m_packedDimension(packedDimension),
      m_typeSpecId(0),
      m_unpackedDimension(0),
      m_const(false),
      m_var(false),
      m_signed(is_signed) {}

Signal::Signal(const FileContent* fileContent, NodeId nodeId,
               NodeId interfaceTypeNameId, VObjectType subnettype, NodeId unpackedDimension, bool is_signed)
    : m_fileContent(fileContent),
      m_nodeId(nodeId),
      m_type(subnettype),
      m_direction(VObjectType::slNoType),
      m_interfaceDef(NULL),
      m_modPort(NULL),
      m_dataType(NULL),
      m_lowConn(NULL),
      m_interfaceTypeNameId(interfaceTypeNameId),
      m_packedDimension(0),
      m_typeSpecId(0),
      m_unpackedDimension(unpackedDimension),
      m_const(false),
      m_var(false),
      m_signed(is_signed) {}

Signal::Signal(const FileContent* fileContent, NodeId nodeId, VObjectType type,
         NodeId packedDimension, VObjectType direction, NodeId typeSpecId, NodeId unpackedDimension, bool is_signed)
    : m_fileContent(fileContent),
      m_nodeId(nodeId),
      m_type(type),
      m_direction(direction),
      m_interfaceDef(NULL),
      m_modPort(NULL),
      m_dataType(NULL),
      m_lowConn(NULL),
      m_interfaceTypeNameId(0),
      m_packedDimension(packedDimension),
      m_typeSpecId(typeSpecId),
      m_unpackedDimension(unpackedDimension),
      m_const(false),
      m_var(false),
      m_signed(is_signed) {}

Signal::Signal(const FileContent* fileContent, NodeId nodeId, VObjectType type, 
               NodeId packedDimension, VObjectType direction, NodeId unpackedDimension, bool is_signed)
    : m_fileContent(fileContent),
      m_nodeId(nodeId),
      m_type(type),
      m_direction(direction),
      m_interfaceDef(NULL),
      m_modPort(NULL),
      m_dataType(NULL),
      m_lowConn(NULL),
      m_interfaceTypeNameId(0),
      m_packedDimension(packedDimension),
      m_typeSpecId(0),
      m_unpackedDimension(unpackedDimension),
      m_const(false),
      m_var(false), 
      m_signed(is_signed) {}

  std::string Signal::getInterfaceTypeName() const {
    std::string type_name;
    if (m_fileContent->Type(m_interfaceTypeNameId) == slClass_scope) {
      NodeId Class_type = m_fileContent->Child(m_interfaceTypeNameId);
      NodeId Pack_name =  m_fileContent->Child(Class_type);
      type_name = m_fileContent->SymName(Pack_name) + "::";
      NodeId Struct_name = m_fileContent->Sibling(m_interfaceTypeNameId);
      type_name += m_fileContent->SymName(Struct_name);
    } else {
      type_name = m_fileContent->SymName(m_interfaceTypeNameId);
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
    }
    return type_name;
  }
