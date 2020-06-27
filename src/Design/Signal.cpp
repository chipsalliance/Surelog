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

Signal::Signal(FileContent* fileContent, NodeId nodeId, VObjectType type,
               VObjectType direction, NodeId packedDimension)
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
      m_var(false) {}

Signal::Signal(FileContent* fileContent, NodeId nodeId,
               NodeId interfaceTypeNameId, VObjectType subnettype, NodeId unpackedDimension)
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
      m_var(false) {}

Signal::Signal(FileContent* fileContent, NodeId nodeId, VObjectType type,
         VObjectType direction, NodeId typeSpecId, NodeId packedDimension)
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
      m_unpackedDimension(0), 
      m_const(false),
      m_var(false) {}

Signal::Signal(FileContent* fileContent, NodeId nodeId, VObjectType type, NodeId packedDimension, VObjectType direction, NodeId unpackedDimension)
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
      m_var(false) {}
