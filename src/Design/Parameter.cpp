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
 * File:   Parameter.cpp
 * Author: alain
 *
 * Created on April 15, 2019, 8:03 PM
 */

#include "Design/FileContent.h"
#include "Design/Parameter.h"

using namespace SURELOG;

Parameter::Parameter(const FileContent* fC, NodeId nodeId,
                     const std::string& name,
                     NodeId node_type, bool port_param)
  : DataType(fC, nodeId, name,
             fC ? fC->Type(node_type) : VObjectType::slParameter_declaration,
             true),
    m_ntype(node_type), m_param(nullptr), m_port_param(port_param) {
  m_category = DataType::Category::PARAMETER;
}

Parameter::~Parameter() {}

VObjectType Parameter::getType() const { 
  return getFileContent()->Type(m_ntype);
}
