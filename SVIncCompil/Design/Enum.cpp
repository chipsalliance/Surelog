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
 * File:   Enum.cpp
 * Author: alain
 * 
 * Created on May 19, 2019, 11:55 AM
 */
#include "../SourceCompile/SymbolTable.h"
#include "../Design/FileContent.h"
#include "Enum.h"
using namespace SURELOG;

Enum::Enum(std::string name, FileContent* fC, NodeId nodeId, VObjectType baseType) : DataType(fC, nodeId, name, fC->Type(nodeId)), m_baseType(baseType) {}

Value* Enum::getValue(std::string& name) {
  NameValueMap::iterator itr = m_values.find(name);
  if (itr == m_values.end ())
    {
      return NULL;
    }
  else 
    {
      return (*itr).second;
    }
}

Enum::~Enum () { }


