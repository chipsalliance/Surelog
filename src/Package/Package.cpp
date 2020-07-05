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
 * File:   Package.cpp
 * Author: alain
 *
 * Created on March 18, 2018, 7:58 PM
 */
#include "SourceCompile/SymbolTable.h"
#include "Expression/ExprBuilder.h"
#include "Package/Package.h"
#include "Testbench/ClassDefinition.h"

using namespace SURELOG;

Package::~Package() {}

unsigned int Package::getSize() const {
  NodeId end = this->m_nodeIds[0];
  NodeId begin = m_fileContents[0]->Child(end);
  unsigned int size = end - begin;
  return size;
}

ClassDefinition* Package::getClassDefinition(const std::string& name) {
  ClassNameClassDefinitionMultiMap::iterator itr =
      m_classDefinitions.find(name);
  if (itr == m_classDefinitions.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}
void Package::append(Package* package) {
  DesignComponent::append(package);
  for (auto& type : package->m_dataTypes)
    insertDataType(type.first, type.second);
  for (auto& param : package->getMappedValues())
    setValue(param.first, param.second.first, m_exprBuilder, param.second.second);
  for (auto& classDef : package->m_classDefinitions) {
    addClassDefinition(classDef.first, classDef.second);
    classDef.second->setContainer(this);
  }
}
