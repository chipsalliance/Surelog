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
 * File:   DesignComponent.cpp
 * Author: alain
 *
 * Created on March 25, 2018, 10:27 PM
 */
#include <vector>
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/VObjectTypes.h"
#include "Design/FileContent.h"
#include "Design/DesignComponent.h"
#include "Design/Function.h"
#include "Design/Parameter.h"
#include "Testbench/Variable.h"

using namespace SURELOG;

void DesignComponent::addFileContent(const FileContent* fileContent,
                                     NodeId nodeId) {
  bool add = true;
  for (auto f : m_fileContents)
    if (fileContent == f) add = false;
  if (add) {
    m_fileContents.push_back(fileContent);
    m_nodeIds.push_back(nodeId);
  }
}

const std::vector<FileCNodeId>& DesignComponent::getObjects(VObjectType type)
  const {
  auto itr = m_objects.find(type);
  if (itr == m_objects.end()) {
    return m_empty;
  } else {
    return (*itr).second;
  }
}

void DesignComponent::addObject(VObjectType type, FileCNodeId object) {
  auto itr = m_objects.find(type);
  if (itr == m_objects.end()) {
    std::vector<FileCNodeId> tmp;
    tmp.push_back(object);
    m_objects.insert(std::make_pair(type, tmp));
  } else {
    (*itr).second.push_back(object);
  }
}

void DesignComponent::addNamedObject(std::string name, FileCNodeId object,
                                     DesignComponent* def) {
  m_namedObjects.insert(std::make_pair(name, std::make_pair(object, def)));
}

const std::pair<FileCNodeId, DesignComponent*>* DesignComponent::getNamedObject(
    const std::string& name) const {
  auto itr = m_namedObjects.find(name);
  if (itr == m_namedObjects.end()) {
    return NULL;
  } else {
    return &(*itr).second;
  }
}

void DesignComponent::append(DesignComponent* comp) {
  for (auto file : comp->m_fileContents) m_fileContents.push_back(file);
  for (auto nodeId : comp->m_nodeIds) m_nodeIds.push_back(nodeId);
  for (auto& obj : comp->m_objects) {
    for (auto& elem : obj.second) addObject(obj.first, elem);
  }
  for (auto& obj : comp->m_namedObjects) {
    addNamedObject(obj.first, obj.second.first, obj.second.second);
  }
  for (auto dtype : comp->m_dataTypes)
    insertDataType(dtype.first, dtype.second);
}

void DesignComponent::insertDataType(const std::string& dataTypeName,
                                     DataType* dataType) {
  m_dataTypes.insert(std::make_pair(dataTypeName, dataType));
}

const DataType* DesignComponent::getDataType(const std::string& name) const {
  DataTypeMap::const_iterator itr = m_dataTypes.find(name);
  if (itr == m_dataTypes.end()) {
    const DesignComponent* parent = (const DesignComponent*)getParentScope();
    if (parent) {
      return parent->getDataType(name);
    } else
      return NULL;
  } else {
    return (*itr).second;
  }
}

void DesignComponent::insertUsedDataType(const std::string& dataTypeName,
                                         DataType* dataType) {
  m_usedDataTypes.insert(std::make_pair(dataTypeName, dataType));
}

DataType* DesignComponent::getUsedDataType(const std::string& name) {
  DataTypeMap::iterator itr = m_usedDataTypes.find(name);
  if (itr == m_usedDataTypes.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

const TypeDef* DesignComponent::getTypeDef(const std::string& name) const {
  TypeDefMap::const_iterator itr = m_typedefs.find(name);
  if (itr == m_typedefs.end()) {
    const DesignComponent* parent = dynamic_cast<const DesignComponent*>(getParentScope());
    if (parent) {
      return parent->getTypeDef(name);
    } else
      return NULL;
  } else {
    return (*itr).second;
  }
}

void DesignComponent::insertTypeDef(TypeDef* p) {
  m_typedefs.insert(std::make_pair(p->getName(), p));
}

Function* DesignComponent::getFunction(const std::string& name) const {
  FunctionMap::const_iterator itr = m_functions.find(name);
  if (itr == m_functions.end()) {
    const DesignComponent* parent = dynamic_cast<const DesignComponent*>(getParentScope());
    if (parent) {
      return parent->getFunction(name);
    } else
      return NULL;
  } else {
    return (*itr).second;
  }
}

void DesignComponent::insertFunction(Function* p) {
  m_functions.insert(std::make_pair(p->getName(), p));
}

void DesignComponent::addVariable(Variable* var) {
  m_variables.insert(std::make_pair(var->getName(), var));
}

Variable* DesignComponent::getVariable(const std::string& name) {
  VariableMap::const_iterator itr = m_variables.find(name);
  if (itr == m_variables.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

Parameter* DesignComponent::getParameter(const std::string& name) const {
  ParameterMap::const_iterator itr = m_parameterMap.find(name);
  if (itr == m_parameterMap.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

void DesignComponent::insertParameter(Parameter* p) {
  m_parameterMap.insert(std::make_pair(p->getName(), p));
  m_orderedParameters.push_back(p);
}