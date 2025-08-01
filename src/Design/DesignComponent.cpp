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

#include "Surelog/Design/DesignComponent.h"

/*
 * File:   DesignComponent.cpp
 * Author: alain
 *
 * Created on March 25, 2018, 10:27 PM
 */

#include <string_view>
#include <utility>
#include <vector>

#include "Surelog/Common/NodeId.h"
#include "Surelog/Design/FileCNodeId.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/Function.h"
#include "Surelog/Design/LetStmt.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/Design/Task.h"
#include "Surelog/Design/ValuedComponentI.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/TypeDef.h"
#include "Surelog/Testbench/Variable.h"

namespace SURELOG {
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

const std::vector<FileCNodeId>& DesignComponent::getObjects(
    VObjectType type) const {
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
    m_objects.emplace(type, tmp);
  } else {
    (*itr).second.push_back(object);
  }
}

void DesignComponent::addNamedObject(std::string_view name, FileCNodeId object,
                                     DesignComponent* def) {
  m_namedObjects.emplace(name, std::make_pair(object, def));
}

const std::pair<FileCNodeId, DesignComponent*>* DesignComponent::getNamedObject(
    std::string_view name) const {
  auto itr = m_namedObjects.find(name);
  if (itr == m_namedObjects.end()) {
    return nullptr;
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
  for (const auto& dtype : comp->m_dataTypes)
    insertDataType(dtype.first, dtype.second);
}

void DesignComponent::insertDataType(std::string_view dataTypeName,
                                     DataType* dataType) {
  m_dataTypes.emplace(dataTypeName, dataType);
}

const DataType* DesignComponent::getDataType(std::string_view name) const {
  DataTypeMap::const_iterator itr = m_dataTypes.find(name);
  if (itr == m_dataTypes.end()) {
    const DesignComponent* parent = (const DesignComponent*)getParentScope();
    if (parent) {
      return parent->getDataType(name);
    } else
      return nullptr;
  } else {
    return (*itr).second;
  }
}

void DesignComponent::insertUsedDataType(std::string_view dataTypeName,
                                         DataType* dataType) {
  m_usedDataTypes.emplace(dataTypeName, dataType);
}

DataType* DesignComponent::getUsedDataType(std::string_view name) {
  DataTypeMap::iterator itr = m_usedDataTypes.find(name);
  if (itr == m_usedDataTypes.end()) {
    return nullptr;
  } else {
    return (*itr).second;
  }
}

const TypeDef* DesignComponent::getTypeDef(std::string_view name) const {
  TypeDefMap::const_iterator itr = m_typedefs.find(name);
  if (itr == m_typedefs.end()) {
    const DesignComponent* parent =
        valuedcomponenti_cast<const DesignComponent*>(getParentScope());
    if (parent) {
      return parent->getTypeDef(name);
    } else
      return nullptr;
  } else {
    return (*itr).second;
  }
}

void DesignComponent::insertTypeDef(TypeDef* p) {
  m_typedefs.emplace(p->getName(), p);
}

Function* DesignComponent::getFunction(std::string_view name) const {
  FunctionMap::const_iterator itr = m_functions.find(name);
  if (itr == m_functions.end()) {
    const DesignComponent* parent =
        valuedcomponenti_cast<const DesignComponent*>(getParentScope());
    if (parent) {
      return parent->getFunction(name);
    } else
      return nullptr;
  } else {
    return (*itr).second;
  }
}

void DesignComponent::insertFunction(Function* p) {
  m_functions.emplace(p->getName(), p);
}

Task* DesignComponent::getTask(std::string_view name) const {
  TaskMap::const_iterator itr = m_tasks.find(name);
  if (itr == m_tasks.end()) {
    const DesignComponent* parent =
        valuedcomponenti_cast<const DesignComponent*>(getParentScope());
    if (parent) {
      return parent->getTask(name);
    } else
      return nullptr;
  } else {
    return (*itr).second;
  }
}

void DesignComponent::insertTask(Task* p) { m_tasks.emplace(p->getName(), p); }

void DesignComponent::addVariable(Variable* var) {
  m_variables.emplace(var->getName(), var);
}

Variable* DesignComponent::getVariable(std::string_view name) {
  VariableMap::const_iterator itr = m_variables.find(name);
  if (itr == m_variables.end()) {
    return nullptr;
  } else {
    return (*itr).second;
  }
}

Parameter* DesignComponent::getParameter(std::string_view name) const {
  ParameterMap::const_iterator itr = m_parameterMap.find(name);
  if (itr == m_parameterMap.end()) {
    return nullptr;
  } else {
    return (*itr).second;
  }
}

void DesignComponent::insertParameter(Parameter* p) {
  m_parameterMap.emplace(p->getName(), p);
  m_orderedParameters.push_back(p);
}

void DesignComponent::insertLetStmt(std::string_view name, LetStmt* decl) {
  m_letDecls.insert(std::pair(name, decl));
}
LetStmt* DesignComponent::getLetStmt(std::string_view name) {
  auto itr = m_letDecls.find(name);
  if (itr == m_letDecls.end()) {
    return nullptr;
  } else {
    return (*itr).second;
  }
}

}  // namespace SURELOG
