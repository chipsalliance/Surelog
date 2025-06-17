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

#include "Surelog/Package/Package.h"

#include <uhdm/Serializer.h>
#include <uhdm/package.h>

#include <cstdint>
#include <string_view>

#include "Surelog/Common/Containers.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Design/DesignComponent.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Testbench/ClassDefinition.h"

namespace SURELOG {

Package::Package(Session* session, std::string_view name, Library* library,
                 const FileContent* fC, NodeId nodeId,
                 uhdm::Serializer& serializer)
    : DesignComponent(session, fC, nullptr),
      m_name(name),
      m_library(library),
      m_exprBuilder(session) {
  addFileContent(fC, nodeId);
  m_unElabPackage = this;
  // if (!name.empty()) {  // avoid loop
  //   m_unElabPackage = new Package("", library, fC, nodeId);
  //   m_unElabPackage->m_name = name;
  // }

  uhdm::Package* const instance = serializer.make<uhdm::Package>();
  if (!name.empty()) instance->setName(name);
  if (nodeId && (fC != nullptr))
    fC->populateCoreMembers(fC->sl_collect(nodeId, VObjectType::paPACKAGE),
                            nodeId, instance);
  setUhdmModel(instance);
}

uint32_t Package::getSize() const {
  NodeId end = this->m_nodeIds[0];
  NodeId begin = m_fileContents[0]->Child(end);
  uint32_t size = (RawNodeId)(end - begin);
  return size;
}

ClassDefinition* Package::getClassDefinition(std::string_view name) {
  ClassNameClassDefinitionMultiMap::iterator itr =
      m_classDefinitions.find(name);
  if (itr == m_classDefinitions.end()) {
    return nullptr;
  } else {
    return itr->second;
  }
}

const ClassDefinition* Package::getClassDefinition(
    std::string_view name) const {
  ClassNameClassDefinitionMultiMap::const_iterator itr =
      m_classDefinitions.find(name);
  if (itr == m_classDefinitions.end()) {
    return nullptr;
  } else {
    return itr->second;
  }
}

const DataType* Package::getDataType(Design* design,
                                     std::string_view name) const {
  if (const DataType* const dt = DesignComponent::getDataType(design, name)) {
    return dt;
  } else if (const DataType* const dt = getClassDefinition(name)) {
    return dt;
  }
  return nullptr;
}

void Package::append(Package* package) {
  DesignComponent::append(package);
  for (auto& type : package->m_dataTypes)
    insertDataType(type.first, type.second);
  for (auto& param : package->getMappedValues())
    setValue(param.first, param.second.first, m_exprBuilder,
             param.second.second);
  for (auto& classDef : package->m_classDefinitions) {
    addClassDefinition(classDef.first, classDef.second);
    classDef.second->setContainer(this);
  }
}

}  // namespace SURELOG
