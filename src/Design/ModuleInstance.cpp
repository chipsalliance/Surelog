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
 * File:   ModuleInstance.cpp
 * Author: alain
 *
 * Created on October 16, 2017, 10:48 PM
 */
#include <string>
#include <iostream>
#include "SourceCompile/SymbolTable.h"
#include "Library/Library.h"
#include "Design/FileContent.h"

#include "Design/ModuleInstance.h"
using namespace SURELOG;

ModuleInstance::ModuleInstance(DesignComponent* moduleDefinition,
                               FileContent* fileContent, NodeId nodeId,
                               ModuleInstance* parent, std::string instName,
                               std::string modName)
    : ValuedComponentI(parent, moduleDefinition),
      m_definition(moduleDefinition),
      m_children(NULL),
      m_nbChildren(0),
      m_fileContent(fileContent),
      m_nodeId(nodeId),
      m_parent(parent),
      m_instName(instName),
      m_netlist(nullptr) {
  if (m_definition == NULL) {
    m_instName = modName + "&" + instName;
  }
}

ModuleInstance::~ModuleInstance() {}

void ModuleInstance::addSubInstances(ModuleInstance** subInstances,
                                     unsigned int nbSubInstances) {
  m_children = subInstances;
  m_nbChildren = nbSubInstances;
}

ModuleInstance* ModuleInstanceFactory::newModuleInstance(
    DesignComponent* moduleDefinition, FileContent* fileContent, NodeId nodeId,
    ModuleInstance* parent, std::string instName, std::string modName) {
  return new ModuleInstance(moduleDefinition, fileContent, nodeId, parent,
                            instName, modName);
}

VObjectType ModuleInstance::getType() { return m_fileContent->Type(m_nodeId); }

VObjectType ModuleInstance::getModuleType() {
  VObjectType type = (VObjectType)0;
  if (m_definition) {
    type = m_definition->getType();
  }
  return type;
}

unsigned int ModuleInstance::getLineNb() {
  return m_fileContent->Line(m_nodeId);
}

SymbolId ModuleInstance::getFullPathId(SymbolTable* symbols) {
  return symbols->registerSymbol(getFullPathName());
}

SymbolId ModuleInstance::getInstanceId(SymbolTable* symbols) {
  return symbols->registerSymbol(getInstanceName());
}
SymbolId ModuleInstance::getModuleNameId(SymbolTable* symbols) {
  return symbols->registerSymbol(getModuleName());
}

std::string ModuleInstance::getFullPathName() {
  std::string path;
  ModuleInstance* tmp = this;
  std::vector<std::string> nibbles;
  while (tmp) {
    nibbles.push_back(tmp->getInstanceName());
    tmp = tmp->getParent();
  }
  for (int i = nibbles.size() - 1; i >= 0; i--) {
    path += nibbles[i];
    if (i > 0) {
      path += ".";
    }
  }
  return path;
}

unsigned int ModuleInstance::getDepth() {
  unsigned int depth = 0;
  ModuleInstance* tmp = this;
  while (tmp) {
    tmp = tmp->getParent();
    depth++;
  }
  return depth;
}

std::string ModuleInstance::getInstanceName() {
  if (m_definition == NULL) {
    std::string name =
        m_instName.substr(m_instName.find("&", 0, 1) + 1, m_instName.size());
    return name;
  } else {
    return m_instName;
  }
}

std::string ModuleInstance::getModuleName() {
  if (m_definition == NULL) {
    std::string name = m_instName.substr(0, m_instName.find("&", 0, 1));
    return name;
  } else {
    return m_definition->getName();
  }
}

void ModuleInstance::overrideParentChild(ModuleInstance* parent,
                                         ModuleInstance* interm,
                                         ModuleInstance* child) {
  if (parent != this) return;
  child->m_parent = this;
  std::vector<ModuleInstance*> children;

  for (unsigned int i = 0; i < m_nbChildren; i++) {
    if (m_children[i] == interm) {
      for (unsigned int j = 0; j < interm->m_nbChildren; j++) {
        children.push_back(interm->m_children[j]);
      }
    } else {
      children.push_back(m_children[i]);
    }
  }

  ModuleInstance** newChild = new ModuleInstance*[children.size()];
  for (unsigned int i = 0; i < children.size(); i++) {
    newChild[i] = children[i];
  }
  m_nbChildren = children.size();
  delete[] m_children;
  m_children = newChild;
}
