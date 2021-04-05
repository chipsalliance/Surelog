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
 * File:   FileContent.cpp
 * Author: alain
 *
 * Created on June 8, 2017, 8:22 PM
 */

#include "SourceCompile/SymbolTable.h"
#include "Design/TimeInfo.h"
#include "Design/DesignElement.h"
#include "Library/Library.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Design/FileContent.h"
#include <queue>
#include <iostream>
#include <stack>
#include <string.h>

using namespace SURELOG;

FileContent::~FileContent() {}

NodeId FileContent::getRootNode() {
  if (m_objects.size() == 0) {
    return 0;
  }
  return m_objects[0].m_sibling;
}

SymbolId FileContent::getFileId(NodeId id) const {
  return m_objects[id].m_fileId;
}

SymbolId* FileContent::getMutableFileId(NodeId id) {
  return &m_objects[id].m_fileId;
}

const std::string& FileContent::getFileName(NodeId id) const {
  SymbolId fileId = m_objects[id].m_fileId;
  return m_symbolTable->getSymbol(fileId);
}

std::string FileContent::printObjects() const {
  std::string text;
  NodeId index = 0;

  if (m_library) text += "LIB:  " + m_library->getName() + "\n";
  std::string fileName = m_symbolTable->getSymbol(m_fileId);
  if (strstr(fileName.c_str(), "/bin/sv/builtin.sv"))
    return "";
  text += "FILE: " + fileName + "\n";

  for (auto object : m_objects) {
    text += object.print(m_symbolTable, index, GetDefinitionFile(index));
    text += "\n";
    index++;
  }
  return text;
}

std::string FileContent::printObject(NodeId nodeId) const {
  return m_objects[nodeId].print(m_symbolTable, nodeId, GetDefinitionFile(nodeId));
}

unsigned int FileContent::getSize() const { return m_objects.size(); }

std::string FileContent::printSubTree(NodeId uniqueId) {
  std::string text;
  for (auto s : collectSubTree(uniqueId)) {
    text += s + "\n";
  }
  return text;
}

void FileContent::insertObjectLookup(std::string name, NodeId id,
                                     ErrorContainer* errors) {
  NameIdMap::iterator itr = m_objectLookup.find(name);
  if (itr == m_objectLookup.end()) {
    m_objectLookup.insert(std::make_pair(name, id));
  } else {
    Location loc(errors->getSymbolTable()->registerSymbol(getFileName(id)),
                 Line(id), 0, errors->getSymbolTable()->registerSymbol(name));
    Location loc2(
        errors->getSymbolTable()->registerSymbol(getFileName((*itr).second)),
        Line((*itr).second), 0);
    Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_DESIGN_UNIT, loc, loc2);
    errors->addError(err);
  }
}

const ModuleDefinition* FileContent::getModuleDefinition(
    const std::string& moduleName) const {
  ModuleNameModuleDefinitionMap::const_iterator itr =
      m_moduleDefinitions.find(moduleName);
  if (itr != m_moduleDefinitions.end()) {
    return (*itr).second;
  }
  return NULL;
}

DesignComponent* FileContent::getComponentDefinition(
    const std::string& componentName) const {
  DesignComponent* comp = (DesignComponent*)getModuleDefinition(componentName);
  if (comp) return comp;
  comp = (DesignComponent*)getProgram(componentName);
  if (comp) return comp;
  comp = (DesignComponent*)getClassDefinition(componentName);
  if (comp) return comp;
  return NULL;
}

Package* FileContent::getPackage(const std::string& name) {
  PackageNamePackageDefinitionMultiMap::iterator itr =
      m_packageDefinitions.find(name);
  if (itr == m_packageDefinitions.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

const Program* FileContent::getProgram(const std::string& name) const {
  ProgramNameProgramDefinitionMap::const_iterator itr =
      m_programDefinitions.find(name);
  if (itr == m_programDefinitions.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

const ClassDefinition* FileContent::getClassDefinition(const std::string& name) const {
  ClassNameClassDefinitionMultiMap::const_iterator itr =
      m_classDefinitions.find(name);
  if (itr == m_classDefinitions.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

std::vector<std::string> FileContent::collectSubTree(NodeId index) {
  std::vector<std::string> text;

  text.push_back(
      m_objects[index].print(m_symbolTable, index, GetDefinitionFile(index)));

  if (m_objects[index].m_child) {
    for (auto s : collectSubTree(m_objects[index].m_child)) {
      text.push_back("    " + s);
    }
  }

  if (m_objects[index].m_sibling) {
    for (auto s : collectSubTree(m_objects[index].m_sibling)) {
      text.push_back(s);
    }
  }

  return text;
}

void FileContent::SetDefinitionFile(NodeId index, SymbolId def) {
  m_definitionFiles.insert(std::make_pair(index, def));
}

SymbolId FileContent::GetDefinitionFile(NodeId index) const {
  auto itr = m_definitionFiles.find(index);
  if (itr != m_definitionFiles.end()) return (*itr).second;
  return 0;
}

VObject FileContent::Object(NodeId index) const { return m_objects[index]; }
VObject* FileContent::MutableObject(NodeId index) {
  return &m_objects[index];
}

NodeId FileContent::UniqueId(NodeId index) { return index; }

SymbolId FileContent::Name(NodeId index) const {
  return m_objects[index].m_name;
}

NodeId FileContent::Child(NodeId index) const {
  return m_objects[index].m_child;
}

NodeId FileContent::Sibling(NodeId index) const {
  return m_objects[index].m_sibling;
}

NodeId FileContent::Definition(NodeId index) const {
  return m_objects[index].m_definition;
}

NodeId FileContent::Parent(NodeId index) const {
  return m_objects[index].m_parent;
}

VObjectType FileContent::Type(NodeId index) const {
  return (VObjectType)m_objects[index].m_type;
}

unsigned int FileContent::Line(NodeId index) const {
  if (index >= m_objects.size()) {
    Location loc(this->m_fileId);
    Error err (ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cout << "\nINTERNAL OUT OF BOUND ERROR\n\n";  
    return m_objects[0].m_line;
  }
  return m_objects[index].m_line;
}

unsigned short FileContent::Column(NodeId index) const {
  if (index >= m_objects.size()) {
    Location loc(this->m_fileId);
    Error err (ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cout << "\nINTERNAL OUT OF BOUND ERROR\n\n";  
    return m_objects[0].m_column;
  }
  return m_objects[index].m_column;
}

unsigned int FileContent::EndLine(NodeId index) const {
  if (index >= m_objects.size()) {
    Location loc(this->m_fileId);
    Error err (ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cout << "\nINTERNAL OUT OF BOUND ERROR\n\n";  
    return m_objects[0].m_endLine;
  }
  return m_objects[index].m_endLine;
}

unsigned short FileContent::EndColumn(NodeId index) const {
  if (index >= m_objects.size()) {
    Location loc(this->m_fileId);
    Error err (ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cout << "\nINTERNAL OUT OF BOUND ERROR\n\n";  
    return m_objects[0].m_endColumn;
  }
  return m_objects[index].m_endColumn;
}

NodeId FileContent::sl_get(NodeId parent, VObjectType type) {
  if (!m_objects.size()) return 0;
  if (parent > m_objects.size() - 1) return 0;
  VObject current = Object(parent);
  if (current.m_type == type) return parent;
  NodeId id = current.m_child;
  while (id) {
    current = Object(id);
    if (current.m_type == type) {
      return id;
    }
    id = current.m_sibling;
  }
  return InvalidNodeId;
}

NodeId FileContent::sl_parent(NodeId parent, std::vector<VObjectType> types,
                              VObjectType& actualType) {
  if (!m_objects.size()) return 0;
  if (parent > m_objects.size() - 1) return 0;
  VObject current = Object(parent);
  for (auto type : types)
    if (current.m_type == type) {
      actualType = type;
      return parent;
    }
  NodeId id = current.m_parent;
  while (id) {
    current = Object(id);
    for (auto type : types)
      if (current.m_type == type) {
        actualType = type;
        return id;
      }
    id = current.m_parent;
  }
  return InvalidNodeId;
}

NodeId FileContent::sl_parent(NodeId parent, VObjectType type) {
  if (!m_objects.size()) return 0;
  if (parent > m_objects.size() - 1) return 0;
  VObject current = Object(parent);
  if (current.m_type == type) return parent;
  NodeId id = current.m_parent;
  while (id) {
    current = Object(id);
    if (current.m_type == type) {
      return id;
    }
    id = current.m_parent;
  }
  return InvalidNodeId;
}

std::vector<NodeId> FileContent::sl_get_all(NodeId parent, VObjectType type) {
  std::vector<NodeId> objects;
  if (!m_objects.size()) return objects;
  if (parent > m_objects.size() - 1) return objects;
  VObject current = Object(parent);
  if (current.m_type == type) objects.push_back(parent);
  NodeId id = current.m_child;
  while (id) {
    current = Object(id);
    if (current.m_type == type) {
      objects.push_back(id);
    }
    id = current.m_sibling;
  }
  return objects;
}

std::vector<NodeId> FileContent::sl_get_all(NodeId parent,
                                            std::vector<VObjectType>& types) {
  std::vector<NodeId> objects;
  if (!m_objects.size()) return objects;
  if (parent > m_objects.size() - 1) return objects;
  VObject current = Object(parent);
  for (auto type : types) {
    if (current.m_type == type) {
      objects.push_back(parent);
      break;
    }
  }

  NodeId id = current.m_child;
  while (id) {
    current = Object(id);
    for (auto type : types) {
      if (current.m_type == type) {
        objects.push_back(id);
        break;
      }
    }
    id = current.m_sibling;
  }
  return objects;
}

NodeId FileContent::sl_collect(NodeId parent, VObjectType type) const {
  if (!m_objects.size()) return 0;
  if (parent > m_objects.size() - 1) return 0;
  VObject current = Object(parent);
  if (current.m_type == type) return parent;
  NodeId id = current.m_child;
  while (id) {
    NodeId idsub = sl_collect(id, type);
    if (idsub != InvalidNodeId) {
      return idsub;
    }
    current = Object(id);
    if (current.m_type == type) {
      return id;
    }
    id = current.m_sibling;
  }
  return InvalidNodeId;
}

std::vector<NodeId> FileContent::sl_collect_all(NodeId parent, VObjectType type,
                                                bool first) const {
  std::vector<NodeId> objects;
  if (!m_objects.size()) return objects;
  if (parent > m_objects.size() - 1) return objects;
  VObject current = Object(parent);
  NodeId id = current.m_child;
  if (!id) id = current.m_sibling;
  if (!id) return objects;
  std::stack<NodeId> stack;
  stack.push(id);
  while (stack.size()) {
    id = stack.top();
    stack.pop();
    current = Object(id);
    if (current.m_type == type) {
      objects.push_back(id);
      if (first) return objects;
    }
    if (current.m_sibling) stack.push(current.m_sibling);
    if (current.m_child) stack.push(current.m_child);
  }
  return objects;
}

std::vector<NodeId> FileContent::sl_collect_all(NodeId parent,
                                                std::vector<VObjectType>& types,
                                                bool first) const {
  std::vector<NodeId> objects;
  if (!m_objects.size()) return objects;
  if (parent > m_objects.size() - 1) return objects;
  VObject current = Object(parent);
  NodeId id = current.m_child;
  if (!id) id = current.m_sibling;
  if (!id) return objects;
  std::stack<NodeId> stack;
  stack.push(id);
  while (stack.size()) {
    id = stack.top();
    stack.pop();
    current = Object(id);
    // std::cout << "COLLECT:" << current.print (m_symbolTable, id,
    // GetDefinitionFile(id)) << std::endl;
    for (auto type : types) {
      if (current.m_type == type) {
        objects.push_back(id);
        if (first) return objects;
        break;
      }
    }
    if (current.m_sibling) stack.push(current.m_sibling);
    if (current.m_child) stack.push(current.m_child);
  }
  return objects;
}

NodeId FileContent::sl_collect(NodeId parent, VObjectType type,
                               VObjectType stopPoint) const {
  NodeId result = InvalidNodeId;
  if (!m_objects.size()) return result;
  if (parent > m_objects.size() - 1) return result;
  VObject current = Object(parent);
  NodeId id = current.m_child;
  if (!id) id = current.m_sibling;
  if (!id) return result;
  std::stack<NodeId> stack;
  stack.push(id);
  while (stack.size()) {
    id = stack.top();
    stack.pop();
    current = Object(id);
    if (current.m_type == type) {
      return id;
    }

    if (current.m_sibling) stack.push(current.m_sibling);

    if (current.m_child) {
      if (stopPoint != current.m_type)
        if (current.m_child) stack.push(current.m_child);
    }
  }
  return result;
}

std::vector<NodeId> FileContent::sl_collect_all(
    NodeId parent, std::vector<VObjectType>& types,
    std::vector<VObjectType>& stopPoints, bool first) const {
  std::vector<NodeId> objects;
  if (!m_objects.size()) return objects;
  if (parent > m_objects.size() - 1) return objects;
  VObject current = Object(parent);
  NodeId id = current.m_child;
  if (!id) id = current.m_sibling;
  if (!id) return objects;
  std::stack<NodeId> stack;
  stack.push(id);
  while (stack.size()) {
    id = stack.top();
    stack.pop();
    current = Object(id);
    // std::cout << "COLLECT:" << current.print (m_symbolTable, id,
    // GetDefinitionFile(id)) << std::endl;
    for (auto type : types) {
      if (current.m_type == type) {
        objects.push_back(id);
        if (first) return objects;
        break;
      }
    }
    if (current.m_sibling) stack.push(current.m_sibling);

    if (current.m_child) {
      if (stopPoints.size()) {
        bool stop = false;
        for (auto t : stopPoints) {
          if (t == current.m_type) {
            stop = true;
            break;
          }
        }
        if (!stop)
          if (current.m_child) stack.push(current.m_child);
      } else {
        if (current.m_child) stack.push(current.m_child);
      }
    }
  }
  return objects;
}

bool FileContent::diffTree(NodeId root, const FileContent* oFc,
                           NodeId oroot, std::string *diff_out) const {
  diff_out->clear();

  VObject current1 = Object(root);
  NodeId id1 = current1.m_child;
  if (!id1) id1 = current1.m_sibling;

  VObject current2 = oFc->Object(oroot);
  NodeId id2 = current2.m_child;
  if (!id2) id2 = current2.m_sibling;

  if ((id1 && (!id2)) || ((!id1) && id2)) return true;

  std::stack<NodeId> stack1;
  std::stack<NodeId> stack2;
  stack1.push(id1);
  stack2.push(id2);
  while (stack1.size()) {
    if (!stack2.size()) return true;
    id1 = stack1.top();
    id2 = stack2.top();
    stack1.pop();
    stack2.pop();
    current1 = Object(id1);
    current2 = oFc->Object(id2);
    if (current1.m_type != current2.m_type) {
      return true;
    }
    std::string symb1;
    std::string symb2;
    if (current1.m_name) symb1 = Name(id1);
    if (current2.m_name) symb2 = oFc->Name(id2);
    if (current1.m_name || current2.m_name)
      if (symb1 != symb2) return true;

    if (current1.m_sibling) stack1.push(current1.m_sibling);
    if (current1.m_child) stack1.push(current1.m_child);
    if (current2.m_sibling) stack2.push(current2.m_sibling);
    if (current2.m_child) stack2.push(current2.m_child);
  }
  if (stack2.size()) return true;
  return false;
}
