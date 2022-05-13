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

#include <Surelog/Design/FileContent.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/Library/Library.h>
#include <Surelog/SourceCompile/SymbolTable.h>

#include <iostream>
#include <stack>

namespace SURELOG {
FileContent::FileContent(SymbolId fileId, Library* library,
                         SymbolTable* symbolTable, ErrorContainer* errors,
                         FileContent* parent, SymbolId fileChunkId)
    : DesignComponent(nullptr, nullptr),
      m_fileId(fileId),
      m_fileChunkId(fileChunkId),
      m_errors(errors),
      m_library(library),
      m_symbolTable(symbolTable),
      m_parentFile(parent) {
  addObject(BadSymbolId, BadSymbolId, sl_INVALID_, 0, 0, 0, 0, InvalidNodeId,
            InvalidNodeId, InvalidNodeId, InvalidNodeId);
}

const std::string& FileContent::getName() const {
  return m_symbolTable->getSymbol(m_fileId);
}

std::filesystem::path FileContent::getChunkFileName() const {
  return m_symbolTable->getSymbol(m_fileChunkId);
}

const std::string& FileContent::SymName(NodeId index) const {
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return SymbolTable::getBadSymbol();
  }
  return m_symbolTable->getSymbol(Name(index));
}

std::filesystem::path FileContent::getFileName() const {
  return m_symbolTable->getSymbol(m_fileId);
}

NodeId FileContent::getRootNode() const {
  return m_objects.empty() ? InvalidNodeId : m_objects[1].m_sibling;
}

SymbolId FileContent::getFileId(NodeId id) const {
  return m_objects[id].m_fileId;
}

SymbolId* FileContent::getMutableFileId(NodeId id) {
  return &m_objects[id].m_fileId;
}

std::filesystem::path FileContent::getFileName(NodeId id) const {
  SymbolId fileId = m_objects[id].m_fileId;
  return m_symbolTable->getSymbol(fileId);
}

std::string FileContent::printObjects() const {
  std::string text;
  NodeId index(0);

  if (m_library) text += "LIB:  " + m_library->getName() + "\n";
  const std::filesystem::path fileName = m_symbolTable->getSymbol(m_fileId);
  text += "FILE: " + fileName.string() + "\n";
  for (auto& object : m_objects) {
    text +=
        object.print(m_symbolTable, index, GetDefinitionFile(index), m_fileId);
    text += "\n";
    index++;
  }
  return text;
}

std::string FileContent::printObject(NodeId nodeId) const {
  if (!nodeId || (nodeId >= m_objects.size())) return "";
  return m_objects[nodeId].print(m_symbolTable, nodeId,
                                 GetDefinitionFile(nodeId), m_fileId);
}

std::string FileContent::printSubTree(NodeId nodeId) const {
  if (!nodeId || (nodeId >= m_objects.size())) return "";
  std::string text;
  for (const auto& s : collectSubTree(nodeId)) {
    text += s + "\n";
  }
  return text;
}

void FileContent::insertObjectLookup(const std::string& name, NodeId id,
                                     ErrorContainer* errors) {
  NameIdMap::iterator itr = m_objectLookup.find(name);
  if (itr == m_objectLookup.end()) {
    m_objectLookup.insert(std::make_pair(name, id));
  } else {
    Location loc(
        errors->getSymbolTable()->registerSymbol(getFileName(id).string()),
        Line(id), Column(id), errors->getSymbolTable()->registerSymbol(name));
    Location loc2(errors->getSymbolTable()->registerSymbol(
                      getFileName(itr->second).string()),
                  Line(itr->second), Column(itr->second));
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
  return nullptr;
}

DesignComponent* FileContent::getComponentDefinition(
    const std::string& componentName) const {
  DesignComponent* comp = (DesignComponent*)getModuleDefinition(componentName);
  if (comp) return comp;
  comp = (DesignComponent*)getProgram(componentName);
  if (comp) return comp;
  comp = (DesignComponent*)getClassDefinition(componentName);
  if (comp) return comp;
  return nullptr;
}

Package* FileContent::getPackage(const std::string& name) const {
  PackageNamePackageDefinitionMultiMap::const_iterator itr =
      m_packageDefinitions.find(name);
  if (itr == m_packageDefinitions.end()) {
    return nullptr;
  } else {
    return (*itr).second;
  }
}

const Program* FileContent::getProgram(const std::string& name) const {
  ProgramNameProgramDefinitionMap::const_iterator itr =
      m_programDefinitions.find(name);
  if (itr == m_programDefinitions.end()) {
    return nullptr;
  } else {
    return (*itr).second;
  }
}

const ClassDefinition* FileContent::getClassDefinition(
    const std::string& name) const {
  ClassNameClassDefinitionMultiMap::const_iterator itr =
      m_classDefinitions.find(name);
  if (itr == m_classDefinitions.end()) {
    return nullptr;
  } else {
    return (*itr).second;
  }
}

std::vector<std::string> FileContent::collectSubTree(NodeId index) const {
  std::vector<std::string> text;

  text.push_back(m_objects[index].print(m_symbolTable, index,
                                        GetDefinitionFile(index), m_fileId));

  if (m_objects[index].m_child) {
    for (const auto& s : collectSubTree(m_objects[index].m_child)) {
      text.push_back("    " + s);
    }
  }

  if (m_objects[index].m_sibling) {
    for (const auto& s : collectSubTree(m_objects[index].m_sibling)) {
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
  return (itr == m_definitionFiles.end()) ? BadSymbolId : (*itr).second;
}

NodeId FileContent::addObject(SymbolId name, SymbolId fileId, VObjectType type,
                              unsigned int line, unsigned short column,
                              unsigned int endLine, unsigned short endColumn,
                              NodeId parent /* = InvalidNodeId */,
                              NodeId definition /* = InvalidNodeId */,
                              NodeId child /* = InvalidNodeId */,
                              NodeId sibling /* = InvalidNodeId */) {
  RawNodeId index = m_objects.size();
  m_objects.emplace_back(name, fileId, type, line, column, endLine, endColumn,
                         parent, definition, child, sibling);
  return NodeId(index);
}

const VObject& FileContent::Object(NodeId index) const {
  if (!index) return m_objects[0];
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return m_objects[0];
  }
  return m_objects[index];
}

VObject* FileContent::MutableObject(NodeId index) {
  if (!index) return &m_objects[0];
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return &m_objects[0];
  }
  return &m_objects[index];
}

NodeId FileContent::UniqueId(NodeId index) const {
  if (!index) return InvalidNodeId;
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return InvalidNodeId;
  }
  return index;
}

SymbolId FileContent::Name(NodeId index) const {
  if (!index) return BadSymbolId;
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return BadSymbolId;
  }
  return m_objects[index].m_name;
}

NodeId FileContent::Child(NodeId index) const {
  if (!index) return InvalidNodeId;
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return InvalidNodeId;
  }
  return m_objects[index].m_child;
}

NodeId FileContent::Sibling(NodeId index) const {
  if (!index) return InvalidNodeId;
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cout << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return InvalidNodeId;
  }
  return m_objects[index].m_sibling;
}

NodeId FileContent::Definition(NodeId index) const {
  if (!index) return InvalidNodeId;
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return InvalidNodeId;
  }
  return m_objects[index].m_definition;
}

NodeId FileContent::Parent(NodeId index) const {
  if (!index) return InvalidNodeId;
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return InvalidNodeId;
  }
  return m_objects[index].m_parent;
}

VObjectType FileContent::Type(NodeId index) const {
  if (!index) return VObjectType::sl_INVALID_;
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return sl_INVALID_;
  }
  return (VObjectType)m_objects[index].m_type;
}

unsigned int FileContent::Line(NodeId index) const {
  if (!index) return 0;
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return 0;
  }
  return m_objects[index].m_line;
}

unsigned short FileContent::Column(NodeId index) const {
  if (!index) return 0;
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return 0;
  }
  return m_objects[index].m_column;
}

unsigned int FileContent::EndLine(NodeId index) const {
  if (!index) return 0;
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return 0;
  }
  return m_objects[index].m_endLine;
}

unsigned short FileContent::EndColumn(NodeId index) const {
  if (!index) return 0;
  if (index >= m_objects.size()) {
    Location loc(m_fileId);
    Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    m_errors->addError(err);
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return 0;
  }
  return m_objects[index].m_endColumn;
}

NodeId FileContent::sl_get(NodeId parent, VObjectType type) const {
  if (!parent) return InvalidNodeId;
  if (m_objects.empty()) return InvalidNodeId;
  if (parent >= m_objects.size()) return InvalidNodeId;
  const VObject& current = Object(parent);
  if (current.m_type == type) return parent;
  NodeId id = current.m_child;
  while (id) {
    const VObject& current = Object(id);
    if (current.m_type == type) {
      return id;
    }
    id = current.m_sibling;
  }
  return InvalidNodeId;
}

NodeId FileContent::sl_parent(NodeId parent,
                              const VObjectTypeUnorderedSet& types,
                              VObjectType& actualType) const {
  if (!parent) return InvalidNodeId;
  if (m_objects.empty()) return InvalidNodeId;
  if (parent >= m_objects.size()) return InvalidNodeId;
  NodeId id = parent;
  while (id) {
    const VObject& current = Object(id);
    if (types.find(current.m_type) != types.end()) {
      actualType = current.m_type;
      return id;
    }
    id = current.m_parent;
  }
  return InvalidNodeId;
}

NodeId FileContent::sl_parent(NodeId parent, VObjectType type) const {
  if (!parent) return InvalidNodeId;
  if (m_objects.empty()) return InvalidNodeId;
  if (parent >= m_objects.size()) return InvalidNodeId;
  NodeId id = parent;
  while (id) {
    const VObject& current = Object(id);
    if (current.m_type == type) {
      return id;
    }
    id = current.m_parent;
  }
  return InvalidNodeId;
}

std::vector<NodeId> FileContent::sl_get_all(NodeId parent,
                                            VObjectType type) const {
  std::vector<NodeId> objects;
  if (!parent) return objects;
  if (m_objects.empty()) return objects;
  if (parent >= m_objects.size()) return objects;
  const VObject& current = Object(parent);
  if (current.m_type == type) objects.push_back(parent);
  NodeId id = current.m_child;
  while (id) {
    const VObject& current = Object(id);
    if (current.m_type == type) {
      objects.push_back(id);
    }
    id = current.m_sibling;
  }
  return objects;
}

std::vector<NodeId> FileContent::sl_get_all(
    NodeId parent, const VObjectTypeUnorderedSet& types) const {
  std::vector<NodeId> objects;
  if (!parent) return objects;
  if (m_objects.empty()) return objects;
  if (parent >= m_objects.size()) return objects;
  const VObject& current = Object(parent);
  if (types.find(current.m_type) != types.end()) {
    objects.push_back(parent);
  }

  NodeId id = current.m_child;
  while (id) {
    const VObject& current = Object(id);
    if (types.find(current.m_type) != types.end()) {
      objects.push_back(id);
    }
    id = current.m_sibling;
  }
  return objects;
}

NodeId FileContent::sl_collect(NodeId parent, VObjectType type) const {
  if (!parent) return InvalidNodeId;
  if (m_objects.empty()) return InvalidNodeId;
  if (parent >= m_objects.size()) return InvalidNodeId;
  const VObject& current = Object(parent);
  if (current.m_type == type) return parent;
  NodeId id = current.m_child;
  while (id) {
    NodeId idsub = sl_collect(id, type);
    if (idsub) return idsub;

    const VObject& current = Object(id);
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
  if (!parent) return objects;
  if (m_objects.empty()) return objects;
  if (parent >= m_objects.size()) return objects;
  const VObject& current = Object(parent);
  NodeId id = current.m_child;
  if (!id) id = current.m_sibling;
  if (!id) return objects;
  std::stack<NodeId> stack;
  stack.push(id);
  while (!stack.empty()) {
    id = stack.top();
    stack.pop();
    const VObject& current = Object(id);
    if (current.m_type == type) {
      objects.push_back(id);
      if (first) return objects;
    }
    if (current.m_sibling) stack.push(current.m_sibling);
    if (current.m_child) stack.push(current.m_child);
  }
  return objects;
}

std::vector<NodeId> FileContent::sl_collect_all(
    NodeId parent, const VObjectTypeUnorderedSet& types, bool first) const {
  std::vector<NodeId> objects;
  if (!parent) return objects;
  if (m_objects.empty()) return objects;
  if (parent >= m_objects.size()) return objects;
  const VObject& current = Object(parent);
  NodeId id = current.m_child;
  if (!id) id = current.m_sibling;
  if (!id) return objects;
  std::stack<NodeId> stack;
  stack.push(id);
  while (!stack.empty()) {
    id = stack.top();
    stack.pop();
    const VObject& current = Object(id);
    // std::cout << "COLLECT:" << current.print (m_symbolTable, id,
    // GetDefinitionFile(id)) << std::endl;
    if (types.find(current.m_type) != types.end()) {
      objects.push_back(id);
      if (first) return objects;
    }
    if (current.m_sibling) stack.push(current.m_sibling);
    if (current.m_child) stack.push(current.m_child);
  }
  return objects;
}

NodeId FileContent::sl_collect(NodeId parent, VObjectType type,
                               VObjectType stopPoint) const {
  if (!parent) return InvalidNodeId;
  if (m_objects.empty()) return InvalidNodeId;
  if (parent >= m_objects.size()) return InvalidNodeId;
  const VObject& current = Object(parent);
  NodeId id = current.m_child;
  if (!id) id = current.m_sibling;
  if (!id) return InvalidNodeId;
  std::stack<NodeId> stack;
  stack.push(id);
  while (!stack.empty()) {
    id = stack.top();
    stack.pop();
    const VObject& current = Object(id);
    if (current.m_type == type) return id;
    if (current.m_sibling) stack.push(current.m_sibling);
    if (current.m_child && (stopPoint != current.m_type)) {
      stack.push(current.m_child);
    }
  }
  return InvalidNodeId;
}

std::vector<NodeId> FileContent::sl_collect_all(
    NodeId parent, const VObjectTypeUnorderedSet& types,
    const VObjectTypeUnorderedSet& stopPoints, bool first) const {
  std::vector<NodeId> objects;
  if (!parent) return objects;
  if (m_objects.empty()) return objects;
  if (parent >= m_objects.size()) return objects;
  const VObject& current = Object(parent);
  NodeId id = current.m_child;
  if (!id) id = current.m_sibling;
  if (!id) return objects;
  std::stack<NodeId> stack;
  stack.push(id);
  while (!stack.empty()) {
    id = stack.top();
    stack.pop();
    const VObject& current = Object(id);
    // std::cout << "COLLECT:" << current.print (m_symbolTable, id,
    // GetDefinitionFile(id)) << std::endl;
    if (types.find(current.m_type) != types.end()) {
      objects.push_back(id);
      if (first) return objects;
    }
    if (current.m_sibling) stack.push(current.m_sibling);
    if (current.m_child &&
        (stopPoints.find(current.m_type) == stopPoints.end())) {
      stack.push(current.m_child);
    }
  }
  return objects;
}

bool FileContent::diffTree(NodeId root, const FileContent* oFc, NodeId oroot,
                           std::string* diff_out) const {
  diff_out->clear();

  const VObject& current1 = Object(root);
  NodeId id1 = current1.m_child;
  if (!id1) id1 = current1.m_sibling;

  const VObject& current2 = oFc->Object(oroot);
  NodeId id2 = current2.m_child;
  if (!id2) id2 = current2.m_sibling;

  if ((id1 && (!id2)) || ((!id1) && id2)) return true;

  std::stack<NodeId> stack1;
  std::stack<NodeId> stack2;
  stack1.push(id1);
  stack2.push(id2);
  while (!stack1.empty()) {
    if (stack2.empty()) return true;
    id1 = stack1.top();
    id2 = stack2.top();
    stack1.pop();
    stack2.pop();

    const VObject& current1 = Object(id1);
    const VObject& current2 = oFc->Object(id2);

    if (current1.m_type != current2.m_type) return true;
    if ((current1.m_name || current2.m_name) && (Name(id1) != oFc->Name(id2))) {
      return true;
    }

    if (current1.m_sibling) stack1.push(current1.m_sibling);
    if (current1.m_child) stack1.push(current1.m_child);
    if (current2.m_sibling) stack2.push(current2.m_sibling);
    if (current2.m_child) stack2.push(current2.m_child);
  }
  return !stack2.empty();
}

void FileContent::addDesignElement(const std::string& name,
                                   DesignElement* elem) {
  m_elements.push_back(elem);
  m_elementMap.insert(std::make_pair(name, elem));
}

const DesignElement* FileContent::getDesignElement(
    std::string_view name) const {
  auto itr = m_elementMap.find(name);
  if (itr != m_elementMap.end()) {
    return (*itr).second;
  }
  return nullptr;
}
}  // namespace SURELOG
