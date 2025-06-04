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

#include "Surelog/Design/FileContent.h"

/*
 * File:   FileContent.cpp
 * Author: alain
 *
 * Created on June 8, 2017, 8:22 PM
 */

#include <uhdm/uhdm_types.h>

#include <cstdint>
#include <iostream>
#include <stack>
#include <string>
#include <string_view>
#include <vector>

#include "Surelog/Common/Containers.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Common/SymbolId.h"
#include "Surelog/Design/DesignComponent.h"
#include "Surelog/Design/DesignElement.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Library/Library.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Utils/StringUtils.h"

namespace SURELOG {
FileContent::FileContent(Session* session, PathId fileId, Library* library,
                         FileContent* parent, PathId fileChunkId)
    : DesignComponent(session, nullptr, nullptr),
      m_fileId(fileId),
      m_fileChunkId(fileChunkId),
      m_library(library),
      m_parentFile(parent) {
  addObject(BadSymbolId, m_fileId, VObjectType::sl_INVALID_, 0, 0, 0, 0,
            InvalidNodeId, InvalidNodeId, InvalidNodeId, InvalidNodeId);
}

FileContent::~FileContent() {
  for (auto de : m_elements) {
    delete de;
  }
}

std::string_view FileContent::getName() const {
  return m_session->getFileSystem()->toPath(m_fileId);
}

std::string_view FileContent::SymName(NodeId index) const {
  if (index >= m_objects.size()) {
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return SymbolTable::getBadSymbol();
  }
  return m_session->getSymbolTable()->getSymbol(Name(index));
}

NodeId FileContent::getRootNode() const {
  if (m_objects.empty()) return InvalidNodeId;

  int32_t index = static_cast<int32_t>(m_objects.size());
  while (--index >= 0) {
    if ((m_objects[index].m_type == VObjectType::ppTop_level_rule) ||
        (m_objects[index].m_type == VObjectType::paTop_level_rule) ||
        (m_objects[index].m_type == VObjectType::paTop_level_library_rule)) {
      return NodeId(index);
    }
  }
  return InvalidNodeId;
}

PathId FileContent::getFileId(NodeId id) const {
  return m_objects[id].m_fileId;
}

PathId* FileContent::getMutableFileId(NodeId id) {
  return &m_objects[id].m_fileId;
}

void FileContent::printTree(std::ostream& strm, NodeId id,
                            size_t indent /* = 0 */) const {
  if (!id) return;

  strm << std::string(indent * 2, ' ')
       << m_objects[id].print(m_session, id, GetDefinitionFile(id), m_fileId)
       << std::endl;
  for (NodeId childId = m_objects[id].m_child; childId;
       childId = m_objects[childId].m_sibling) {
    printTree(strm, childId, indent + 1);
  }
}

void FileContent::printTree(std::ostream& strm) const {
  FileSystem* const fileSystem = m_session->getFileSystem();
  strm << "AST_DEBUG_BEGIN" << std::endl;
  strm << "Count: " << m_objects.size() << std::endl;
  if (m_library) strm << "LIB: " << m_library->getName() << std::endl;
  strm << "FILE: " << fileSystem->toPath(m_fileId) << std::endl;

  PathIdSet includes;
  for (const auto& object : m_objects) {
    if (object.m_fileId && (object.m_fileId != m_fileId)) {
      includes.insert(object.m_fileId);
    }
  }
  for (const PathId& include : includes) {
    strm << "INCL f<" << (RawPathId)include
         << ">: " << fileSystem->toPath(include) << std::endl;
  }

  printTree(strm, getRootNode(), 0);
  strm << "AST_DEBUG_END" << std::endl;
}

std::string FileContent::printObjects() const {
  FileSystem* const fileSystem = m_session->getFileSystem();
  std::ostringstream strm;

  strm << "AST_DEBUG_BEGIN\n";
  strm << "Count: " << m_objects.size() << "\n";
  if (m_library) strm << "LIB: " << m_library->getName() << "\n";
  strm << "FILE f<" << (RawPathId)m_fileId
       << ">:" << fileSystem->toPath(m_fileId) << "\n";
  PathIdSet includes;
  for (const auto& object : m_objects) {
    if (object.m_fileId && (object.m_fileId != m_fileId)) {
      includes.insert(object.m_fileId);
    }
  }
  for (const PathId& include : includes) {
    strm << "INCL f<" << (RawPathId)include
         << ">: " << fileSystem->toPath(include) << "\n";
  }
  if (const NodeId id = getRootNode()) {
    printTree(strm, id, 0);
  } else {
    for (size_t i = 0, ni = m_objects.size(); i < ni; ++i) {
      if (m_objects[i].m_type == VObjectType::paPREPROC_END) {
        printTree(strm, NodeId(i), 0);
      }
    }
  }
  strm << "AST_DEBUG_END\n";
  return strm.str();
}

std::string FileContent::printObject(NodeId nodeId) const {
  if (!nodeId || (nodeId >= m_objects.size())) return "";
  return m_objects[nodeId].print(m_session, nodeId, GetDefinitionFile(nodeId),
                                 m_fileId);
}

void FileContent::insertObjectLookup(std::string_view name, NodeId id,
                                     ErrorContainer* errors) {
  std::pair<NameIdMap::iterator, bool> itr = m_objectLookup.emplace(name, id);
  if (!itr.second) {
    Location loc(getFileId(id), Line(id), Column(id),
                 errors->getSession()->getSymbolTable()->registerSymbol(name));
    Location loc2(getFileId(itr.first->second), Line(itr.first->second),
                  Column(itr.first->second));
    errors->addError(ErrorDefinition::COMP_MULTIPLY_DEFINED_DESIGN_UNIT,
                     {loc, loc2});
  }
}

const ModuleDefinition* FileContent::getModuleDefinition(
    std::string_view moduleName) const {
  ModuleNameModuleDefinitionMap::const_iterator itr =
      m_moduleDefinitions.find(moduleName);
  if (itr != m_moduleDefinitions.end()) {
    return itr->second;
  }
  return nullptr;
}

DesignComponent* FileContent::getComponentDefinition(
    std::string_view componentName) const {
  DesignComponent* comp = (DesignComponent*)getModuleDefinition(componentName);
  if (comp) return comp;
  comp = (DesignComponent*)getProgram(componentName);
  if (comp) return comp;
  comp = (DesignComponent*)getClassDefinition(componentName);
  if (comp) return comp;
  return nullptr;
}

Package* FileContent::getPackage(std::string_view name) const {
  PackageNamePackageDefinitionMultiMap::const_iterator itr =
      m_packageDefinitions.find(name);
  if (itr == m_packageDefinitions.end()) {
    return nullptr;
  } else {
    return itr->second;
  }
}

const Program* FileContent::getProgram(std::string_view name) const {
  ProgramNameProgramDefinitionMap::const_iterator itr =
      m_programDefinitions.find(name);
  if (itr == m_programDefinitions.end()) {
    return nullptr;
  } else {
    return itr->second;
  }
}

ClassDefinition* FileContent::getClassDefinition(std::string_view name) {
  ClassNameClassDefinitionMultiMap::iterator itr =
      m_classDefinitions.find(name);
  if (itr == m_classDefinitions.end()) {
    return nullptr;
  } else {
    return itr->second;
  }
}

const ClassDefinition* FileContent::getClassDefinition(
    std::string_view name) const {
  ClassNameClassDefinitionMultiMap::const_iterator itr =
      m_classDefinitions.find(name);
  if (itr == m_classDefinitions.end()) {
    return nullptr;
  } else {
    return itr->second;
  }
}

const DataType* FileContent::getDataType(Design* design,
                                         std::string_view name) const {
  if (const DataType* const dt = DesignComponent::getDataType(design, name)) {
    return dt;
  } else if (const DataType* const dt = getClassDefinition(name)) {
    return dt;
  }
  return nullptr;
}

void FileContent::SetDefinitionFile(NodeId index, PathId def) {
  m_definitionFiles.emplace(index, def);
}

PathId FileContent::GetDefinitionFile(NodeId index) const {
  auto itr = m_definitionFiles.find(index);
  return (itr == m_definitionFiles.end()) ? BadPathId : itr->second;
}

NodeId FileContent::addObject(SymbolId name, PathId fileId, VObjectType type,
                              uint32_t line, uint16_t column, uint32_t endLine,
                              uint16_t endColumn,
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
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return m_objects[0];
  }
  return m_objects[index];
}

VObject* FileContent::MutableObject(NodeId index) {
  if (!index) return &m_objects[0];
  if (index >= m_objects.size()) {
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return &m_objects[0];
  }
  return &m_objects[index];
}

NodeId FileContent::UniqueId(NodeId index) const {
  if (!index) return InvalidNodeId;
  if (index >= m_objects.size()) {
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return InvalidNodeId;
  }
  return index;
}

SymbolId FileContent::Name(NodeId index) const {
  if (!index) return BadSymbolId;
  if (index >= m_objects.size()) {
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return BadSymbolId;
  }
  return m_objects[index].m_name;
}

NodeId FileContent::Child(NodeId index) const {
  if (!index) return InvalidNodeId;
  if (index >= m_objects.size()) {
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return InvalidNodeId;
  }
  return m_objects[index].m_child;
}

NodeId FileContent::Sibling(NodeId index) const {
  if (!index) return InvalidNodeId;
  if (index >= m_objects.size()) {
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
    std::cout << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return InvalidNodeId;
  }
  return m_objects[index].m_sibling;
}

NodeId FileContent::Definition(NodeId index) const {
  if (!index) return InvalidNodeId;
  if (index >= m_objects.size()) {
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return InvalidNodeId;
  }
  return m_objects[index].m_definition;
}

NodeId FileContent::Parent(NodeId index) const {
  if (!index) return InvalidNodeId;
  if (index >= m_objects.size()) {
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return InvalidNodeId;
  }
  return m_objects[index].m_parent;
}

VObjectType FileContent::Type(NodeId index) const {
  if (!index) return VObjectType::sl_INVALID_;
  if (index >= m_objects.size()) {
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return VObjectType::sl_INVALID_;
  }
  return (VObjectType)m_objects[index].m_type;
}

uint32_t FileContent::Line(NodeId index) const {
  if (!index) return 0;
  if (index >= m_objects.size()) {
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return 0;
  }
  return m_objects[index].m_startLine;
}

uint16_t FileContent::Column(NodeId index) const {
  if (!index) return 0;
  if (index >= m_objects.size()) {
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return 0;
  }
  return m_objects[index].m_startColumn;
}

uint32_t FileContent::EndLine(NodeId index) const {
  if (!index) return 0;
  if (index >= m_objects.size()) {
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
    std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    return 0;
  }
  return m_objects[index].m_endLine;
}

uint16_t FileContent::EndColumn(NodeId index) const {
  if (!index) return 0;
  if (index >= m_objects.size()) {
    m_session->getErrorContainer()->addError(
        ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, Location(m_fileId));
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
  if (current.m_type == type) objects.emplace_back(parent);
  NodeId id = current.m_child;
  while (id) {
    const VObject& current = Object(id);
    if (current.m_type == type) {
      objects.emplace_back(id);
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
    objects.emplace_back(parent);
  }

  NodeId id = current.m_child;
  while (id) {
    const VObject& current = Object(id);
    if (types.find(current.m_type) != types.end()) {
      objects.emplace_back(id);
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
  stack.emplace(id);
  while (!stack.empty()) {
    id = stack.top();
    stack.pop();
    const VObject& current = Object(id);
    if (current.m_type == type) {
      objects.emplace_back(id);
      if (first) return objects;
    }
    if (current.m_sibling) stack.emplace(current.m_sibling);
    if (current.m_child) stack.emplace(current.m_child);
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
  stack.emplace(id);
  while (!stack.empty()) {
    id = stack.top();
    stack.pop();
    const VObject& current = Object(id);
    // std::cout << "COLLECT:" << current.print (m_symbolTable, id,
    // GetDefinitionFile(id)) << std::endl;
    if (types.find(current.m_type) != types.end()) {
      objects.emplace_back(id);
      if (first) return objects;
    }
    if (current.m_sibling) stack.emplace(current.m_sibling);
    if (current.m_child) stack.emplace(current.m_child);
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
  stack.emplace(id);
  while (!stack.empty()) {
    id = stack.top();
    stack.pop();
    const VObject& current = Object(id);
    if (current.m_type == type) return id;
    if (current.m_sibling) stack.emplace(current.m_sibling);
    if (current.m_child && (stopPoint != current.m_type)) {
      stack.emplace(current.m_child);
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
  stack.emplace(id);
  while (!stack.empty()) {
    id = stack.top();
    stack.pop();
    const VObject& current = Object(id);
    // std::cout << "COLLECT:" << current.print (m_symbolTable, id,
    // GetDefinitionFile(id)) << std::endl;
    if (types.find(current.m_type) != types.end()) {
      objects.emplace_back(id);
      if (first) return objects;
    }
    if (current.m_sibling) stack.emplace(current.m_sibling);
    if (current.m_child &&
        (stopPoints.find(current.m_type) == stopPoints.end())) {
      stack.emplace(current.m_child);
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
  stack1.emplace(id1);
  stack2.emplace(id2);
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

    if (current1.m_sibling) stack1.emplace(current1.m_sibling);
    if (current1.m_child) stack1.emplace(current1.m_child);
    if (current2.m_sibling) stack2.emplace(current2.m_sibling);
    if (current2.m_child) stack2.emplace(current2.m_child);
  }
  return !stack2.empty();
}

void FileContent::addDesignElement(std::string_view name, DesignElement* elem) {
  m_elements.emplace_back(elem);
  m_elementMap.emplace(name, elem);
}

const DesignElement* FileContent::getDesignElement(
    std::string_view name) const {
  auto itr = m_elementMap.find(name);
  if (itr != m_elementMap.end()) {
    return itr->second;
  }
  return nullptr;
}

void FileContent::populateCoreMembers(NodeId startIndex, NodeId endIndex,
                                      uhdm::Any* instance,
                                      bool force /* = false */) const {
  NodeId cacheStartIndex, cacheEndIndex;
  if (startIndex && ((instance->getStartLine() == 0) || force)) {
    if (startIndex < m_objects.size()) {
      const VObject& object = m_objects[startIndex];
      instance->setStartLine(object.m_startLine);
      instance->setStartColumn(object.m_startColumn);
      cacheStartIndex = startIndex;
    } else {
      m_session->getErrorContainer()->addError(
          ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND,
          Location(m_fileId));
      std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    }
  }

  if (endIndex && ((instance->getEndLine() == 0) || force)) {
    if (endIndex < m_objects.size()) {
      // For packed/unpacked dimenion, include all ranges!
      if (instance->getUhdmType() != uhdm::UhdmType::Range) {
        NodeId siblingId = endIndex;
        while (siblingId && ((m_objects[siblingId].m_type ==
                              VObjectType::paPacked_dimension) ||
                             (m_objects[siblingId].m_type ==
                              VObjectType::paUnpacked_dimension))) {
          endIndex = siblingId;
          siblingId = m_objects[siblingId].m_sibling;
        }
      }

      const VObject& object = m_objects[endIndex];
      instance->setEndLine(object.m_endLine);
      instance->setEndColumn(object.m_endColumn);
      cacheEndIndex = endIndex;
    } else {
      m_session->getErrorContainer()->addError(
          ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND,
          Location(m_fileId));
      std::cerr << "\nINTERNAL OUT OF BOUND ERROR\n\n";
    }
  }

  if (instance->getFile().empty() ||
      (instance->getFile() == SymbolTable::getBadSymbol()) || force) {
    PathId fileId;
    // Issue #3239: Apparently, it's possible that startIndex.m_fileId
    // & endIndex.m_fileId are differently (for example, including a file
    // in the middle of a module declaration).
    //
    // if (startIndex && endIndex) {
    //   const VObject& startObject = m_objects[startIndex];
    //   const VObject& endObject = m_objects[endIndex];
    //   if (startObject.m_fileId == endObject.m_fileId) {
    //     fileId = startObject.m_fileId;
    //   } else {
    //     Location loc(m_fileId);
    //     Error err(ErrorDefinition::COMP_INTERNAL_ERROR_OUT_OF_BOUND, loc);
    //     m_errors->addError(err);
    //     std::cerr << "\nFILE INDEX MISMATCH\n\n";
    //   }
    // } else
    if (startIndex) {
      const VObject& object = m_objects[startIndex];
      fileId = object.m_fileId;
    } else if (endIndex) {
      const VObject& object = m_objects[endIndex];
      fileId = object.m_fileId;
    }

    if (!fileId) {
      fileId = m_fileId;
    }

    if (fileId) {
      instance->setFile(m_session->getFileSystem()->toPath(fileId));
    }

    if (cacheStartIndex || cacheEndIndex) {
      AnyToNodeIdPairCache::const_iterator it =
          m_anyToNodeIdPairCache.find(instance);
      if (it != m_anyToNodeIdPairCache.cend()) {
        if (!cacheStartIndex) cacheStartIndex = it->second.first;
        if (!cacheEndIndex) cacheEndIndex = it->second.second;
      }
      m_anyToNodeIdPairCache.insert_or_assign(
          instance, std::make_pair(cacheStartIndex, cacheEndIndex));
    }
  }
}

bool FileContent::validate(NodeId parentId) const {
  if (!parentId) return true;

  const VObject& parentObject = m_objects[(RawNodeId)parentId];
  if (parentObject.m_type == VObjectType::paNull_rule) return true;

  if ((parentObject.m_type != VObjectType::paTop_level_rule) &&
      !parentObject.m_parent) {
    return false;
  }

  if (parentObject.m_startLine == parentObject.m_endLine) {
    if (parentObject.m_startColumn > parentObject.m_endColumn) {
      return false;
    }
  } else if (parentObject.m_startLine > parentObject.m_endLine) {
    return false;
  }

  for (NodeId childId = parentObject.m_child; childId;
       childId = m_objects[(RawNodeId)childId].m_sibling) {
    const VObject& childObject = m_objects[(RawNodeId)childId];
    if (childObject.m_parent != parentId) {
      return false;
    }

    if (!validate(childId)) {
      return false;
    }
  }

  return true;
}

bool FileContent::validate() const {
  if (const NodeId id = getRootNode()) {
    return validate(id);
  } else {
    bool result = true;
    for (size_t i = 0, ni = m_objects.size(); i < ni && result; ++i) {
      if (m_objects[i].m_type == VObjectType::paPREPROC_END) {
        result = result && validate(NodeId(i));
      }
    }
    return result;
  }
}
}  // namespace SURELOG
