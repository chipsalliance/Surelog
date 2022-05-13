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
 * File:   FileContent.h
 * Author: alain
 *
 * Created on June 8, 2017, 8:22 PM
 */

#ifndef SURELOG_FILECONTENT_H
#define SURELOG_FILECONTENT_H
#pragma once

#include <Surelog/Common/Containers.h>
#include <Surelog/Design/DesignComponent.h>
#include <Surelog/Design/VObject.h>

#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SURELOG {

class ClassDefinition;
class ErrorContainer;
class ExprBuilder;
class Library;
class ModuleDefinition;
class Package;
class Program;

class FileContent : public DesignComponent {
  SURELOG_IMPLEMENT_RTTI(FileContent, DesignComponent)
 public:
  FileContent(SymbolId fileId, Library* library, SymbolTable* symbolTable,
              ErrorContainer* errors, FileContent* parent,
              SymbolId fileChunkId);
  ~FileContent() override = default;

  void setLibrary(Library* lib) { m_library = lib; }

  typedef std::unordered_map<std::string, NodeId> NameIdMap;

  NodeId sl_get(NodeId parent,
                VObjectType type) const;  // Get first child item of type

  NodeId sl_parent(NodeId parent,
                   VObjectType type) const;  // Get first parent item of type

  NodeId sl_parent(
      NodeId parent, const VObjectTypeUnorderedSet& types,
      VObjectType& actualType) const;  // Get first parent item of type

  std::vector<NodeId> sl_get_all(
      NodeId parent, VObjectType type) const;  // get all child items of type

  std::vector<NodeId> sl_get_all(NodeId parent,
                                 const VObjectTypeUnorderedSet& types)
      const;  // get all child items of types

  NodeId sl_collect(
      NodeId parent,
      VObjectType type) const;  // Recursively search for first item of type

  NodeId sl_collect(
      NodeId parent, VObjectType type,
      VObjectType stopType) const;  // Recursively search for first item of type

  std::vector<NodeId> sl_collect_all(
      NodeId parent, VObjectType type,
      bool first = false) const;  // Recursively search for all items of type

  std::vector<NodeId> sl_collect_all(
      NodeId parent, const VObjectTypeUnorderedSet& types,
      bool first = false) const;  // Recursively search for all items of types

  std::vector<NodeId> sl_collect_all(NodeId parent,
                                     const VObjectTypeUnorderedSet& types,
                                     const VObjectTypeUnorderedSet& stopPoints,
                                     bool first = false) const;
  // Recursively search for all items of types
  // and stops at types stopPoints
  unsigned int getSize() const override { return m_objects.size(); }
  VObjectType getType() const override { return VObjectType::slNoType; }
  bool isInstance() const override { return false; }
  const std::string& getName() const override;
  NodeId getRootNode() const;
  std::string printObjects() const;  // The whole file content
  std::string printSubTree(
      NodeId parentIndex) const;                 // Print subtree from parent
  std::string printObject(NodeId noedId) const;  // Only print that object
  std::vector<std::string> collectSubTree(
      NodeId uniqueId) const;  // Helper function
  std::filesystem::path getFileName(NodeId id) const;
  std::filesystem::path getChunkFileName() const;
  SymbolTable* getSymbolTable() const { return m_symbolTable; }
  void setSymbolTable(SymbolTable* table) { m_symbolTable = table; }
  SymbolId getFileId(NodeId id) const;
  SymbolId* getMutableFileId(NodeId id);
  Library* getLibrary() const { return m_library; }
  std::vector<DesignElement*>& getDesignElements() { return m_elements; }
  void addDesignElement(const std::string& name, DesignElement* elem);
  const DesignElement* getDesignElement(std::string_view name) const;
  using DesignComponent::addObject;
  NodeId addObject(SymbolId name, SymbolId fileId, VObjectType type,
                   unsigned int line, unsigned short column,
                   unsigned int endLine, unsigned short endColumn,
                   NodeId parent = InvalidNodeId,
                   NodeId definition = InvalidNodeId,
                   NodeId child = InvalidNodeId,
                   NodeId sibling = InvalidNodeId);
  const std::vector<VObject>& getVObjects() const { return m_objects; }
  std::vector<VObject>* mutableVObjects() { return &m_objects; }
  const NameIdMap& getObjectLookup() const { return m_objectLookup; }
  void insertObjectLookup(const std::string& name, NodeId id,
                          ErrorContainer* errors);
  std::unordered_set<std::string>& getReferencedObjects() {
    return m_referencedObjects;
  }

  const VObject& Object(NodeId index) const;
  VObject* MutableObject(NodeId index);

  NodeId UniqueId(NodeId index) const;

  SymbolId Name(NodeId index) const;

  NodeId Child(NodeId index) const;

  NodeId Sibling(NodeId index) const;

  NodeId Definition(NodeId index) const;

  void SetDefinitionFile(NodeId index, SymbolId def);
  SymbolId GetDefinitionFile(NodeId index) const;

  NodeId Parent(NodeId index) const;

  VObjectType Type(NodeId index) const;

  unsigned int Line(NodeId index) const;

  unsigned short Column(NodeId index) const;

  unsigned int EndLine(NodeId index) const;

  unsigned short EndColumn(NodeId index) const;

  const std::string& SymName(NodeId index) const;

  const ModuleNameModuleDefinitionMap& getModuleDefinitions() const {
    return m_moduleDefinitions;
  }
  const PackageNamePackageDefinitionMultiMap& getPackageDefinitions() const {
    return m_packageDefinitions;
  }
  const ProgramNameProgramDefinitionMap& getProgramDefinitions() const {
    return m_programDefinitions;
  }
  const ClassNameClassDefinitionMultiMap& getClassDefinitions() const {
    return m_classDefinitions;
  }
  void addModuleDefinition(const std::string& moduleName,
                           ModuleDefinition* def) {
    m_moduleDefinitions.insert(std::make_pair(moduleName, def));
  }
  void addPackageDefinition(const std::string& packageName, Package* package) {
    m_packageDefinitions.insert(std::make_pair(packageName, package));
  }
  void addProgramDefinition(const std::string& programName, Program* program) {
    m_programDefinitions.insert(std::make_pair(programName, program));
  }
  void addClassDefinition(const std::string& className,
                          ClassDefinition* classDef) {
    m_classDefinitions.insert(std::make_pair(className, classDef));
  }

  const ModuleDefinition* getModuleDefinition(
      const std::string& moduleName) const;

  DesignComponent* getComponentDefinition(
      const std::string& componentName) const;

  Package* getPackage(const std::string& name) const;

  const Program* getProgram(const std::string& name) const;

  const ClassDefinition* getClassDefinition(const std::string& name) const;

  const FileContent* getParent() const { return m_parentFile; }
  void setParent(FileContent* parent) { m_parentFile = parent; }

  std::filesystem::path getFileName() const;

  bool diffTree(NodeId id, const FileContent* oFc, NodeId oId,
                std::string* diff_out) const;

  SymbolId getSymbolId() const { return m_fileId; }
  bool isLibraryCellFile() const { return m_isLibraryCellFile; }
  void setLibraryCellFile() { m_isLibraryCellFile = true; }

 protected:
  std::vector<DesignElement*> m_elements;
  std::map<std::string, DesignElement*, StringViewCompare> m_elementMap;
  std::vector<VObject> m_objects;
  std::unordered_map<NodeId, SymbolId, NodeIdHasher, NodeIdEqualityComparer>
      m_definitionFiles;

  NameIdMap m_objectLookup;  // Populated at ResolveSymbol stage
  std::unordered_set<std::string> m_referencedObjects;

  ModuleNameModuleDefinitionMap m_moduleDefinitions;

  PackageNamePackageDefinitionMultiMap m_packageDefinitions;

  ProgramNameProgramDefinitionMap m_programDefinitions;

  ClassNameClassDefinitionMultiMap m_classDefinitions;

  const SymbolId m_fileId;
  const SymbolId m_fileChunkId;
  ErrorContainer* const m_errors;

  Library* m_library;          // TODO: should be set in constructor and *const
  SymbolTable* m_symbolTable;  // TODO: should be set in constructor *const
  FileContent* m_parentFile;   // for file chunks
  bool m_isLibraryCellFile = false;
};

};  // namespace SURELOG

#endif /* SURELOG_FILECONTENT_H */
