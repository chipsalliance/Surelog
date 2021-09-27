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

#ifndef FILECONTENT_H
#define FILECONTENT_H

#include <map>
#include <unordered_set>
#include <vector>

#include "Design/DesignComponent.h"
#include "Design/DesignElement.h"
#include "Design/TimeInfo.h"
#include "Design/VObject.h"
#include "Design/ValuedComponentI.h"
#include "SourceCompile/VObjectTypes.h"

namespace SURELOG {

class Library;
class ModuleDefinition;
class Package;
class Program;
class ClassDefinition;
class ExprBuilder;
class ErrorContainer;

typedef std::map<std::string, ModuleDefinition*> ModuleNameModuleDefinitionMap;
typedef std::multimap<std::string, Package*>
    PackageNamePackageDefinitionMultiMap;
typedef std::vector<Package*> PackageDefinitionVec;
typedef std::map<std::string, Program*> ProgramNameProgramDefinitionMap;

typedef std::multimap<std::string, ClassDefinition*>
    ClassNameClassDefinitionMultiMap;
typedef std::map<std::string, ClassDefinition*> ClassNameClassDefinitionMap;

class FileContent : public DesignComponent {
  SURELOG_IMPLEMENT_RTTI(FileContent, DesignComponent)
 public:
  FileContent(SymbolId fileId, Library* library, SymbolTable* symbolTable,
              ErrorContainer* errors, FileContent* parent, SymbolId fileChunkId)
      : DesignComponent(NULL, NULL),
        m_fileId(fileId),
        m_fileChunkId(fileChunkId),
        m_errors(errors),
        m_library(library),
        m_symbolTable(symbolTable),
        m_parentFile(parent) {}

  void setLibrary(Library* lib) { m_library = lib; }
  ~FileContent() override;

  typedef std::unordered_map<std::string, NodeId> NameIdMap;

  NodeId sl_get(NodeId parent,
                VObjectType type);  // Get first child item of type

  NodeId sl_parent(NodeId parent,
                   VObjectType type);  // Get first parent item of type

  NodeId sl_parent(NodeId parent, std::vector<VObjectType> types,
                   VObjectType& actualType);  // Get first parent item of type

  std::vector<NodeId> sl_get_all(
      NodeId parent, VObjectType type);  // get all child items of type

  std::vector<NodeId> sl_get_all(
      NodeId parent,
      std::vector<VObjectType>& types);  // get all child items of types

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
      NodeId parent, std::vector<VObjectType>& types,
      bool first = false) const;  // Recursively search for all items of types

  std::vector<NodeId> sl_collect_all(NodeId parent,
                                     std::vector<VObjectType>& types,
                                     std::vector<VObjectType>& stopPoints,
                                     bool first = false) const;
  // Recursively search for all items of types
  // and stops at types stopPoints
  unsigned int getSize() const override;
  VObjectType getType() const override { return VObjectType::slNoType; }
  bool isInstance() const override { return false; }
  const std::string& getName() const override {
    return m_symbolTable->getSymbol(m_fileId);
  }
  NodeId getRootNode();
  std::string printObjects() const;              // The whole file content
  std::string printSubTree(NodeId parentIndex);  // Print subtree from parent
  std::string printObject(NodeId noedId) const;  // Only print that object
  std::vector<std::string> collectSubTree(NodeId uniqueId);  // Helper function
  const std::string& getFileName(NodeId id) const;
  std::string getChunkFileName() {
    return m_symbolTable->getSymbol(m_fileChunkId);
  }
  SymbolTable* getSymbolTable() { return m_symbolTable; }
  void setSymbolTable(SymbolTable* table) { m_symbolTable = table; }
  SymbolId getFileId(NodeId id) const;
  SymbolId* getMutableFileId(NodeId id);
  Library* getLibrary() const { return m_library; }
  std::vector<DesignElement>& getDesignElements() { return m_elements; }
  std::vector<VObject>& getVObjects() { return m_objects; }
  const NameIdMap& getObjectLookup() const { return m_objectLookup; }
  void insertObjectLookup(std::string name, NodeId id, ErrorContainer* errors);
  std::unordered_set<std::string>& getReferencedObjects() {
    return m_referencedObjects;
  }

  VObject Object(NodeId index) const;
  VObject* MutableObject(NodeId index);

  NodeId UniqueId(NodeId index);

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

  const std::string& SymName(NodeId index) const {
    return m_symbolTable->getSymbol(Name(index));
  }

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
  void addModuleDefinition(std::string moduleName, ModuleDefinition* def) {
    m_moduleDefinitions.insert(std::make_pair(moduleName, def));
  }
  void addPackageDefinition(std::string packageName, Package* package) {
    m_packageDefinitions.insert(std::make_pair(packageName, package));
  }
  void addProgramDefinition(std::string programName, Program* program) {
    m_programDefinitions.insert(std::make_pair(programName, program));
  }
  void addClassDefinition(std::string className, ClassDefinition* classDef) {
    m_classDefinitions.insert(std::make_pair(className, classDef));
  }

  const ModuleDefinition* getModuleDefinition(
      const std::string& moduleName) const;

  DesignComponent* getComponentDefinition(
      const std::string& componentName) const;

  Package* getPackage(const std::string& name);

  const Program* getProgram(const std::string& name) const;

  const ClassDefinition* getClassDefinition(const std::string& name) const;

  const FileContent* getParent() const { return m_parentFile; }
  void setParent(FileContent* parent) { m_parentFile = parent; }

  const std::string& getFileName() const {
    return m_symbolTable->getSymbol(m_fileId);
  }

  bool diffTree(NodeId id, const FileContent* oFc, NodeId oId,
                std::string* diff_out) const;

  SymbolId getSymbolId() const { return m_fileId; }
  bool isLibraryCellFile() { return m_isLibraryCellFile; }
  void setLibraryCellFile() { m_isLibraryCellFile = true; }

 protected:
  std::vector<DesignElement> m_elements;

  std::vector<VObject> m_objects;
  std::unordered_map<NodeId, SymbolId> m_definitionFiles;

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

#endif /* FILECONTENT_H */
