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
#include <vector>
#include <map>
#include <unordered_set>
#include "Design/TimeInfo.h"
#include "Design/DesignElement.h"
#include "Design/DesignComponent.h"
#include "Design/ValuedComponentI.h"
#include "Design/VObject.h"
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
 public:
  FileContent(SymbolId fileId, Library* library, SymbolTable* symbolTable,
              ErrorContainer* errors, FileContent* parent, SymbolId fileChunkId)
      : DesignComponent(NULL),
        m_fileId(fileId),
        m_library(library),
        m_symbolTable(symbolTable),
        m_errors(errors),
        m_parentFile(parent),
        m_fileChunkId(fileChunkId) {}
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
      VObjectType type);  // Recursively search for first item of type

  NodeId sl_collect(
      NodeId parent, VObjectType type,
      VObjectType stopType);  // Recursively search for first item of type

  std::vector<NodeId> sl_collect_all(
      NodeId parent, VObjectType type,
      bool first = false);  // Recursively search for all items of type

  std::vector<NodeId> sl_collect_all(
      NodeId parent, std::vector<VObjectType>& types,
      bool first = false);  // Recursively search for all items of types

  std::vector<NodeId> sl_collect_all(NodeId parent,
                                     std::vector<VObjectType>& types,
                                     std::vector<VObjectType>& stopPoints,
                                     bool first = false);
  // Recursively search for all items of types
  // and stops at types stopPoints
  unsigned int getSize() override;
  VObjectType getType() override { return VObjectType::slNoType; }
  bool isInstance() override { return false; }
  std::string getName() override { return m_symbolTable->getSymbol(m_fileId); }
  NodeId getRootNode();
  std::string printObjects();                    // The whole file content
  std::string printSubTree(NodeId parentIndex);  // Print subtree from parent
  std::vector<std::string> collectSubTree(NodeId uniqueId);  // Helper function
  std::string getFileName(NodeId id);
  std::string getChunkFileName() {
    return m_symbolTable->getSymbol(m_fileChunkId);
  }
  SymbolTable* getSymbolTable() { return m_symbolTable; }
  void setSymbolTable(SymbolTable* table) { m_symbolTable = table; }
  SymbolId& getFileId(NodeId id);
  Library* getLibrary() { return m_library; }
  std::vector<DesignElement>& getDesignElements() { return m_elements; }
  std::vector<VObject>& getVObjects() { return m_objects; }
  NameIdMap& getObjectLookup() { return m_objectLookup; }
  void insertObjectLookup(std::string name, NodeId id, ErrorContainer* errors);
  std::unordered_set<std::string>& getReferencedObjects() {
    return m_referencedObjects;
  }

  VObject& Object(NodeId index);

  NodeId UniqueId(NodeId index);

  SymbolId& Name(NodeId index);

  NodeId& Child(NodeId index);

  NodeId& Sibling(NodeId index);

  NodeId& Definition(NodeId index);

  void SetDefinitionFile(NodeId index, SymbolId def);
  SymbolId GetDefinitionFile(NodeId index);

  NodeId& Parent(NodeId index);

  VObjectType Type(NodeId index);

  unsigned int& Line(NodeId index);

  std::string SymName(NodeId index) {
    return m_symbolTable->getSymbol(Name(index));
  }

  ModuleNameModuleDefinitionMap& getModuleDefinitions() {
    return m_moduleDefinitions;
  }
  PackageNamePackageDefinitionMultiMap& getPackageDefinitions() {
    return m_packageDefinitions;
  }
  ProgramNameProgramDefinitionMap& getProgramDefinitions() {
    return m_programDefinitions;
  }
  ClassNameClassDefinitionMultiMap& getClassDefinitions() {
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

  ModuleDefinition* getModuleDefinition(const std::string& moduleName);

  DesignComponent* getComponentDefinition(const std::string& componentName);

  Package* getPackage(const std::string& name);

  Program* getProgram(const std::string& name);

  ClassDefinition* getClassDefinition(const std::string& name);

  FileContent* getParent() { return m_parentFile; }
  void setParent(FileContent* parent) { m_parentFile = parent; }

  std::string getFileName() { return m_symbolTable->getSymbol(m_fileId); }

  bool diffTree(std::string& diff, NodeId id, FileContent* oFc, NodeId oId);

 private:
  std::vector<DesignElement> m_elements;

  std::vector<VObject> m_objects;
  std::unordered_map<NodeId, SymbolId> m_definitionFiles;

  NameIdMap m_objectLookup;  // Populated at ResolveSymbol stage
  std::unordered_set<std::string> m_referencedObjects;

  ModuleNameModuleDefinitionMap m_moduleDefinitions;

  PackageNamePackageDefinitionMultiMap m_packageDefinitions;

  ProgramNameProgramDefinitionMap m_programDefinitions;

  ClassNameClassDefinitionMultiMap m_classDefinitions;

  SymbolId m_fileId;
  Library* m_library;
  SymbolTable* m_symbolTable;
  ErrorContainer* m_errors;
  FileContent* m_parentFile;  // for file chunks
  SymbolId m_fileChunkId;
};

};  // namespace SURELOG

#endif /* FILECONTENT_H */
