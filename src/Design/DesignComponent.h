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
 * File:   DesignComponent.h
 * Author: alain
 *
 * Created on March 25, 2018, 10:27 PM
 */

#ifndef DESIGNCOMPONENT_H
#define DESIGNCOMPONENT_H
#include <vector>
#include <map>
#include "SourceCompile/VObjectTypes.h"
#include "Design/FileCNodeId.h"
#include "Design/DataType.h"
#include "Testbench/TypeDef.h"
#include "Design/ValuedComponentI.h"

namespace SURELOG {

class Package;
class Function;
class Variable;

class DesignComponent : public ValuedComponentI {
 public:
  DesignComponent(DesignComponent* parent) : ValuedComponentI(parent) {}
  ~DesignComponent() override {}

  virtual unsigned int getSize() = 0;
  virtual VObjectType getType() = 0;
  virtual bool isInstance() = 0;
  virtual std::string getName() = 0;
  void append(DesignComponent*);

  typedef std::map<std::string, DataType*> DataTypeMap;
  typedef std::map<std::string, TypeDef*> TypeDefMap;
  typedef std::map<std::string, Function*> FunctionMap;
  typedef std::map<std::string, Variable*> VariableMap;

  void addFileContent(FileContent* fileContent, NodeId nodeId);
  std::vector<FileContent*>& getFileContents() { return m_fileContents; }
  std::vector<NodeId>& getNodeIds() { return m_nodeIds; }

  // Precompiled Object of interest
  std::vector<FileCNodeId>& getObjects(VObjectType type);
  void addObject(VObjectType type, FileCNodeId object);

  void addNamedObject(std::string name, FileCNodeId object,
                      DesignComponent* def = NULL);
  std::map<std::string, std::pair<FileCNodeId, DesignComponent*>>&
  getNamedObjects() {
    return m_namedObjects;
  }
  std::pair<FileCNodeId, DesignComponent*>* getNamedObject(std::string name);

  DataTypeMap& getUsedDataTypeMap() { return m_usedDataTypes; }
  DataType* getUsedDataType(const std::string& name);
  void insertUsedDataType(const std::string& dataTypeName, DataType* dataType);

  DataTypeMap& getDataTypeMap() { return m_dataTypes; }
  DataType* getDataType(const std::string& name);
  void insertDataType(const std::string& dataTypeName, DataType* dataType);

  TypeDefMap& getTypeDefMap() { return m_typedefs; }
  TypeDef* getTypeDef(const std::string& name);
  void insertTypeDef(TypeDef* p);

  FunctionMap& getFunctionMap() { return m_functions; }
  virtual Function* getFunction(const std::string& name);
  void insertFunction(Function* p);

  void addAccessPackage(Package* p) { m_packages.push_back(p); }
  std::vector<Package*>& getAccessPackages() { return m_packages; }

  void addVariable(Variable* var);
  VariableMap& getVariables() { return m_variables; }
  Variable* getVariable(const std::string& name);

 protected:
  std::vector<FileContent*> m_fileContents;
  std::vector<NodeId> m_nodeIds;
  FunctionMap m_functions;

 private:
  std::map<VObjectType, std::vector<FileCNodeId>> m_objects;
  std::map<std::string, std::pair<FileCNodeId, DesignComponent*>>
      m_namedObjects;
  std::vector<FileCNodeId> m_empty;
  DataTypeMap m_dataTypes;
  DataTypeMap m_usedDataTypes;
  TypeDefMap m_typedefs;
  std::vector<Package*> m_packages;
  VariableMap m_variables;
};

};  // namespace SURELOG

#endif /* DESIGNCOMPONENT_H */
