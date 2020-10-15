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
#include "Common/PortNetHolder.h"
#include "Design/ValuedComponentI.h"

namespace SURELOG {

class Package;
class Function;
class Variable;
class Parameter;

class DesignComponent : public ValuedComponentI, public PortNetHolder {
 public:
  DesignComponent(const DesignComponent* parent,
                  DesignComponent* definition)
    : ValuedComponentI(parent, definition), PortNetHolder() {}
  ~DesignComponent() override {}

  virtual unsigned int getSize() const = 0;
  virtual VObjectType getType() const = 0;
  virtual bool isInstance() const = 0;
  virtual const std::string& getName() const = 0;
  void append(DesignComponent*);

  typedef std::map<std::string, DataType*> DataTypeMap;
  typedef std::map<std::string, TypeDef*> TypeDefMap;
  typedef std::map<std::string, Function*> FunctionMap;
  typedef std::map<std::string, Variable*> VariableMap;
  typedef std::map<std::string, Parameter*> ParameterMap;

  void addFileContent(const FileContent* fileContent, NodeId nodeId);
  const std::vector<const FileContent*>& getFileContents() const {
    return m_fileContents;
  }
  const std::vector<NodeId>& getNodeIds() const { return m_nodeIds; }

  // Precompiled Object of interest
  const std::vector<FileCNodeId>& getObjects(VObjectType type) const;
  void addObject(VObjectType type, FileCNodeId object);

  void addNamedObject(std::string name, FileCNodeId object,
                      DesignComponent* def = NULL);
  std::map<std::string, std::pair<FileCNodeId, DesignComponent*>>&
  getNamedObjects() {
    return m_namedObjects;
  }
  const std::pair<FileCNodeId, DesignComponent*>* getNamedObject(const std::string& name) const;

  DataTypeMap& getUsedDataTypeMap() { return m_usedDataTypes; }
  DataType* getUsedDataType(const std::string& name);
  void insertUsedDataType(const std::string& dataTypeName, DataType* dataType);

  const DataTypeMap& getDataTypeMap() const { return m_dataTypes; }
  const DataType* getDataType(const std::string& name) const;
  void insertDataType(const std::string& dataTypeName, DataType* dataType);

  const TypeDefMap& getTypeDefMap() const { return m_typedefs; }
  const TypeDef* getTypeDef(const std::string& name) const;
  void insertTypeDef(TypeDef* p);

  FunctionMap& getFunctionMap() { return m_functions; }
  virtual Function* getFunction(const std::string& name) const;
  void insertFunction(Function* p);

  void addAccessPackage(Package* p) { m_packages.push_back(p); }
  const std::vector<Package*>& getAccessPackages() const { return m_packages; }

  void addVariable(Variable* var);
  const VariableMap& getVariables() const { return m_variables; }
  Variable* getVariable(const std::string& name);

  ParameterMap& getParameterMap() { return m_parameters; }
  Parameter* getParameter(const std::string& name) const;
  void insertParameter(Parameter* p);

  void addImportedSymbol(UHDM::import* i) { m_imported_symbols.push_back(i); }
  const std::vector<UHDM::import*>& getImportedSymbols() const { return m_imported_symbols; }

  void needLateBinding(UHDM::ref_obj* obj) { m_needLateBinding.push_back(obj); }
  const std::vector<UHDM::ref_obj*>& getLateBinding() const { return m_needLateBinding; }

 protected:
  std::vector<const FileContent*> m_fileContents;
  std::vector<NodeId> m_nodeIds;
  FunctionMap m_functions;

 private:
  std::map<VObjectType, std::vector<FileCNodeId>> m_objects;
  std::map<std::string, std::pair<FileCNodeId, DesignComponent*>>
      m_namedObjects;
  std::vector<FileCNodeId> m_empty;
 protected: 
  DataTypeMap m_dataTypes;
 private: 
  DataTypeMap m_usedDataTypes;
  TypeDefMap m_typedefs;
  std::vector<Package*> m_packages;
  VariableMap m_variables;
  std::vector<UHDM::import*> m_imported_symbols;
  std::vector<UHDM::ref_obj*> m_needLateBinding;
  ParameterMap m_parameters;
};

};  // namespace SURELOG

#endif /* DESIGNCOMPONENT_H */
