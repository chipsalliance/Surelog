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

#ifndef SURELOG_DESIGNCOMPONENT_H
#define SURELOG_DESIGNCOMPONENT_H
#pragma once

#include <Surelog/Common/Containers.h>
#include <Surelog/Common/NodeId.h>
#include <Surelog/Common/PathId.h>
#include <Surelog/Common/PortNetHolder.h>
#include <Surelog/Common/RTTI.h>
#include <Surelog/Common/SymbolId.h>
#include <Surelog/Design/FileCNodeId.h>
#include <Surelog/Design/LetStmt.h>
#include <Surelog/Design/ValuedComponentI.h>
#include <Surelog/SourceCompile/VObjectTypes.h>

#include <cstdint>
#include <functional>
#include <map>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

// UHDM
#include <uhdm/BaseClass.h>
#include <uhdm/uhdm_forward_decl.h>

namespace SURELOG {

class DataType;
class Design;
class DesignElement;
class FileContent;
class Function;
class Package;
class ParamAssign;
class Parameter;
class Task;
class TypeDef;
class Variable;

class ExprEval {
 public:
  ExprEval(uhdm::Expr* expr, ValuedComponentI* instance, PathId fileId,
           uint32_t lineNumber, uhdm::Any* pexpr)
      : m_expr(expr),
        m_instance(instance),
        m_fileId(fileId),
        m_lineNumber(lineNumber),
        m_pexpr(pexpr) {}
  uhdm::Expr* const m_expr = nullptr;
  ValuedComponentI* const m_instance = nullptr;
  PathId m_fileId;
  uint32_t m_lineNumber;
  uhdm::Any* const m_pexpr = nullptr;
};

class DesignComponent : public ValuedComponentI, public PortNetHolder {
  SURELOG_IMPLEMENT_RTTI(DesignComponent, ValuedComponentI)
 public:
  DesignComponent(Session* session, const DesignComponent* parent,
                  DesignComponent* definition)
      : ValuedComponentI(session, parent, definition) {}
  ~DesignComponent() override = default;

  virtual uint32_t getSize() const = 0;
  virtual VObjectType getType() const = 0;
  virtual bool isInstance() const = 0;
  virtual std::string_view getName() const = 0;
  void append(DesignComponent*);

  using DataTypeMap = std::map<std::string, DataType*, StringViewCompare>;
  using TypeDefMap = std::map<std::string, TypeDef*, StringViewCompare>;
  using DataTypeVec = std::vector<DataType*>;
  using TypeDefVec = std::vector<TypeDef*>;
  using FunctionMap = std::map<std::string, Function*, StringViewCompare>;
  using TaskMap = std::map<std::string, Task*, StringViewCompare>;
  using VariableMap = std::map<std::string, Variable*, StringViewCompare>;
  using ParameterMap = std::map<std::string, Parameter*, StringViewCompare>;
  using ParameterVec = std::vector<Parameter*>;
  using ParamAssignVec = std::vector<ParamAssign*>;
  using LetStmtMap = std::map<std::string, LetStmt*, StringViewCompare>;
  using NamedObjectMap =
      std::map<std::string, std::pair<FileCNodeId, DesignComponent*>,
               StringViewCompare>;
  using FuncNameTypespecVec =
      std::vector<std::pair<std::string, uhdm::Typespec*>>;

  void addFileContent(const FileContent* fileContent, NodeId nodeId);
  const std::vector<const FileContent*>& getFileContents() const {
    return m_fileContents;
  }
  const std::vector<NodeId>& getNodeIds() const { return m_nodeIds; }

  // Precompiled Object of interest
  const std::vector<FileCNodeId>& getObjects(VObjectType type) const;
  void addObject(VObjectType type, FileCNodeId object);

  void addNamedObject(std::string_view name, FileCNodeId object,
                      DesignComponent* def = nullptr);
  const NamedObjectMap& getNamedObjects() const { return m_namedObjects; }
  const std::pair<FileCNodeId, DesignComponent*>* getNamedObject(
      std::string_view name) const;

  DataTypeMap& getUsedDataTypeMap() { return m_usedDataTypes; }
  DataType* getUsedDataType(std::string_view name);
  void insertUsedDataType(std::string_view dataTypeName, DataType* dataType);

  const DataTypeMap& getDataTypeMap() const { return m_dataTypes; }
  virtual const DataType* getDataType(Design* design,
                                      std::string_view name) const;
  void insertDataType(std::string_view dataTypeName, DataType* dataType);

  const TypeDefMap& getTypeDefMap() const { return m_typedefs; }
  const TypeDef* getTypeDef(std::string_view name) const;
  void insertTypeDef(TypeDef* p);

  FunctionMap& getFunctionMap() { return m_functions; }
  virtual Function* getFunction(std::string_view name) const;
  void insertFunction(Function* p);

  TaskMap& getTaskMap() { return m_tasks; }
  virtual Task* getTask(std::string_view name) const;
  void insertTask(Task* p);

  void addAccessPackage(Package* p) { m_packages.emplace_back(p); }
  const std::vector<Package*>& getAccessPackages() const { return m_packages; }

  void addVariable(Variable* var);
  const VariableMap& getVariables() const { return m_variables; }
  Variable* getVariable(std::string_view name);

  const ParameterMap& getParameterMap() const { return m_parameterMap; }
  Parameter* getParameter(std::string_view name) const;
  void insertParameter(Parameter* p);
  const ParameterVec& getOrderedParameters() const {
    return m_orderedParameters;
  }

  void addParamAssign(ParamAssign* assign) {
    m_paramAssigns.emplace_back(assign);
  }
  const ParamAssignVec& getParamAssignVec() const { return m_paramAssigns; }

  void addImportTypespec(uhdm::ImportTypespec* i) {
    m_importTypespecs.emplace_back(i);
  }
  const DataType* getImportedDataType(
      Design* design, std::string_view name,
      std::set<const DesignComponent*>& visited) const;
  const std::vector<uhdm::ImportTypespec*>& getImportedSymbols() const {
    return m_importTypespecs;
  }

  void addElabSysCall(uhdm::TFCall* elab_sys_call) {
    m_elabSysCalls.emplace_back(elab_sys_call);
  }
  const std::vector<uhdm::TFCall*>& getElabSysCalls() const {
    return m_elabSysCalls;
  }

  void addPropertyDecl(uhdm::PropertyDecl* prop_decl) {
    m_propertyDecls.emplace_back(prop_decl);
  }
  const std::vector<uhdm::PropertyDecl*>& getPropertyDecls() const {
    return m_propertyDecls;
  }

  void addSequenceDecl(uhdm::SequenceDecl* seq_decl) {
    m_sequenceDecls.emplace_back(seq_decl);
  }
  const std::vector<uhdm::SequenceDecl*>& getSequenceDecls() const {
    return m_sequenceDecls;
  }

  void setUhdmModel(uhdm::Any* model) { m_model = model; }
  uhdm::Any* getUhdmModel() { return m_model; }
  template <typename T>
  T* getUhdmModel() const {
    return (m_model == nullptr) ? nullptr : any_cast<T>(m_model);
  }

  void scheduleParamExprEval(std::string_view name, ExprEval& expr_eval) {
    m_scheduledParamExprEval.emplace_back(name, expr_eval);
  }
  std::vector<std::pair<std::string, ExprEval>>& getScheduledParamExprEval() {
    return m_scheduledParamExprEval;
  }
  void setDesignElement(const DesignElement* elem) { m_designElement = elem; }
  const DesignElement* getDesignElement() const { return m_designElement; }

  void insertLetStmt(std::string_view name, LetStmt* decl);
  LetStmt* getLetStmt(std::string_view name);

  const LetStmtMap& getLetStmts() const { return m_letDecls; }

 private:
  const DataType* getDataTypeRecursive(
      Design* design, std::string_view name,
      std::set<const DesignComponent*>& visited) const;

 protected:
  std::vector<const FileContent*> m_fileContents;
  std::vector<NodeId> m_nodeIds;
  FunctionMap m_functions;
  TaskMap m_tasks;

 private:
  std::map<VObjectType, std::vector<FileCNodeId>, std::less<>> m_objects;
  NamedObjectMap m_namedObjects;
  std::vector<FileCNodeId> m_empty;

 protected:
  DataTypeMap m_dataTypes;

 private:
  DataTypeMap m_usedDataTypes;
  TypeDefMap m_typedefs;
  std::vector<Package*> m_packages;
  VariableMap m_variables;
  std::vector<uhdm::ImportTypespec*> m_importTypespecs;
  std::vector<uhdm::TFCall*> m_elabSysCalls;
  std::vector<uhdm::PropertyDecl*> m_propertyDecls;
  std::vector<uhdm::SequenceDecl*> m_sequenceDecls;
  ParameterMap m_parameterMap;
  ParameterVec m_orderedParameters;
  ParamAssignVec m_paramAssigns;
  uhdm::Any* m_model = nullptr;
  std::vector<std::pair<std::string, ExprEval>> m_scheduledParamExprEval;
  const DesignElement* m_designElement = nullptr;
  LetStmtMap m_letDecls;
};

};  // namespace SURELOG

#endif /* SURELOG_DESIGNCOMPONENT_H */
