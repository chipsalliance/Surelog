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
 * File:   Scope.h
 * Author: alain
 *
 * Created on August 31, 2019, 11:24 AM
 */

#ifndef SURELOG_SCOPE_H
#define SURELOG_SCOPE_H
#pragma once

#include <Surelog/Common/RTTI.h>

#include <functional>
#include <map>
#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

class DataType;
class Statement;
class Variable;

class Scope : public RTTI {
  SURELOG_IMPLEMENT_RTTI(Scope, RTTI)
 public:
  using VariableMap = std::map<std::string, Variable*, std::less<>>;
  using DataTypeMap = std::map<std::string, DataType*, std::less<>>;
  using StmtVector = std::vector<Statement*>;
  using ScopeVector = std::vector<Scope*>;

  Scope(std::string_view name, Scope* parent)
      : m_name(name), m_parentScope(parent) {}
  ~Scope() override {}

  std::string_view getName() const { return m_name; }
  Scope* getParentScope() { return m_parentScope; }

  void addVariable(Variable* var);

  VariableMap& getVariables() { return m_variables; }
  Variable* getVariable(std::string_view name);

  DataTypeMap& getUsedDataTypeMap() { return m_usedDataTypes; }
  DataType* getUsedDataType(std::string_view name);
  void insertUsedDataType(std::string_view dataTypeName, DataType* dataType) {
    m_usedDataTypes.emplace(dataTypeName, dataType);
  }

  void addStmt(Statement* stmt) { m_statements.push_back(stmt); }
  StmtVector& getStmts() { return m_statements; }

  void addScope(Scope* scope) { m_scopes.push_back(scope); }
  ScopeVector& getScopes() { return m_scopes; }

 private:
  const std::string m_name;
  Scope* const m_parentScope;
  VariableMap m_variables;
  DataTypeMap m_usedDataTypes;
  StmtVector m_statements;
  ScopeVector m_scopes;
};

}  // namespace SURELOG
SURELOG_IMPLEMENT_RTTI_VIRTUAL_CAST_FUNCTIONS(scope_cast, SURELOG::Scope)

#endif /* SURELOG_SCOPE_H */
