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
 * File:   Statement.h
 * Author: alain
 *
 * Created on May 25, 2019, 11:34 AM
 */

#ifndef STATEMENT_H
#define STATEMENT_H
#include <string>
#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"
#include "SourceCompile/VObjectTypes.h"
#include "Design/DataType.h"
#include "Design/Scope.h"

namespace SURELOG {

class Statement {
 public:
  typedef std::vector<Statement*> StatementVector;
  Statement(Scope* scope, Statement* parentStmt,
            const FileContent* fileContent,
            NodeId node, VObjectType type)
      : m_scope(scope),
        m_parent(parentStmt),
        m_fileContent(fileContent),
        m_nodeId(node),
        m_type(type) {}
  virtual ~Statement();

  Scope* getScope() { return m_scope; }
  Statement* getParentStmt() { return m_parent; }

  VObjectType getType() const { return m_type; }

  const FileContent* getFileContent() const { return m_fileContent; }

  NodeId getNodeId() const { return m_nodeId; }

  virtual Function* getFunction() { return NULL; }
  virtual void setFunction(Function* function) {}

  void addStatement(Statement* statement) { m_statements.push_back(statement); }
  const StatementVector& getStatements() const { return m_statements; }

 private:
  Scope* m_scope;
  Statement* m_parent;
  const FileContent* m_fileContent;
  NodeId m_nodeId;
  VObjectType m_type;
  StatementVector m_statements;
};

class SubRoutineArg {
 public:
  SubRoutineArg(NodeId node, Value* value) : m_nodeId(node), m_value(value) {}
  NodeId getNodeId() { return m_nodeId; }
  Value* getValue() { return m_value; }

 private:
  NodeId m_nodeId;
  Value* m_value;
};

class SubRoutineCallStmt : public Statement {
 public:
  SubRoutineCallStmt(Scope* scope, Statement* parentStmt,
                     const FileContent* fileContent,
                     NodeId node, VObjectType type,
                     std::vector<NodeId>& var_chain, std::string funcName,
                     std::vector<SubRoutineArg*>& args, bool static_call,
                     bool system_call)
      : Statement(scope, parentStmt, fileContent, node, type),
        m_var_chain(var_chain),
        m_func(funcName),
        m_args(args),
        m_static(static_call),
        m_system(system_call) {
    m_function = NULL;
  };
  std::vector<NodeId>& getVarChain() { return m_var_chain; }
  std::string getVarName(NodeId base_name);
  std::vector<std::string> getVarChainNames();
  std::string getFunc() { return m_func; }
  bool isStatic() { return m_static; }
  bool isSystemCall() { return m_system; }
  Function* getFunction() override { return m_function; }
  void setFunction(Function* function) override { m_function = function; }

 private:
  std::vector<NodeId> m_var_chain;
  std::string m_func;
  std::vector<SubRoutineArg*> m_args;
  bool m_static;
  bool m_system;
  Function* m_function;
};

class ForLoopStmt : public Scope, public Statement {
 public:
  ForLoopStmt(std::string name, Scope* scope, Statement* parentStmt,
              const FileContent* fileContent, NodeId node, VObjectType type)
      : Scope(name, scope),
        Statement(scope, parentStmt, fileContent, node, type),
        m_conditionId(0),
        m_iteratorType(VObjectType::slNoType) {}

  void addIteratorId(NodeId itrId, NodeId init_expression) {
    m_iteratorIds.push_back(std::make_pair(itrId, init_expression));
  }
  std::vector<std::pair<NodeId, NodeId>>& getIteratorIds() {
    return m_iteratorIds;
  }
  void setIteratorType(VObjectType type) { m_iteratorType = type; }
  VObjectType getIteratorType() { return m_iteratorType; }
  void addIteratorStepId(NodeId itrId) { m_stepIds.push_back(itrId); }
  std::vector<NodeId>& getIteratorStepIds() { return m_stepIds; }
  void setConditionId(NodeId id) { m_conditionId = id; }
  NodeId getConditionId() { return m_conditionId; }

 private:
  std::vector<std::pair<NodeId, NodeId>> m_iteratorIds;
  std::vector<NodeId> m_stepIds;
  NodeId m_conditionId;
  VObjectType m_iteratorType;
};

class ForeachLoopStmt : public Scope, public Statement {
 public:
  ForeachLoopStmt(std::string name, NodeId arrayId, Scope* scope,
                  Statement* parentStmt, const FileContent* fileContent,
                  NodeId node,
                  VObjectType type)
      : Scope(name, scope),
        Statement(scope, parentStmt, fileContent, node, type),
        m_arrayId(arrayId) {}

  NodeId getArrayId() { return m_arrayId; }

  void addIteratorId(NodeId itrId) { m_iteratorIds.push_back(itrId); }
  std::vector<NodeId>& getIteratorIds() { return m_iteratorIds; }

 private:
  NodeId m_arrayId;
  std::vector<NodeId> m_iteratorIds;
};

};  // namespace SURELOG

#endif /* STATEMENT_H */
