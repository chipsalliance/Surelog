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
 * File:   Function.h
 * Author: alain
 *
 * Created on February 21, 2019, 8:19 PM
 */

#ifndef FUNCTION_H
#define FUNCTION_H
#include <string>

#include "Design/DataType.h"
#include "Design/FileContent.h"
#include "Design/Scope.h"
#include "Design/Statement.h"
#include "Design/TfPortItem.h"
#include "DesignCompile/CompileHelper.h"
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/VObjectTypes.h"
#include "Testbench/Variable.h"

namespace SURELOG {

class Procedure : public Scope, public Statement {
  SURELOG_IMPLEMENT_RTTI_2_BASES(Procedure, Scope, Statement)
 public:
  Procedure(DesignComponent* parent, const FileContent* fC, NodeId id,
            const std::string& name)
      : Scope(name, NULL),
        Statement(this, NULL, fC, id,
                  fC ? fC->Type(id) : VObjectType::slFunction_prototype),
        m_parent(parent),
        m_fileContent(fC),
        m_nodeId(id),
        m_name(name) {}

  ~Procedure() override {}

  DesignComponent* getParent() const { return m_parent; }

  const std::string& getName() const { return m_name; }

  const FileContent* getFileContent() const { return m_fileContent; }

  NodeId getNodeId() const { return m_nodeId; }

  TfPortList& getParams() { return m_params; }

 protected:
  DesignComponent* m_parent;
  const FileContent* m_fileContent;
  NodeId m_nodeId;
  const std::string m_name;
  TfPortList m_params;
};

class SeqBlock : public Scope, public Statement {
  SURELOG_IMPLEMENT_RTTI_2_BASES(SeqBlock, Scope, Statement)
 public:
  SeqBlock(const std::string& name, Scope* parent, Statement* parentStmt,
           const FileContent* fC, NodeId id)
      : Scope(name, parent),
        Statement(this, parentStmt, fC, id,
                  fC ? fC->Type(id) : VObjectType::slSeq_block){};
};

class Function : public Procedure {
  SURELOG_IMPLEMENT_RTTI(Function, Procedure)
 public:
  Function(DesignComponent* parent, const FileContent* fC, NodeId id,
           std::string name, DataType* returnType)
      : Procedure(parent, fC, id, name), m_returnType(returnType) {}
  bool compile(CompileHelper& compile_helper);
  ~Function() override;

  DataType* getReturnType() { return m_returnType; }

 private:
  DataType* m_returnType;
};
};  // namespace SURELOG

#endif /* FUNCTION_H */
