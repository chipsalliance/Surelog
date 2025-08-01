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

#ifndef SURELOG_FUNCTION_H
#define SURELOG_FUNCTION_H
#pragma once

#include <Surelog/Common/NodeId.h>
#include <Surelog/Common/RTTI.h>
#include <Surelog/Design/Scope.h>
#include <Surelog/Design/Statement.h>

#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

class CompileHelper;
class DesignComponent;
class FileContent;
class TfPortItem;
using TfPortList = std::vector<TfPortItem*>;

class Procedure : public Scope, public Statement {
  SURELOG_IMPLEMENT_RTTI_2_BASES(Procedure, Scope, Statement)
 public:
  Procedure(DesignComponent* parent, const FileContent* fC, NodeId id,
            std::string_view name);
  ~Procedure() override = default;

  DesignComponent* getParent() const { return m_parent; }

  std::string_view getName() const { return m_name; }

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
  SeqBlock(std::string_view name, Scope* parent, Statement* parentStmt,
           const FileContent* fC, NodeId id);
};

class Function : public Procedure {
  SURELOG_IMPLEMENT_RTTI(Function, Procedure)
 public:
  Function(DesignComponent* parent, const FileContent* fC, NodeId id,
           std::string_view name, DataType* returnType)
      : Procedure(parent, fC, id, name), m_returnType(returnType) {}
  bool compile(CompileHelper& compile_helper);
  ~Function() override = default;

  DataType* getReturnType() const { return m_returnType; }

 private:
  DataType* m_returnType;
};
};  // namespace SURELOG

#endif /* SURELOG_FUNCTION_H */
