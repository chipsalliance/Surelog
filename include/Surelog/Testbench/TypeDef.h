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
 * File:   TypeDef.h
 * Author: alain
 *
 * Created on March 6, 2019, 9:14 PM
 */

#ifndef SURELOG_TYPEDEF_H
#define SURELOG_TYPEDEF_H
#pragma once

#include <Surelog/Common/NodeId.h>
#include <Surelog/Common/RTTI.h>
#include <Surelog/Design/DataType.h>

#include <string_view>

namespace SURELOG {

class Enum;
class FileContent;

class TypeDef final : public DataType {
  SURELOG_IMPLEMENT_RTTI(TypeDef, DataType)
 public:
  TypeDef(const FileContent* fC, NodeId id, NodeId the_def,
          std::string_view name, bool forwardDeclaration = false);
  ~TypeDef() final = default;

  void setDataType(DataType* the_type) { m_datatype = the_type; }
  NodeId getDefinitionNode() const { return m_the_def; }
  const DataType* getDataType() const { return m_datatype; }
  bool isForwardDeclaration() const { return m_forwardDeclaration; }

 private:
  NodeId m_the_def;
  DataType* m_datatype;
  bool m_forwardDeclaration;
};

}  // namespace SURELOG
#endif /* SURELOG_TYPEDEF_H */
