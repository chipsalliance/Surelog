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

#ifndef TYPEDEF_H
#define TYPEDEF_H

#include <string>
#include "SourceCompile/SymbolTable.h"
#include "Design/DataType.h"

namespace SURELOG {
class FileContent;
class Enum;

class TypeDef : public DataType {
 public:
  TypeDef(const FileContent* fC, NodeId id, NodeId the_def,
          const std::string& name);
  ~TypeDef() override;

  virtual Category getCategory() { return Category::TYPEDEF; }

  void setDataType(DataType* the_type) { m_datatype = the_type; }
  NodeId getDefinitionNode() { return m_the_def; }
  const DataType* getDataType() const { return m_datatype; }

 private:
  NodeId m_the_def;
  DataType* m_datatype;
};

};     // namespace SURELOG
#endif /* TYPEDEF_H */
