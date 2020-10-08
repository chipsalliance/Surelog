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
 * File:   Parameter.h
 * Author: alain
 *
 * Created on April 15, 2019, 8:03 PM
 */

#ifndef PARAMETER_H
#define PARAMETER_H
#include <string>
#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"

namespace UHDM {
  class typespec;
};

namespace SURELOG {

class Parameter : public DataType {
 public:
  Parameter(const FileContent* fC, NodeId nodeId, const std::string& name,
            NodeId node_type);

 ~Parameter() override;

  virtual Category getCategory() { return Category::PARAMETER; }

  VObjectType getType() const override;
  NodeId getNodeType() const { return m_ntype; }

  void setTypespec(UHDM::typespec* type) { m_typespec = type; }
  UHDM::typespec* getTypespec() const { return m_typespec; }

 private:
  NodeId m_ntype;
  UHDM::typespec* m_typespec;
};

}  // namespace SURELOG

#endif /* PARAMETER_H */
