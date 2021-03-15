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

namespace SURELOG {

class Parameter : public DataType {
 public:
  Parameter(const FileContent* fC, NodeId nodeId, const std::string& name,
            NodeId node_type, bool port_param);

 ~Parameter() override;

  VObjectType getType() const override;
  NodeId getNodeType() const { return m_ntype; }

  void setUhdmParam(UHDM::any* param) { m_param = param; }
  UHDM::any* getUhdmParam() const { return m_param; }
  bool isPortParam() { return m_port_param; }
  void setImportedPackage(const std::string& package) {m_importedPackage = package; }
  std::string importedPackage() { return m_importedPackage; }
  bool isTypeParam() { return type_param; }
  void setTypeParam() { type_param = true; }
  bool isMultidimension() { return multi_dimension; }
  void setMultidimension() { multi_dimension  = true; }
  
 private:
  NodeId m_ntype;
  UHDM::any* m_param;
  std::string m_importedPackage;
  bool m_port_param;
  bool type_param = false;
  bool multi_dimension = false;
};

}  // namespace SURELOG

#endif /* PARAMETER_H */
