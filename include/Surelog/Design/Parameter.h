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

#ifndef SURELOG_PARAMETER_H
#define SURELOG_PARAMETER_H
#pragma once

#include <Surelog/Common/NodeId.h>
#include <Surelog/Common/RTTI.h>
#include <Surelog/Common/SymbolId.h>
#include <Surelog/Design/DataType.h>
#include <Surelog/SourceCompile/VObjectTypes.h>

#include <string_view>

// UHDM
#include <uhdm/uhdm_forward_decl.h>

#include <string>

namespace SURELOG {

class FileContent;

class Parameter final : public DataType {
  SURELOG_IMPLEMENT_RTTI(Parameter, DataType)
 public:
  Parameter(const FileContent* fC, NodeId nodeId, std::string_view name,
            NodeId nodeType, bool portParam);
  ~Parameter() final = default;

  VObjectType getType() const final;
  NodeId getNodeType() const { return m_ntype; }

  void setUhdmParam(uhdm::Any* param) { m_param = param; }
  uhdm::Any* getUhdmParam() const { return m_param; }
  bool isPortParam() const { return m_portParam; }
  void setImportedPackage(std::string_view package) {
    m_importedPackage = package;
  }
  std::string importedPackage() { return m_importedPackage; }
  bool isTypeParam() const { return m_typeParam; }
  void setTypeParam() { m_typeParam = true; }
  bool isMultidimension() const { return m_multiDimension; }
  void setMultidimension() { m_multiDimension = true; }

 private:
  NodeId m_ntype;
  uhdm::Any* m_param = nullptr;
  std::string m_importedPackage;
  bool m_portParam = false;
  bool m_typeParam = false;
  bool m_multiDimension = false;
};

}  // namespace SURELOG

#endif /* SURELOG_PARAMETER_H */
