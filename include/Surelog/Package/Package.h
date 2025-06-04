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
 * File:   Package.h
 * Author: alain
 *
 * Created on March 18, 2018, 7:58 PM
 */

#ifndef SURELOG_PACKAGE_H
#define SURELOG_PACKAGE_H
#pragma once

#include <Surelog/Common/Containers.h>
#include <Surelog/Common/RTTI.h>
#include <Surelog/Design/DesignComponent.h>
#include <Surelog/Expression/ExprBuilder.h>
#include <Surelog/SourceCompile/VObjectTypes.h>

#include <cstdint>
#include <string_view>

// UHDM
#include <uhdm/containers.h>

namespace SURELOG {
class CompilePackage;
class FileContent;
class Library;
class Netlist;
class Session;

class Package final : public DesignComponent {
  SURELOG_IMPLEMENT_RTTI(Package, DesignComponent)
  friend CompilePackage;

 public:
  Package(Session* session, std::string_view name, Library* library,
          const FileContent* fC, NodeId nodeId, uhdm::Serializer& serializer);
  void append(Package* package);

  ~Package() final = default;

  Library* getLibrary() { return m_library; }

  uint32_t getSize() const final;
  VObjectType getType() const final {
    return VObjectType::paPackage_declaration;
  }
  bool isInstance() const final { return false; }
  std::string_view getName() const final { return m_name; }

  const DataType* getDataType(Design* design,
                              std::string_view name) const override;

  ClassNameClassDefinitionMultiMap& getClassDefinitions() {
    return m_classDefinitions;
  }
  void addClassDefinition(std::string_view className,
                          ClassDefinition* classDef) {
    m_classDefinitions.emplace(className, classDef);
  }
  ClassDefinition* getClassDefinition(std::string_view name);
  const ClassDefinition* getClassDefinition(std::string_view name) const;
  ExprBuilder* getExprBuilder() { return &m_exprBuilder; }

  uhdm::AttributeCollection* getAttributes() const { return m_attributes; }

  bool setAttributes(uhdm::AttributeCollection* data) {
    m_attributes = data;
    return true;
  }

  // To hold variables
  Netlist* getNetlist() { return m_netlist; }
  void setNetlist(Netlist* netlist) { m_netlist = netlist; }

  Package* getUnElabPackage() { return m_unElabPackage; }

  std::string_view getEndLabel() const { return m_endLabel; }
  void setEndLabel(std::string_view endLabel) { m_endLabel = endLabel; }

 private:
  std::string m_name;
  std::string m_endLabel;
  Library* m_library = nullptr;
  ExprBuilder m_exprBuilder;
  ClassNameClassDefinitionMultiMap m_classDefinitions;

  uhdm::AttributeCollection* m_attributes = nullptr;
  Netlist* m_netlist = nullptr;
  Package* m_unElabPackage = nullptr;
};

};  // namespace SURELOG

#endif /* SURELOG_PACKAGE_H */
