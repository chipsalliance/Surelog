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

#include <string_view>

#include <Surelog/Common/Containers.h>
#include <Surelog/Design/DesignComponent.h>
#include <Surelog/Expression/ExprBuilder.h>

// UHDM
#include <uhdm/containers.h>

namespace SURELOG {

class CompilePackage;
class FileContent;
class Library;
class Netlist;

class Package : public DesignComponent {
  SURELOG_IMPLEMENT_RTTI(Package, DesignComponent)
  friend CompilePackage;

 public:
  Package(std::string_view name, Library* library,
          FileContent* fC, NodeId nodeId);
  void append(Package* package);

  ~Package() override = default;

  Library* getLibrary() { return m_library; }

  unsigned int getSize() const override;
  VObjectType getType() const override {
    return VObjectType::slPackage_declaration;
  }
  bool isInstance() const override { return false; }
  const std::string& getName() const override { return m_name; }

  ClassNameClassDefinitionMultiMap& getClassDefinitions() {
    return m_classDefinitions;
  }
  void addClassDefinition(std::string className, ClassDefinition* classDef) {
    m_classDefinitions.insert(std::make_pair(className, classDef));
  }
  ClassDefinition* getClassDefinition(const std::string& name);
  ExprBuilder* getExprBuilder() { return &m_exprBuilder; }

  UHDM::VectorOfattribute* Attributes() const { return attributes_; }

  bool Attributes(UHDM::VectorOfattribute* data) {
    attributes_ = data;
    return true;
  }

  // To hold variables
  Netlist* getNetlist() { return m_netlist; }
  void setNetlist(Netlist* netlist) { m_netlist = netlist; }

 private:
  std::string m_name;
  Library* m_library;
  ExprBuilder m_exprBuilder;
  ClassNameClassDefinitionMultiMap m_classDefinitions;

  UHDM::VectorOfattribute* attributes_ = nullptr;
  Netlist* m_netlist = nullptr;
};

};  // namespace SURELOG

#endif /* SURELOG_PACKAGE_H */
