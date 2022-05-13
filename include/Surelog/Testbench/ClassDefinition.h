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
 * File:   ClassDefinition.h
 * Author: alain
 *
 * Created on June 1, 2018, 10:12 PM
 */

#ifndef SURELOG_CLASSDEFINITION_H
#define SURELOG_CLASSDEFINITION_H
#pragma once

#include <Surelog/Common/Containers.h>
#include <Surelog/Design/DataType.h>
#include <Surelog/Design/DesignComponent.h>
#include <Surelog/Testbench/TaskMethod.h>

#include <string_view>

// UHDM
#include <uhdm/containers.h>
#include <uhdm/uhdm_forward_decl.h>

namespace SURELOG {

class CompileClass;
class Constraint;
class CoverGroupDefinition;
class DataType;
class FileContent;
class Library;
class Property;

class ClassDefinition : public DesignComponent, public DataType {
  SURELOG_IMPLEMENT_RTTI_2_BASES(ClassDefinition, DesignComponent, DataType)
  friend class CompileClass;

 public:
  ClassDefinition(std::string_view name, Library* library,
                  DesignComponent* container, const FileContent* fC,
                  NodeId nodeId, ClassDefinition* parent,
                  UHDM::class_defn* uhdm_definition);

  ~ClassDefinition() override = default;

  unsigned int getSize() const override;
  VObjectType getType() const override {
    return VObjectType::slClass_declaration;
  }
  bool isInstance() const override { return false; }
  const std::string& getName() const override { return m_name; }
  Library* getLibrary() { return m_library; }
  DesignComponent* getContainer() const { return m_container; }
  void setContainer(DesignComponent* container) { m_container = container; }
  UHDM::class_defn* getUhdmDefinition() const { return m_uhdm_definition; }

  // Parameter definitions are stored DesignComponent maps
  typedef std::map<std::string, Property*, StringViewCompare> PropertyMap;
  typedef std::map<std::string, TaskMethod*, StringViewCompare> TaskMap;
  typedef std::map<std::string, Constraint*, StringViewCompare> ConstraintMap;
  typedef std::map<std::string, const DataType*, StringViewCompare>
      BaseClassMap;
  typedef std::map<std::string, ClassDefinition*, StringViewCompare> ClassMap;
  typedef std::map<std::string, CoverGroupDefinition*, StringViewCompare>
      CoverGroupMap;

  const PropertyMap& getPropertyMap() const { return m_properties; }
  Property* getProperty(std::string_view name) const;
  void insertProperty(Property* p);

  Function* getFunction(std::string_view name) const override;

  const TaskMap& getTaskMap() const { return m_tasks; }
  TaskMap& getMutableTaskMap() { return m_tasks; }
  TaskMethod* getTask(std::string_view name) const override;
  void insertTask(TaskMethod* p);

  const ConstraintMap& getConstraintMap() const { return m_constraints; }
  Constraint* getConstraint(std::string_view name);
  void insertConstraint(Constraint* p);

  // Nested classes
  const ClassMap& getClassMap() const { return m_classes; }
  ClassDefinition* getClass(std::string_view name);
  void insertClass(ClassDefinition* p);

  const CoverGroupMap& getCoverGroupMap() const { return m_covergroups; }
  CoverGroupDefinition* getCoverGroup(std::string_view name);
  void insertCoverGroup(CoverGroupDefinition* p);

  const BaseClassMap& getBaseClassMap() const { return m_baseclasses; }
  BaseClassMap& getMutableBaseClassMap() { return m_baseclasses; }
  const DataType* getBaseClass(std::string_view name) const;
  void insertBaseClass(DataType* p);

  const DataType* getBaseDataType(std::string_view type) const;

  bool hasCompleteBaseSpecification() const;

  UHDM::VectorOfattribute* Attributes() const { return attributes_; }

  bool Attributes(UHDM::VectorOfattribute* data) {
    attributes_ = data;
    return true;
  }

 private:
  std::string m_name;
  Library* m_library;
  DesignComponent* m_container;
  ClassDefinition* m_parent;
  PropertyMap m_properties;
  TaskMap m_tasks;
  ConstraintMap m_constraints;
  ClassMap m_classes;
  CoverGroupMap m_covergroups;
  BaseClassMap m_baseclasses;
  UHDM::class_defn* m_uhdm_definition;

  UHDM::VectorOfattribute* attributes_ = nullptr;
};

}  // namespace SURELOG

#endif /* SURELOG_CLASSDEFINITION_H */
