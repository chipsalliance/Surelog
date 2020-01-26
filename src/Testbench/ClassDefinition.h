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

#ifndef CLASSDEFINITION_H
#define CLASSDEFINITION_H

#include "Design/DesignComponent.h"
#include "Design/ValuedComponentI.h"
#include "Design/DataType.h"
#include "Property.h"
#include "FunctionMethod.h"
#include "TaskMethod.h"
#include "Constraint.h"
#include "TypeDef.h"
#include "CoverGroupDefinition.h"
#include "Design/Parameter.h"

namespace SURELOG {
class CompileClass;

class ClassDefinition : public DesignComponent, public DataType {
  friend class CompileClass;

 public:
  ClassDefinition(std::string name, Library* library,
                  DesignComponent* container, FileContent* fC, NodeId nodeId,
                  ClassDefinition* parent);

  virtual ~ClassDefinition();

  unsigned int getSize();
  VObjectType getType() { return VObjectType::slClass_declaration; }
  bool isInstance() { return false; }
  std::string getName() { return m_name; }
  Library* getLibrary() { return m_library; }
  DesignComponent* getContainer() { return m_container; }
  void setContainer(DesignComponent* container) { m_container = container; }

  // Parameter definitions are stored DesignComponent maps
  typedef std::map<std::string, Property*> PropertyMap;
  typedef std::map<std::string, TaskMethod*> TaskMap;
  typedef std::map<std::string, Constraint*> ConstraintMap;
  typedef std::map<std::string, DataType*> BaseClassMap;
  typedef std::map<std::string, ClassDefinition*> ClassMap;
  typedef std::map<std::string, CoverGroupDefinition*> CoverGroupMap;
  typedef std::map<std::string, Parameter*> ParameterMap;

  PropertyMap& getPropertyMap() { return m_properties; }
  Property* getProperty(const std::string& name);
  void insertProperty(Property* p);

  Function* getFunction(const std::string& name);

  TaskMap& getTaskMap() { return m_tasks; }
  TaskMethod* getTask(const std::string& name);
  void insertTask(TaskMethod* p);

  ConstraintMap& getConstraintMap() { return m_constraints; }
  Constraint* getConstraint(const std::string& name);
  void insertConstraint(Constraint* p);

  // Nested classes
  ClassMap& getClassMap() { return m_classes; }
  ClassDefinition* getClass(const std::string& name);
  void insertClass(ClassDefinition* p);

  CoverGroupMap& getCoverGroupMap() { return m_covergroups; }
  CoverGroupDefinition* getCoverGroup(const std::string& name);
  void insertCoverGroup(CoverGroupDefinition* p);

  BaseClassMap& getBaseClassMap() { return m_baseclasses; }
  DataType* getBaseClass(const std::string& name);
  void insertBaseClass(DataType* p);

  ParameterMap& getParameterMap() { return m_parameters; }
  Parameter* getParameter(const std::string& name);
  void insertParameter(Parameter* p);

  DataType* getBaseDataType(std::string type);

  bool hasCompleteBaseSpecification();

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
  ParameterMap m_parameters;
};

};  // namespace SURELOG

#endif /* CLASSDEFINITION_H */
