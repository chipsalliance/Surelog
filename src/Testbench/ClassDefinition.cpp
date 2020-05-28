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
 * File:   ClassDefinition.cpp
 * Author: alain
 *
 * Created on June 1, 2018, 10:12 PM
 */
#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"
#include "ClassDefinition.h"

using namespace SURELOG;

ClassDefinition::ClassDefinition(std::string name, Library* library,
                                 DesignComponent* container, FileContent* fC,
                                 NodeId nodeId, ClassDefinition* parent)
    : DesignComponent(container ? container : fC, NULL),
      DataType(fC, nodeId, name,
               fC ? fC->Type(nodeId) : VObjectType::slClass_declaration),
      m_name(name),
      m_library(library),
      m_container(container),
      m_parent(parent) {
  addFileContent(fC, nodeId);
}

ClassDefinition::~ClassDefinition() {}

unsigned int ClassDefinition::getSize() {
  NodeId end = m_nodeIds[0];
  NodeId begin = m_fileContents[0]->Child(end);
  unsigned int size = end - begin;
  return size;
}

Property* ClassDefinition::getProperty(const std::string& name) {
  PropertyMap::iterator itr = m_properties.find(name);
  if (itr == m_properties.end()) {
    for (auto parent : getBaseClassMap()) {
      if (parent.second) {
        ClassDefinition* cparent =
            dynamic_cast<ClassDefinition*>(parent.second);
        if (cparent) {
          Property* d = cparent->getProperty(name);
          if (d) return d;
        }
      }
    }
    return NULL;
  } else {
    return (*itr).second;
  }
}

void ClassDefinition::insertProperty(Property* p) {
  m_properties.insert(std::make_pair(p->getName(), p));
}

Function* ClassDefinition::getFunction(const std::string& name) {
  FunctionMap::iterator itr = m_functions.find(name);
  if (itr != m_functions.end()) {
    return (*itr).second;
  }

  for (auto parent : getBaseClassMap()) {
    if (parent.second) {
      ClassDefinition* cparent = dynamic_cast<ClassDefinition*>(parent.second);
      if (cparent) {
        Function* d = cparent->getFunction(name);
        if (d) return d;
      }
    }
  }

  if (m_container) {
    return m_container->getFunction(name);
  }

  return NULL;
}

TaskMethod* ClassDefinition::getTask(const std::string& name) {
  TaskMap::iterator itr = m_tasks.find(name);
  if (itr == m_tasks.end()) {
    for (auto parent : getBaseClassMap()) {
      if (parent.second) {
        ClassDefinition* cparent =
            dynamic_cast<ClassDefinition*>(parent.second);
        if (cparent) {
          TaskMethod* d = cparent->getTask(name);
          if (d) return d;
        }
      }
    }
    return NULL;
  } else {
    return (*itr).second;
  }
}

void ClassDefinition::insertTask(TaskMethod* p) {
  m_tasks.insert(std::make_pair(p->getName(), p));
}

Constraint* ClassDefinition::getConstraint(const std::string& name) {
  ConstraintMap::iterator itr = m_constraints.find(name);
  if (itr == m_constraints.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

void ClassDefinition::insertConstraint(Constraint* p) {
  m_constraints.insert(std::make_pair(p->getName(), p));
}

ClassDefinition* ClassDefinition::getClass(const std::string& name) {
  ClassMap::iterator itr = m_classes.find(name);
  if (itr == m_classes.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

void ClassDefinition::insertClass(ClassDefinition* p) {
  m_classes.insert(std::make_pair(p->getName(), p));
}

CoverGroupDefinition* ClassDefinition::getCoverGroup(const std::string& name) {
  CoverGroupMap::iterator itr = m_covergroups.find(name);
  if (itr == m_covergroups.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

void ClassDefinition::insertCoverGroup(CoverGroupDefinition* p) {
  m_covergroups.insert(std::make_pair(p->getName(), p));
}

DataType* ClassDefinition::getBaseClass(const std::string& name) {
  BaseClassMap::iterator itr = m_baseclasses.find(name);
  if (itr == m_baseclasses.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

void ClassDefinition::insertBaseClass(DataType* p) {
  m_baseclasses.insert(std::make_pair(p->getName(), p));
}

Parameter* ClassDefinition::getParameter(const std::string& name) {
  ParameterMap::iterator itr = m_parameters.find(name);
  if (itr == m_parameters.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

void ClassDefinition::insertParameter(Parameter* p) {
  m_parameters.insert(std::make_pair(p->getName(), p));
}

DataType* ClassDefinition::getBaseDataType(std::string name) {
  DataTypeMap& dataTypes = getDataTypeMap();
  DataTypeMap::iterator itr = dataTypes.find(name);
  if (itr == dataTypes.end()) {
    for (auto parent : getBaseClassMap()) {
      if (parent.second) {
        ClassDefinition* cparent =
            dynamic_cast<ClassDefinition*>(parent.second);
        if (cparent) {
          DataType* d = cparent->getBaseDataType(name);
          if (d) return d;
        }
      }
    }
    return NULL;
  } else {
    return (*itr).second;
  }
}

bool ClassDefinition::hasCompleteBaseSpecification() {
  for (auto parent : getBaseClassMap()) {
    if (parent.second) {
      ClassDefinition* cparent = dynamic_cast<ClassDefinition*>(parent.second);
      if (cparent) {
        return cparent->hasCompleteBaseSpecification();
      }
      Parameter* param = dynamic_cast<Parameter*>(parent.second);
      if (param) return false;
    }
  }
  return true;
}
