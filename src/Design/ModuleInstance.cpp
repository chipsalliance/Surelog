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
 * File:   ModuleInstance.cpp
 * Author: alain
 *
 * Created on October 16, 2017, 10:48 PM
 */
#include "Design/ModuleInstance.h"

#include <iostream>
#include <string>

#include "Design/FileContent.h"
#include "Library/Library.h"
#include "SourceCompile/SymbolTable.h"

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/clone_tree.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_visitor.h>

using UHDM::any;
using UHDM::constant;
using UHDM::param_assign;
using UHDM::uhdmconstant;

namespace SURELOG {
ModuleInstance::ModuleInstance(DesignComponent* moduleDefinition,
                               const FileContent* fileContent, NodeId nodeId,
                               ModuleInstance* parent,
                               std::string_view instName,
                               std::string_view modName)
    : ValuedComponentI(parent, moduleDefinition),
      m_definition(moduleDefinition),
      m_fileContent(fileContent),
      m_nodeId(nodeId),
      m_parent(parent),
      m_instName(instName),
      m_netlist(nullptr) {
  if (m_definition == NULL) {
    m_instName.assign(modName).append("&").append(instName);
  }
}

UHDM::expr* ModuleInstance::getComplexValue(std::string_view name) const {
  ModuleInstance* instance = (ModuleInstance*)this;
  while (instance) {
    UHDM::expr* res = ValuedComponentI::getComplexValue(name);
    if (res) {
      return res;
    }

    if (instance->m_netlist) {
      UHDM::VectorOfparam_assign* param_assigns =
          instance->m_netlist->param_assigns();
      if (param_assigns) {
        for (param_assign* param : *param_assigns) {
          if (param && param->Lhs()) {
            const std::string_view param_name = param->Lhs()->VpiName();
            if (param_name == name) {
              const any* exp = param->Rhs();
              if (exp) return (UHDM::expr*)exp;
            }
          }
        }
      }
    }

    if (instance->getType() != slModule_instantiation)
      instance = instance->getParent();
    else
      instance = nullptr;
  }
  return nullptr;
}

Value* ModuleInstance::getValue(std::string_view name,
                                ExprBuilder& exprBuilder) const {
  Value* sval = nullptr;

  if (ValuedComponentI::getComplexValue(
          name)) {  // Only check current instance level
    return nullptr;
  }

  ModuleInstance* instance = (ModuleInstance*)this;
  while (instance) {
    if (instance->m_netlist) {
      UHDM::VectorOfparam_assign* param_assigns =
          instance->m_netlist->param_assigns();
      if (param_assigns) {
        for (param_assign* param : *param_assigns) {
          if (param && param->Lhs()) {
            const std::string_view param_name = param->Lhs()->VpiName();
            if (param_name == name) {
              const any* exp = param->Rhs();
              if (exp && exp->UhdmType() == uhdmconstant) {
                constant* c = (constant*)exp;
                sval = exprBuilder.fromVpiValue(std::string(c->VpiValue()),
                                                c->VpiSize());
              }
              break;
            }
          }
        }
      }
    }

    if (instance->getType() != slModule_instantiation)
      instance = instance->getParent();
    else
      instance = nullptr;
  }

  if (sval == nullptr) {
    sval = ValuedComponentI::getValue(name);
  }

  if (m_definition && (sval == nullptr)) {
    UHDM::VectorOfparam_assign* param_assigns =
        m_definition->getParam_assigns();
    if (param_assigns) {
      for (param_assign* param : *param_assigns) {
        const std::string_view param_name = param->Lhs()->VpiName();
        if (param_name == name) {
          const any* exp = param->Rhs();
          if (exp && (exp->UhdmType() == uhdmconstant)) {
            constant* c = (constant*)exp;
            sval = exprBuilder.fromVpiValue(c->VpiValue(), c->VpiSize());
          }
          break;
        }
      }
    }
  }

  return sval;
}

std::string ModuleInstance::decompile(char* valueName) {
  ExprBuilder exprBuilder;
  Value* val = getValue(valueName, exprBuilder);
  if (val) {
    return val->uhdmValue();
  }
  if (UHDM::expr* complex = getComplexValue(valueName)) {
    return UHDM::decompile(complex);
  } else {
    return "Undefined";
  }
}

ModuleInstance::~ModuleInstance() {
  delete m_netlist;
  for (unsigned int index = 0; index < m_allSubInstances.size(); index++) {
    delete m_allSubInstances[index];
  }
}

void ModuleInstance::addSubInstance(ModuleInstance* subInstance) {
  m_allSubInstances.push_back(subInstance);
}

ModuleInstance* ModuleInstanceFactory::newModuleInstance(
    DesignComponent* moduleDefinition, const FileContent* fileContent,
    NodeId nodeId, ModuleInstance* parent, std::string_view instName,
    std::string_view modName) {
  return new ModuleInstance(moduleDefinition, fileContent, nodeId, parent,
                            instName, modName);
}

VObjectType ModuleInstance::getType() const {
  return m_fileContent->Type(m_nodeId);
}

VObjectType ModuleInstance::getModuleType() const {
  VObjectType type = (VObjectType)0;
  if (m_definition) {
    type = m_definition->getType();
  }
  return type;
}

unsigned int ModuleInstance::getLineNb() const {
  return m_fileContent->Line(m_nodeId);
}

unsigned short ModuleInstance::getColumnNb() const {
  return m_fileContent->Column(m_nodeId);
}

unsigned int ModuleInstance::getEndLineNb() const {
  return m_fileContent->EndLine(m_nodeId);
}

unsigned short ModuleInstance::getEndColumnNb() const {
  return m_fileContent->EndColumn(m_nodeId);
}

SymbolId ModuleInstance::getFullPathId(SymbolTable* symbols) {
  return symbols->registerSymbol(getFullPathName());
}

SymbolId ModuleInstance::getInstanceId(SymbolTable* symbols) {
  return symbols->registerSymbol(getInstanceName());
}
SymbolId ModuleInstance::getModuleNameId(SymbolTable* symbols) {
  return symbols->registerSymbol(getModuleName());
}

std::string ModuleInstance::getFullPathName() {
  std::string path;
  ModuleInstance* tmp = this;
  std::vector<std::string> nibbles;
  while (tmp) {
    nibbles.push_back(tmp->getInstanceName());
    tmp = tmp->getParent();
  }
  for (int i = nibbles.size() - 1; i >= 0; i--) {
    path += nibbles[i];
    if (i > 0) {
      path += ".";
    }
  }
  return path;
}

unsigned int ModuleInstance::getDepth() const {
  unsigned int depth = 0;
  const ModuleInstance* tmp = this;
  while (tmp) {
    tmp = tmp->getParent();
    depth++;
  }
  return depth;
}

std::string ModuleInstance::getInstanceName() const {
  if (m_definition == NULL) {
    std::string name =
        m_instName.substr(m_instName.find("&", 0, 1) + 1, m_instName.size());
    return name;
  } else {
    return m_instName;
  }
}

std::string ModuleInstance::getModuleName() const {
  if (m_definition == NULL) {
    std::string name = m_instName.substr(0, m_instName.find("&", 0, 1));
    return name;
  } else {
    return m_definition->getName().data();
  }
}

void ModuleInstance::overrideParentChild(ModuleInstance* parent,
                                         ModuleInstance* interm,
                                         ModuleInstance* child) {
  if (parent != this) return;
  child->m_parent = this;
  std::vector<ModuleInstance*> children;

  for (unsigned int i = 0; i < m_allSubInstances.size(); i++) {
    if (m_allSubInstances[i] == interm) {
      for (unsigned int j = 0; j < interm->m_allSubInstances.size(); j++) {
        children.push_back(interm->m_allSubInstances[j]);
      }
    } else {
      children.push_back(m_allSubInstances[i]);
    }
  }

  m_allSubInstances = children;
}

void ModuleInstance::setOverridenParam(std::string_view name) {
  m_overridenParams.insert(name.data());
}

bool ModuleInstance::isOverridenParam(std::string_view name) const {
  return (m_overridenParams.find(name) != m_overridenParams.end());
}

}  // namespace SURELOG
