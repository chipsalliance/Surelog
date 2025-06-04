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
#include "Surelog/Design/ModuleInstance.h"

/*
 * File:   ModuleInstance.cpp
 * Author: alain
 *
 * Created on October 16, 2017, 10:48 PM
 */

#include <uhdm/expr.h>
#include <uhdm/uhdm_types.h>

#include <cstdint>
#include <set>
#include <string_view>
#include <vector>

#include "Surelog/Common/SymbolId.h"
#include "Surelog/Design/DesignComponent.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/Netlist.h"
#include "Surelog/Expression/ExprBuilder.h"
#include "Surelog/Expression/Value.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"

// UHDM
#include <uhdm/ExprEval.h>
#include <uhdm/constant.h>
#include <uhdm/param_assign.h>
#include <uhdm/ref_obj.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_visitor.h>

namespace SURELOG {
ModuleInstance::ModuleInstance(Session* session,
                               DesignComponent* moduleDefinition,
                               const FileContent* fileContent, NodeId nodeId,
                               ModuleInstance* parent,
                               std::string_view instName,
                               std::string_view modName)
    : ValuedComponentI(session, parent, moduleDefinition),
      m_definition(moduleDefinition),
      m_fileContent(fileContent),
      m_nodeId(nodeId),
      m_parent(parent),
      m_instName(instName),
      m_netlist(nullptr) {
  if (m_definition == nullptr) {
    m_instName = modName;
    m_instName.append("&").append(instName);
  }
}

uhdm::Expr* ModuleInstance::getComplexValue(std::string_view name) const {
  ModuleInstance* instance = (ModuleInstance*)this;
  while (instance) {
    uhdm::Expr* res = ValuedComponentI::getComplexValue(name);
    if (res) {
      return res;
    }

    if (instance->m_netlist) {
      uhdm::ParamAssignCollection* param_assigns =
          instance->m_netlist->param_assigns();
      if (param_assigns) {
        for (uhdm::ParamAssign* param : *param_assigns) {
          if (param && param->getLhs()) {
            const std::string_view param_name = param->getLhs()->getName();
            if (param_name == name) {
              const uhdm::Any* exp = param->getRhs();
              if (exp) return (uhdm::Expr*)exp;
            }
          }
        }
      }
    }

    if (instance->getType() != VObjectType::paModule_instantiation)
      instance = instance->getParent();
    else
      instance = nullptr;
  }
  return nullptr;
}

const uhdm::Constant* resolveFromParamAssign(
    const uhdm::ParamAssignCollection* param_assigns,
    std::set<std::string>& visited, const std::string_view& name) {
  std::string s(name);
  if (visited.find(s) != visited.end()) {
    return nullptr;
  }
  visited.insert(std::string(name));
  for (uhdm::ParamAssign* param : *param_assigns) {
    const std::string_view param_name = param->getLhs()->getName();
    if (param_name == name) {
      const uhdm::Any* exp = param->getRhs();
      if (exp) {
        if (exp->getUhdmType() == uhdm::UhdmType::Constant) {
          return (uhdm::Constant*)exp;
        } else if (exp->getUhdmType() == uhdm::UhdmType::RefObj) {
          uhdm::RefObj* ref = (uhdm::RefObj*)exp;
          const std::string_view ref_name = ref->getName();
          return resolveFromParamAssign(param_assigns, visited, ref_name);
        }
      }
    }
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
      uhdm::ParamAssignCollection* param_assigns =
          instance->m_netlist->param_assigns();
      if (param_assigns) {
        std::set<std::string> visited;
        const uhdm::Constant* res =
            resolveFromParamAssign(param_assigns, visited, name);
        if (res) {
          sval = exprBuilder.fromVpiValue(res->getValue(), res->getSize());
          break;
        }
      }
    }

    if (instance->getType() != VObjectType::paModule_instantiation)
      instance = instance->getParent();
    else
      instance = nullptr;
  }

  if (sval == nullptr) {
    sval = ValuedComponentI::getValue(name);
  }

  if (m_definition && (sval == nullptr)) {
    uhdm::ParamAssignCollection* param_assigns =
        m_definition->getParamAssigns();
    if (param_assigns) {
      std::set<std::string> visited;
      const uhdm::Constant* res =
          resolveFromParamAssign(param_assigns, visited, name);
      if (res) {
        sval = exprBuilder.fromVpiValue(res->getValue(), res->getSize());
      }
    }
  }

  return sval;
}

ModuleInstance* ModuleInstance::getChildByName(std::string_view name) {
  for (auto child : m_allSubInstances) {
    if (child->getInstanceName() == name) return child;
  }
  return nullptr;
}

std::string ModuleInstance::decompile(char* valueName) {
  ExprBuilder exprBuilder(m_session);
  Value* val = getValue(valueName, exprBuilder);
  if (val) {
    return val->uhdmValue();
  }
  if (uhdm::Expr* complex = getComplexValue(valueName)) {
    return uhdm::decompile(complex);
  } else {
    return "Undefined";
  }
}

ModuleInstance::~ModuleInstance() {
  delete m_netlist;
  for (auto child : m_allSubInstances) {
    delete child;
  }
}

void ModuleInstance::addSubInstance(ModuleInstance* subInstance) {
  m_allSubInstances.push_back(subInstance);
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

PathId ModuleInstance::getFileId() const {
  return m_fileContent->getFileId(m_nodeId);
}

uint32_t ModuleInstance::getLineNb() const {
  return m_fileContent->Line(m_nodeId);
}

uint16_t ModuleInstance::getColumnNb() const {
  return m_fileContent->Column(m_nodeId);
}

uint32_t ModuleInstance::getEndLineNb() const {
  return m_fileContent->EndLine(m_nodeId);
}

uint16_t ModuleInstance::getEndColumnNb() const {
  return m_fileContent->EndColumn(m_nodeId);
}

SymbolId ModuleInstance::getFullPathId(SymbolTable* symbols) const {
  return symbols->registerSymbol(getFullPathName());
}

SymbolId ModuleInstance::getInstanceId(SymbolTable* symbols) const {
  return symbols->registerSymbol(getInstanceName());
}
SymbolId ModuleInstance::getModuleNameId(SymbolTable* symbols) const {
  return symbols->registerSymbol(getModuleName());
}

std::string ModuleInstance::getFullPathName() const {
  std::string path;
  const ModuleInstance* tmp = this;
  std::vector<std::string> nibbles;
  while (tmp) {
    nibbles.push_back(tmp->getInstanceName());
    tmp = tmp->getParent();
  }
  for (int32_t i = nibbles.size() - 1; i >= 0; i--) {
    path += nibbles[i];
    if (i > 0) {
      path += ".";
    }
  }
  return path;
}

uint32_t ModuleInstance::getDepth() const {
  uint32_t depth = 0;
  const ModuleInstance* tmp = this;
  while (tmp) {
    tmp = tmp->getParent();
    depth++;
  }
  return depth;
}

std::string ModuleInstance::getInstanceName() const {
  if (m_definition == nullptr) {
    std::string name =
        m_instName.substr(m_instName.find("&", 0, 1) + 1, m_instName.size());
    return name;
  } else {
    return m_instName;
  }
}

std::string_view ModuleInstance::getModuleName() const {
  if (m_definition == nullptr) {
    return std::string_view(m_instName).substr(0, m_instName.find("&", 0, 1));
  } else {
    return m_definition->getName();
  }
}

void ModuleInstance::overrideParentChild(ModuleInstance* parent,
                                         ModuleInstance* interm,
                                         ModuleInstance* child,
                                         uhdm::Serializer& s) {
  if (parent != this) return;
  Netlist* netlist = interm->getNetlist();
  if (netlist) {
    if (netlist->cont_assigns() || netlist->process_stmts() ||
        netlist->array_nets() || netlist->param_assigns() ||
        netlist->array_vars() || netlist->nets() || netlist->variables() ||
        netlist->interface_arrays() || netlist->interfaces())
      return;
  }

  Netlist* child_netlist = child->getNetlist();
  if (netlist->param_assigns()) {
    auto params = child_netlist->param_assigns();
    if (params == nullptr) {
      params = s.makeCollection<uhdm::ParamAssign>();
      child_netlist->param_assigns(params);
    }
    for (auto p : *netlist->param_assigns()) {
      params->push_back(p);
    }
  }

  // Loop indexes
  for (auto& param : interm->getMappedValues()) {
    const std::string_view name = param.first;
    Value* val = param.second.first;
    auto params = child_netlist->param_assigns();
    if (params == nullptr) {
      params = s.makeCollection<uhdm::ParamAssign>();
      child_netlist->param_assigns(params);
    }
    bool found = false;
    for (auto p : *params) {
      if (p->getName() == name) {
        found = true;
        break;
      }
    }
    if (!found) {
      uhdm::Parameter* p = s.make<uhdm::Parameter>();
      p->setName(name);
      if (val && val->isValid()) p->setValue(val->uhdmValue());
      p->setStartLine(param.second.second);
      p->setLocalParam(true);
      uhdm::IntTypespec* ts = s.make<uhdm::IntTypespec>();
      uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
      rt->setParent(p);
      p->setTypespec(rt);
      rt->setActual(ts);
      uhdm::ParamAssign* pass = s.make<uhdm::ParamAssign>();
      pass->setLhs(p);
      uhdm::Constant* c = s.make<uhdm::Constant>();
      c->setValue(val->uhdmValue());
      pass->setRhs(c);
      params->push_back(pass);
    }
  }

  child->m_parent = this;
  std::vector<ModuleInstance*> children;

  for (ModuleInstance* sub_instance : m_allSubInstances) {
    if (sub_instance == interm) {
      for (ModuleInstance* interm_subinstance : interm->m_allSubInstances) {
        children.push_back(interm_subinstance);
      }
    } else {
      children.push_back(sub_instance);
    }
  }

  m_allSubInstances = children;
}

void ModuleInstance::setOverridenParam(std::string_view name) {
  m_overridenParams.emplace(name);
}

bool ModuleInstance::isOverridenParam(std::string_view name) const {
  if (m_overridenParams.find(name) == m_overridenParams.end()) return false;
  return true;
}

}  // namespace SURELOG
