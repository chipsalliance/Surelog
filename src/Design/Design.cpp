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
#include "Surelog/Design/Design.h"

/*
 * File:   Design.cpp
 * Author: alain
 *
 * Created on July 1, 2017, 1:23 PM
 */

#include <uhdm/design.h>

#include <cstdint>
#include <iterator>
#include <map>
#include <queue>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Design/DefParam.h"
#include "Surelog/Design/DesignComponent.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/ValuedComponentI.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Expression/Value.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Testbench/Program.h"
#include "Surelog/Utils/StringUtils.h"

namespace SURELOG {

Design::Design(Session* session, uhdm::Serializer& serializer,
               LibrarySet* librarySet, ConfigSet* configSet)
    : m_session(session),
      m_uhdmDesign(serializer.make<uhdm::Design>()),
      m_librarySet(librarySet),
      m_configSet(configSet) {}

Design::~Design() {
  for (const auto& elem : m_ppFileContents) {
    delete elem.second;
  }
  for (const auto& elem : m_fileContents) {
    delete elem.second;
  }
  for (const auto& elem : m_moduleDefinitions) {
    delete elem.second;
  }
  for (auto elem : m_topLevelModuleInstances) {
    delete elem;
  }
  for (auto elem : m_orderedPackageDefinitions) {
    delete elem;
  }
  for (const auto& elem : m_programDefinitions) {
    delete elem.second;
  }
  for (const auto& elem : m_uniqueClassDefinitions) {
    delete elem.second;
  }
}

void Design::addFileContent(PathId fileId, FileContent* content) {
  m_mutex.lock();
  m_fileContents.emplace_back(fileId, content);
  m_mutex.unlock();
}

void Design::addPPFileContent(PathId fileId, FileContent* content) {
  m_mutex.lock();
  m_ppFileContents.emplace_back(fileId, content);
  m_mutex.unlock();
}

DesignComponent* Design::getComponentDefinition(
    std::string_view componentName) const {
  if (DesignComponent* const dc = getPackage(componentName)) {
    return dc;
  } else if (DesignComponent* const dc = getModuleDefinition(componentName)) {
    return dc;
  } else if (DesignComponent* const dc = getProgram(componentName)) {
    return dc;
  } else if (DesignComponent* const dc = getClassDefinition(componentName)) {
    return dc;
  }
  return nullptr;
}

ModuleDefinition* Design::getModuleDefinition(
    std::string_view moduleName) const {
  ModuleNameModuleDefinitionMap::const_iterator itr =
      m_moduleDefinitions.find(moduleName);
  if (itr != m_moduleDefinitions.end()) {
    return itr->second;
  }
  return nullptr;
}

std::string Design::reportInstanceTree() const {
  std::string tree;
  ModuleInstance* tmp;
  std::queue<ModuleInstance*> queue;
  ErrorContainer* const errors = m_session->getErrorContainer();
  SymbolTable* const symbols = m_session->getSymbolTable();
  for (auto instance : m_topLevelModuleInstances) {
    queue.push(instance);
  }
  while (!queue.empty()) {
    tmp = queue.front();
    queue.pop();
    if (tmp->getNbChildren()) {
      for (uint32_t i = 0; i < tmp->getNbChildren(); i++) {
        queue.push(tmp->getChildren(i));
      }
    }
    std::string def;
    def = tmp->getModuleName();
    std::string undef;
    VObjectType type = tmp->getType();
    if (tmp->getDefinition() == nullptr) {
      undef = " [U]";
    }
    std::string type_s;
    Location loc(tmp->getFileId(), tmp->getLineNb(), tmp->getColumnNb(),
                 tmp->getFullPathId(symbols));
    if (type == VObjectType::paUdp_instantiation) {
      type_s = "[UDP]";
      Error err(ErrorDefinition::ELAB_INSTANCE_PATH, loc);
      errors->addError(err);
    } else if (type == VObjectType::paModule_instantiation) {
      type_s = "[MOD]";
      Error err(ErrorDefinition::ELAB_INSTANCE_PATH, loc);
      errors->addError(err);
    } else if ((type == VObjectType::paCmos_switch_instance) ||
               (type == VObjectType::paEnable_gate_instance) ||
               (type == VObjectType::paMos_switch_instance) ||
               (type == VObjectType::paN_input_gate_instance) ||
               (type == VObjectType::paN_output_gate_instance) ||
               (type == VObjectType::paPass_enable_switch_instance) ||
               (type == VObjectType::paPass_switch_instance) ||
               (type == VObjectType::paPull_gate_instance)) {
      type_s = "[GAT]";
      Error err(ErrorDefinition::ELAB_INSTANCE_PATH, loc);
      errors->addError(err);
    } else if (type == VObjectType::paInterface_instantiation) {
      type_s = "[I/F]";
      Error err(ErrorDefinition::ELAB_INTERFACE_INSTANCE_PATH, loc);
      errors->addError(err);
    } else if (type == VObjectType::paProgram_instantiation) {
      type_s = "[PRG]";
      Error err(ErrorDefinition::ELAB_PROGRAM_INSTANCE_PATH, loc);
      errors->addError(err);
    } else if (type == VObjectType::paModule_declaration) {
      type_s = "[TOP]";
      Error err(ErrorDefinition::ELAB_INSTANCE_PATH, loc);
      errors->addError(err);
    } else {
      type_s = "[SCO]";
      Error err(ErrorDefinition::ELAB_SCOPE_PATH, loc);
      errors->addError(err);
    }

    StrAppend(&tree, type_s, " ", def, undef, " ", tmp->getFullPathName(),
              "\n");

    bool extraInfo = false;
    if (extraInfo) {
      // Extra debug info:
      if (tmp) {
        ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(tmp);
        if (inst) {
          for (const auto& ps : inst->getMappedValues()) {
            const std::string& name = ps.first;
            Value* val = ps.second.first;
            StrAppend(&tree, "    ", name, " = ", val->uhdmValue(), "\n");
          }
          for (const auto& ps : inst->getComplexValues()) {
            const std::string& name = ps.first;
            StrAppend(&tree, "    ", name, " = ", "complex", "\n");
          }
        }
      }
    }
  }

  return tree;
}

void Design::reportInstanceTreeStats(uint32_t& nbTopLevelModules,
                                     uint32_t& maxDepth,
                                     uint32_t& numberOfInstances,
                                     uint32_t& numberOfLeafInstances,
                                     uint32_t& nbUndefinedModules,
                                     uint32_t& nbUndefinedInstances) const {
  nbTopLevelModules = 0;
  maxDepth = 0;
  numberOfInstances = 0;
  numberOfLeafInstances = 0;
  nbUndefinedModules = 0;
  nbUndefinedInstances = 0;
  std::set<std::string_view> undefModules;
  ModuleInstance* tmp;
  std::queue<ModuleInstance*> queue;
  for (auto instance : m_topLevelModuleInstances) {
    queue.push(instance);
    nbTopLevelModules++;
  }
  while (!queue.empty()) {
    tmp = queue.front();
    queue.pop();
    bool isInstance = false;
    if (!tmp->getDefinition())
      isInstance = true;
    else {
      isInstance = tmp->getDefinition()->isInstance();
    }

    if (isInstance) {
      numberOfInstances++;
      uint32_t depth = tmp->getDepth();
      if (depth > maxDepth) {
        maxDepth = depth;
      }
    }
    if (tmp->getNbChildren()) {
      for (uint32_t i = 0; i < tmp->getNbChildren(); i++) {
        queue.push(tmp->getChildren(i));
      }
    } else {
      if (isInstance) numberOfLeafInstances++;
    }
    std::string def;
    if (tmp->getDefinition()) {
    } else {
      nbUndefinedInstances++;
      undefModules.emplace(tmp->getModuleName());
    }
  }

  nbUndefinedModules = undefModules.size();
}

ModuleInstance* Design::findInstance(std::string_view path,
                                     ModuleInstance* scope) const {
  std::vector<std::string> vpath;
  StringUtils::tokenize(path, ".", vpath);
  return findInstance(vpath, scope);
}

ModuleInstance* Design::findInstance(const std::vector<std::string>& path,
                                     ModuleInstance* scope) const {
  if (path.empty()) return nullptr;
  if (scope) {
    ModuleInstance* res = findInstance_(path, scope);
    if (res) return res;
  } else {
    for (auto top : m_topLevelModuleInstances) {
      if (path.size() == 1) {
        if (top->getInstanceName() == path[0]) {
          return top;
        }
      } else {
        if (top->getInstanceName() == path[0]) {
          std::vector<std::string> subpath = path;
          subpath.erase(subpath.begin());
          ModuleInstance* res = findInstance_(subpath, top);
          if (res) return res;
        }
      }
    }
  }

  return nullptr;
}

ModuleInstance* Design::findInstance_(const std::vector<std::string>& path,
                                      ModuleInstance* scope) const {
  if (path.empty()) return nullptr;
  if (scope == nullptr) return nullptr;
  if (path.size() == 1) {
    if (scope->getInstanceName() == path[0]) {
      return scope;
    }
  }

  for (uint32_t i = 0; i < scope->getNbChildren(); i++) {
    ModuleInstance* child = scope->getChildren(i);
    if (path.empty()) continue;
    if (child->getInstanceName() == path[0]) {
      if (path.size() == 1) {
        return child;
      } else {
        std::vector<std::string> subpath = path;
        subpath.erase(subpath.begin());
        ModuleInstance* res = findInstance(subpath, child);
        if (res) return res;
      }
    }
  }
  return nullptr;
}

DefParam* Design::getDefParam(std::string_view name) const {
  std::vector<std::string> vpath;
  StringUtils::tokenize(name, ".", vpath);
  std::map<std::string, DefParam*>::const_iterator itr =
      m_defParams.find(vpath[0]);
  if (itr != m_defParams.end()) {
    vpath.erase(vpath.begin());
    return getDefParam_(vpath, itr->second);
  }
  return nullptr;
}

Value* Design::getDefParamValue(std::string_view name) {
  DefParam* def = getDefParam(name);
  if (def) return def->getValue();
  return nullptr;
}

DefParam* Design::getDefParam_(std::vector<std::string>& path,
                               DefParam* parent) const {
  if (path.empty()) {
    return parent;
  }
  std::map<std::string, DefParam*>::iterator itr =
      parent->getChildren().find(path[0]);
  if (itr != parent->getChildren().end()) {
    path.erase(path.begin());
    return getDefParam_(path, itr->second);
  }
  return nullptr;
}

void Design::addDefParam(std::string_view name, const FileContent* fC,
                         NodeId nodeId, Value* value) {
  std::vector<std::string> vpath;
  StringUtils::tokenize(name, ".", vpath);
  std::map<std::string, DefParam*>::iterator itr = m_defParams.find(vpath[0]);
  if (itr != m_defParams.end()) {
    vpath.erase(vpath.begin());
    addDefParam_(vpath, fC, nodeId, value, itr->second);
  } else {
    DefParam* def = new DefParam(vpath[0]);
    m_defParams.emplace(vpath[0], def);
    vpath.erase(vpath.begin());
    addDefParam_(vpath, fC, nodeId, value, def);
  }
}

void Design::addDefParam_(std::vector<std::string>& path, const FileContent* fC,
                          NodeId nodeId, Value* value, DefParam* parent) {
  if (path.empty()) {
    parent->setValue(value);
    parent->setLocation(fC, nodeId);
    return;
  }
  ErrorContainer* const errors = m_session->getErrorContainer();
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  std::map<std::string, DefParam*>::iterator itr =
      parent->getChildren().find(path[0]);
  if (itr != parent->getChildren().end()) {
    path.erase(path.begin());
    if (path.empty()) {
      DefParam* previous = itr->second;
      if (!fC->getFileId(nodeId).equals(
              previous->getLocation()->getFileId(previous->getNodeId()),
              fileSystem) ||
          (fC->Line(nodeId) !=
           previous->getLocation()->Line(previous->getNodeId()))) {
        Location loc1(fC->getFileId(nodeId), fC->Line(nodeId),
                      fC->Column(nodeId),
                      symbols->registerSymbol(previous->getFullName()));
        Location loc2(previous->getLocation()->getFileId(previous->getNodeId()),
                      previous->getLocation()->Line(previous->getNodeId()),
                      previous->getLocation()->Column(previous->getNodeId()));
        Error err(ErrorDefinition::ELAB_MULTI_DEFPARAM_ON_OBJECT, loc1, loc2);
        errors->addError(err);
      }
    }
    addDefParam_(path, fC, nodeId, value, itr->second);
  } else {
    DefParam* def = new DefParam(path[0], parent);
    parent->setChild(path[0], def);
    path.erase(path.begin());
    addDefParam_(path, fC, nodeId, value, def);
  }
}

void Design::checkDefParamUsage(DefParam* parent) {
  ErrorContainer* const errors = m_session->getErrorContainer();
  SymbolTable* const symbols = m_session->getSymbolTable();
  if (parent == nullptr) {
    // Start by all the top defs of the trie
    for (const auto& top : m_defParams) {
      checkDefParamUsage(top.second);
    }
  } else {
    // Check the leaf
    if (parent->getValue() && (!parent->isUsed())) {
      if (parent->getParent()) {
        ModuleInstance* inst = findInstance(parent->getParent()->getFullName());
        if (inst && (!inst->getDefinition())) {
          return;
        } else {
        }
      } else {
        return;
      }

      Location loc(parent->getLocation()->getFileId(parent->getNodeId()),
                   parent->getLocation()->Line(parent->getNodeId()),
                   parent->getLocation()->Column(parent->getNodeId()),
                   symbols->registerSymbol(parent->getFullName()));
      Error err(ErrorDefinition::ELAB_UNMATCHED_DEFPARAM, loc);
      errors->addError(err);
    }
    for (const auto& param : parent->getChildren()) {
      checkDefParamUsage(param.second);
    }
  }
}

Package* Design::getPackage(std::string_view name) const {
  PackageNamePackageDefinitionMultiMap::const_iterator itr =
      m_packageDefinitions.find(name);
  if (itr == m_packageDefinitions.end()) {
    return nullptr;
  } else {
    return itr->second;
  }
}

Program* Design::getProgram(std::string_view name) const {
  ProgramNameProgramDefinitionMap::const_iterator itr =
      m_programDefinitions.find(name);
  if (itr == m_programDefinitions.end()) {
    return nullptr;
  } else {
    return itr->second;
  }
}

ClassDefinition* Design::getClassDefinition(std::string_view name) const {
  ClassNameClassDefinitionMap::const_iterator itr =
      m_uniqueClassDefinitions.find(name);
  if (itr == m_uniqueClassDefinitions.end()) {
    return nullptr;
  } else {
    return itr->second;
  }
}

void Design::orderPackages() {
  if (m_orderedPackageNames.empty()) return;
  m_orderedPackageDefinitions.resize(m_orderedPackageNames.size());
  uint32_t index = 0;
  typedef std::map<std::string, int32_t> MultiDefCount;
  MultiDefCount multiDefCount;
  for (const auto& packageName : m_orderedPackageNames) {
    for (uint32_t i = 0; i < m_packageDefinitions.size(); i++) {
      PackageNamePackageDefinitionMultiMap::iterator pos =
          m_packageDefinitions.begin();
      std::advance(pos, i);

      if (packageName == pos->first) {
        MultiDefCount::iterator itr = multiDefCount.find(packageName);
        if (itr == multiDefCount.end()) {
          multiDefCount.emplace(packageName, 1);
        } else {
          int32_t level = itr->second++;
          pos = m_packageDefinitions.begin();
          std::advance(pos, i + level);
        }
        m_orderedPackageDefinitions[index] = pos->second;
        index++;
        break;
      }
    }
  }
}

Package* Design::addPackageDefinition(std::string_view packageName,
                                      Package* package) {
  PackageNamePackageDefinitionMultiMap::iterator itr =
      m_packageDefinitions.find(packageName);
  if (itr == m_packageDefinitions.end()) {
    m_packageDefinitions.emplace(packageName, package);
    return package;
  } else {
    Package* old = itr->second;
    if (old->getFileContents()[0]->getParent() &&
        (old->getFileContents()[0]->getParent() ==
         package->getFileContents()[0]->getParent())) {
      old->append(package);
      return old;
    } else {
      m_packageDefinitions.emplace(packageName, package);
      return package;
    }
  }
}

void Design::addClassDefinition(std::string_view className,
                                ClassDefinition* classDef) {
  if (m_uniqueClassDefinitions.emplace(className, classDef).second) {
    m_classDefinitions.emplace(className, classDef);
  }
}

void Design::clearContainers() {
  m_moduleDefinitions.clear();

  m_topLevelModuleInstances.clear();

  m_defParams.clear();

  m_packageDefinitions.clear();

  // Do not clear, this is computed in a specific pass once
  // m_orderedPackageDefinitions.clear();

  m_programDefinitions.clear();

  m_classDefinitions.clear();

  m_uniqueClassDefinitions.clear();

  m_orderedPackageNames.clear();
}

std::vector<BindStmt*> Design::getBindStmts(std::string_view targetName) {
  std::vector<BindStmt*> results;
  BindMap::iterator itr = m_bindMap.find(targetName);
  while (itr != m_bindMap.end()) {
    if (itr->first != targetName) {
      break;
    }
    results.emplace_back(itr->second);
    itr++;
  }
  return results;
}

void Design::addBindStmt(std::string_view targetName, BindStmt* stmt) {
  m_bindMap.emplace(targetName, stmt);
}

vpiHandle Design::getVpiDesign() const {
  if (m_uhdmDesign != nullptr) {
    return m_uhdmDesign->getSerializer()->makeUhdmHandle(uhdm::UhdmType::Design,
                                                         m_uhdmDesign);
  }
  return nullptr;
}
}  // namespace SURELOG
