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
 * File:   Design.cpp
 * Author: alain
 *
 * Created on July 1, 2017, 1:23 PM
 */
#include <queue>
#include <set>
#include "Utils/StringUtils.h"
#include "SourceCompile/VObjectTypes.h"
#include "Design/VObject.h"
#include "Design/FileContent.h"
#include "SourceCompile/SymbolTable.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/ErrorContainer.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "CommandLine/CommandLineParser.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/ParseFile.h"
#include "Utils/FileUtils.h"
#include "Design/Design.h"
#include "Testbench/ClassDefinition.h"

using namespace SURELOG;

static std::mutex m;
void Design::addFileContent(SymbolId fileId, FileContent* content) {
  m.lock();
  m_fileContents.push_back(std::make_pair(fileId, content));
  m.unlock();
}

void Design::addPPFileContent(SymbolId fileId, FileContent* content) {
  m.lock();
  m_ppFileContents.push_back(std::make_pair(fileId, content));
  m.unlock();
}

DesignComponent* Design::getComponentDefinition(
    const std::string& componentName) {
  DesignComponent* comp = (DesignComponent*)getModuleDefinition(componentName);
  if (comp) return comp;
  comp = (DesignComponent*)getProgram(componentName);
  if (comp) return comp;
  comp = (DesignComponent*)getClassDefinition(componentName);
  if (comp) return comp;
  return NULL;
}

ModuleDefinition* Design::getModuleDefinition(const std::string& moduleName) {
  ModuleNameModuleDefinitionMap::iterator itr =
      m_moduleDefinitions.find(moduleName);
  if (itr != m_moduleDefinitions.end()) {
    return (*itr).second;
  }
  return NULL;
}

std::string Design::reportInstanceTree() const {
  std::string tree;
  ModuleInstance* tmp;
  std::queue<ModuleInstance*> queue;
  SymbolTable* symbols = m_errors->getSymbolTable();
  for (auto instance : m_topLevelModuleInstances) {
    queue.push(instance);
  }
  while (!queue.empty()) {
    tmp = queue.front();
    queue.pop();
    if (tmp->getNbChildren()) {
      for (unsigned int i = 0; i < tmp->getNbChildren(); i++) {
        queue.push(tmp->getChildren(i));
      }
    }
    std::string def;
    def = tmp->getModuleName();
    std::string undef;
    VObjectType type = tmp->getType();
    if (tmp->getDefinition() == NULL) {
      undef = " [U]";
    }
    std::string type_s;
    Location loc(symbols->registerSymbol(tmp->getFileName()), tmp->getLineNb(),
                 0, tmp->getFullPathId(symbols));
    if (type == slUdp_instantiation) {
      type_s = "[UDP]";
      Error err(ErrorDefinition::ELAB_INSTANCE_PATH, loc);
      m_errors->addError(err);
    } else if (type == VObjectType::slModule_instantiation) {
      type_s = "[MOD]";
      Error err(ErrorDefinition::ELAB_INSTANCE_PATH, loc);
      m_errors->addError(err);
    } else if (type == VObjectType::slGate_instantiation) {
      type_s = "[GAT]";
      Error err(ErrorDefinition::ELAB_INSTANCE_PATH, loc);
      m_errors->addError(err);
    } else if (type == slInterface_instantiation) {
      type_s = "[I/F]";
      Error err(ErrorDefinition::ELAB_INTERFACE_INSTANCE_PATH, loc);
      m_errors->addError(err);
    } else if (type == slProgram_instantiation) {
      type_s = "[PRG]";
      Error err(ErrorDefinition::ELAB_PROGRAM_INSTANCE_PATH, loc);
      m_errors->addError(err);
    } else if (type == slModule_declaration) {
      type_s = "[TOP]";
      Error err(ErrorDefinition::ELAB_INSTANCE_PATH, loc);
      m_errors->addError(err);
    } else {
      type_s = "[SCO]";
      Error err(ErrorDefinition::ELAB_SCOPE_PATH, loc);
      m_errors->addError(err);
    }

    tree += type_s + " " + def + undef + " " + tmp->getFullPathName() + "\n";

    bool extraInfo = false;
    if (extraInfo) {
      // Extra debug info:
      if (tmp) {
        ModuleInstance* inst = dynamic_cast<ModuleInstance*>(tmp);
        if (inst) {
          for (auto ps : inst->getMappedValues()) {
            const std::string& name = ps.first;
            Value* val = ps.second.first;
            tree += std::string("    " + name + " = " + val->uhdmValue() +
                                     "\n");
          }
          for (auto ps : inst->getComplexValues()) {
            const std::string& name = ps.first;
            tree += std::string("    " + name + " = " + "complex" +
                                     "\n");
          }
        }
      }
    }

  }

  return tree;
}

void Design::reportInstanceTreeStats(unsigned int& nbTopLevelModules,
                                     unsigned int& maxDepth,
                                     unsigned int& numberOfInstances,
                                     unsigned int& numberOfLeafInstances,
                                     unsigned int& nbUndefinedModules,
                                     unsigned int& nbUndefinedInstances) {
  nbTopLevelModules = 0;
  maxDepth = 0;
  numberOfInstances = 0;
  numberOfLeafInstances = 0;
  nbUndefinedModules = 0;
  nbUndefinedInstances = 0;
  std::set<std::string> undefModules;
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
      unsigned int depth = tmp->getDepth();
      if (depth > maxDepth) {
        maxDepth = depth;
      }
    }
    if (tmp->getNbChildren()) {
      for (unsigned int i = 0; i < tmp->getNbChildren(); i++) {
        queue.push(tmp->getChildren(i));
      }
    } else {
      if (isInstance) numberOfLeafInstances++;
    }
    std::string def;
    if (tmp->getDefinition()) {
    } else {
      nbUndefinedInstances++;
      undefModules.insert(tmp->getModuleName());
    }
  }

  nbUndefinedModules = undefModules.size();
}

ModuleInstance* Design::findInstance(const std::string& path,
                                     ModuleInstance* scope) {
  std::vector<std::string> vpath;
  StringUtils::tokenize(path, ".", vpath);
  return findInstance(vpath, scope);
}

ModuleInstance* Design::findInstance(std::vector<std::string>& path,
                                     ModuleInstance* scope) {
  if (!path.size()) return NULL;
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

  return NULL;
}

ModuleInstance* Design::findInstance_(std::vector<std::string>& path,
                                      ModuleInstance* scope) {
  if (!path.size()) return NULL;
  if (scope == NULL) return NULL;
  if (path.size() == 1) {
    if (scope->getInstanceName() == path[0]) {
      return scope;
    }
  }

  for (unsigned int i = 0; i < scope->getNbChildren(); i++) {
    ModuleInstance* child = scope->getChildren(i);
    if (path.size()) {
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
  }
  return NULL;
}

DefParam* Design::getDefParam(const std::string& name) {
  std::vector<std::string> vpath;
  StringUtils::tokenize(name, ".", vpath);
  std::map<std::string, DefParam*>::iterator itr = m_defParams.find(vpath[0]);
  if (itr != m_defParams.end()) {
    vpath.erase(vpath.begin());
    return getDefParam_(vpath, (*itr).second);
  }
  return NULL;
}

Value* Design::getDefParamValue(const std::string& name) {
  DefParam* def = getDefParam(name);
  if (def) return def->getValue();
  return NULL;
}

DefParam* Design::getDefParam_(std::vector<std::string>& path,
                               DefParam* parent) {
  if (path.size() == 0) {
    return parent;
  }
  std::map<std::string, DefParam*>::iterator itr =
      parent->getChildren().find(path[0]);
  if (itr != parent->getChildren().end()) {
    path.erase(path.begin());
    return getDefParam_(path, (*itr).second);
  }
  return NULL;
}

void Design::addDefParam(const std::string& name, const FileContent* fC,
                         NodeId nodeId, Value* value) {
  std::vector<std::string> vpath;
  StringUtils::tokenize(name, ".", vpath);
  std::map<std::string, DefParam*>::iterator itr = m_defParams.find(vpath[0]);
  if (itr != m_defParams.end()) {
    vpath.erase(vpath.begin());
    addDefParam_(vpath, fC, nodeId, value, (*itr).second);
  } else {
    DefParam* def = new DefParam(vpath[0]);
    m_defParams.insert(std::make_pair(vpath[0], def));
    vpath.erase(vpath.begin());
    addDefParam_(vpath, fC, nodeId, value, def);
  }
}

void Design::addDefParam_(std::vector<std::string>& path,
                          const FileContent* fC,
                          NodeId nodeId, Value* value, DefParam* parent) {
  if (path.size() == 0) {
    parent->setValue(value);
    parent->setLocation(fC, nodeId);
    return;
  }
  std::map<std::string, DefParam*>::iterator itr =
      parent->getChildren().find(path[0]);
  if (itr != parent->getChildren().end()) {
    path.erase(path.begin());
    if (path.size() == 0) {
      DefParam* previous = (*itr).second;
      if ((fC->getFileId(nodeId) !=
           previous->getLocation()->getFileId(previous->getNodeId())) ||
          (fC->Line(nodeId) !=
           previous->getLocation()->Line(previous->getNodeId()))) {
        Location loc1(
            fC->getFileId(nodeId), fC->Line(nodeId), 0,
            m_errors->getSymbolTable()->registerSymbol(
                previous->getFullName()));
        Location loc2(previous->getLocation()->getFileId(previous->getNodeId()),
                      previous->getLocation()->Line(previous->getNodeId()), 0,
                      0);
        Error err(ErrorDefinition::ELAB_MULTI_DEFPARAM_ON_OBJECT, loc1, loc2);
        m_errors->addError(err);
      }
    }
    addDefParam_(path, fC, nodeId, value, (*itr).second);
  } else {
    DefParam* def = new DefParam(path[0], parent);
    parent->setChild(path[0], def);
    path.erase(path.begin());
    addDefParam_(path, fC, nodeId, value, def);
  }
}

void Design::checkDefParamUsage(DefParam* parent) {
  if (parent == NULL) {
    // Start by all the top defs of the trie
    for (auto top : m_defParams) {
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

      Location loc(
          parent->getLocation()->getFileId(parent->getNodeId()),
          parent->getLocation()->Line(parent->getNodeId()), 0,
          m_errors->getSymbolTable()->registerSymbol(
              parent->getFullName()));

      Error err(ErrorDefinition::ELAB_UNMATCHED_DEFPARAM, loc);
      m_errors->addError(err);
    }
    for (auto param : parent->getChildren()) {
      checkDefParamUsage(param.second);
    }
  }
}

Package* Design::getPackage(const std::string& name) {
  PackageNamePackageDefinitionMultiMap::iterator itr =
      m_packageDefinitions.find(name);
  if (itr == m_packageDefinitions.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

Program* Design::getProgram(const std::string& name) {
  ProgramNameProgramDefinitionMap::iterator itr =
      m_programDefinitions.find(name);
  if (itr == m_programDefinitions.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

ClassDefinition* Design::getClassDefinition(const std::string& name) {
  ClassNameClassDefinitionMap::iterator itr =
      m_uniqueClassDefinitions.find(name);
  if (itr == m_uniqueClassDefinitions.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}

void Design::orderPackages() {
  if (m_orderedPackageNames.size() == 0) return;
  m_orderedPackageDefinitions.resize(m_orderedPackageNames.size());
  unsigned int index = 0;
  typedef std::map<std::string, int> MultiDefCount;
  MultiDefCount multiDefCount;
  for (auto packageName : m_orderedPackageNames) {
    for (unsigned int i = 0; i < m_packageDefinitions.size(); i++) {
      PackageNamePackageDefinitionMultiMap::iterator pos =
          m_packageDefinitions.begin();
      for (unsigned ii = 0; ii < i; ii++) pos++;
      std::pair<const std::string, Package*>* name_pack;
      name_pack = &(*pos);

      if (packageName == name_pack->first) {
        MultiDefCount::iterator itr = multiDefCount.find(packageName);
        if (itr == multiDefCount.end()) {
          multiDefCount.insert(std::make_pair(packageName, 1));
        } else {
          int level = (*itr).second;
          (*itr).second++;
          pos = m_packageDefinitions.begin();
          for (unsigned ii = 0; ii < i + level; ii++) pos++;
          name_pack = &(*pos);
        }
        m_orderedPackageDefinitions[index] = name_pack->second;
        index++;
        break;
      }
    }
  }
}

Package* Design::addPackageDefinition(const std::string& packageName,
                                      Package* package) {
  PackageNamePackageDefinitionMultiMap::iterator itr =
      m_packageDefinitions.find(packageName);
  if (itr == m_packageDefinitions.end()) {
    m_packageDefinitions.insert(std::make_pair(packageName, package));
    return package;
  } else {
    Package* old = (*itr).second;
    if (old->getFileContents()[0]->getParent() &&
        (old->getFileContents()[0]->getParent() ==
         package->getFileContents()[0]->getParent())) {
      old->append(package);
      return old;
    } else {
      m_packageDefinitions.insert(std::make_pair(packageName, package));
      return package;
    }
  }
}

void Design::addClassDefinition(const std::string& className,
                                ClassDefinition* classDef) {
  m_classDefinitions.insert(std::make_pair(className, classDef));
  m_uniqueClassDefinitions.insert(std::make_pair(className, classDef));
}

void Design::clearContainers() {
  m_moduleDefinitions.clear();

  m_topLevelModuleInstances.clear();

  m_defParams.clear();

  m_packageDefinitions.clear();
  m_orderedPackageDefinitions.clear();

  m_programDefinitions.clear();

  m_classDefinitions.clear();

  m_uniqueClassDefinitions.clear();

  m_orderedPackageNames.clear();
}
