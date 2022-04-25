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
 * File:   DesignElaboration.cpp
 * Author: alain
 *
 * Created on July 12, 2017, 8:55 PM
 */

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Config/ConfigSet.h>
#include <Surelog/Design/BindStmt.h>
#include <Surelog/Design/DefParam.h>
#include <Surelog/Design/DesignElement.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/ModuleDefinition.h>
#include <Surelog/Design/ModuleInstance.h>
#include <Surelog/Design/Parameter.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/CompileModule.h>
#include <Surelog/DesignCompile/DesignElaboration.h>
#include <Surelog/DesignCompile/NetlistElaboration.h>
#include <Surelog/Library/Library.h>
#include <Surelog/Package/Package.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Testbench/Program.h>
#include <Surelog/Utils/StringUtils.h>

#include <cstring>

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/RTTI.h>
#include <uhdm/bit_typespec.h>
#include <uhdm/clone_tree.h>
#include <uhdm/constant.h>
#include <uhdm/expr.h>
#include <uhdm/instance.h>
#include <uhdm/operation.h>
#include <uhdm/parameter.h>
#include <uhdm/ref_obj.h>
#include <uhdm/string_typespec.h>
#include <uhdm/typespec.h>

#include <fstream>
#include <queue>
#include <unordered_set>

namespace SURELOG {

namespace fs = std::filesystem;

DesignElaboration::DesignElaboration(CompileDesign* compileDesign)
    : TestbenchElaboration(compileDesign) {
  m_moduleDefFactory = nullptr;
  m_moduleInstFactory = nullptr;
  m_exprBuilder.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
  m_exprBuilder.setDesign(m_compileDesign->getCompiler()->getDesign());
}

DesignElaboration::~DesignElaboration() {}

bool DesignElaboration::elaborate() {
  createBuiltinPrimitives_();
  setupConfigurations_();
  identifyTopModules_();
  bindPackagesDataTypes_();
  elaborateAllModules_(true);
  elaborateAllModules_(false);
  reduceUnnamedBlocks_();
  checkElaboration_();
  reportElaboration_();
  createFileList_();
  return true;
}

std::string builtinGateName(VObjectType gatetype) {
  std::string modName;
  switch (gatetype) {
    case VObjectType::slNInpGate_And:
      modName = "work@and";
      break;
    case VObjectType::slNInpGate_Or:
      modName = "work@or";
      break;
    case VObjectType::slNInpGate_Nand:
      modName = "work@nand";
      break;
    case VObjectType::slNInpGate_Nor:
      modName = "work@nor";
      break;
    case VObjectType::slNInpGate_Xor:
      modName = "work@xor";
      break;
    case VObjectType::slNInpGate_Xnor:
      modName = "work@xnor";
      break;
    case VObjectType::slNOutGate_Buf:
      modName = "work@buf";
      break;
    case VObjectType::slNOutGate_Not:
      modName = "work@not";
      break;
    case VObjectType::slPassEnSwitch_Tranif0:
      modName = "work@tranif0";
      break;
    case VObjectType::slPassEnSwitch_Tranif1:
      modName = "work@tranif1";
      break;
    case VObjectType::slPassEnSwitch_RTranif1:
      modName = "work@rtranif1";
      break;
    case VObjectType::slPassEnSwitch_RTranif0:
      modName = "work@rtranif0";
      break;
    case VObjectType::slPassSwitch_Tran:
      modName = "work@tran";
      break;
    case VObjectType::slPassSwitch_RTran:
      modName = "work@rtran";
      break;
    case VObjectType::slCmosSwitchType_Cmos:
      modName = "work@cmos";
      break;
    case VObjectType::slCmosSwitchType_RCmos:
      modName = "work@rcmos";
      break;
    case VObjectType::slEnableGateType_Bufif0:
      modName = "work@bufif0";
      break;
    case VObjectType::slEnableGateType_Bufif1:
      modName = "work@bufif1";
      break;
    case VObjectType::slEnableGateType_Notif0:
      modName = "work@notif0";
      break;
    case VObjectType::slEnableGateType_Notif1:
      modName = "work@notif1";
      break;
    case VObjectType::slMosSwitchType_NMos:
      modName = "work@nmos";
      break;
    case VObjectType::slMosSwitchType_PMos:
      modName = "work@pmos";
      break;
    case VObjectType::slMosSwitchType_RNMos:
      modName = "work@rnmos";
      break;
    case VObjectType::slMosSwitchType_RPMos:
      modName = "work@rpmos";
      break;
    case VObjectType::slPullup:
      modName = "work@pullup";
      break;
    case VObjectType::slPulldown:
      modName = "work@pulldown";
      break;
    default:
      modName = "work@UnsupportedPrimitive";
      break;
  }
  return modName;
}

bool DesignElaboration::setupConfigurations_() {
  ConfigSet* configSet =
      m_compileDesign->getCompiler()->getDesign()->getConfigSet();
  SymbolTable* st = m_compileDesign->getCompiler()
                        ->getCommandLineParser()
                        ->mutableSymbolTable();
  std::vector<Config>& allConfigs = configSet->getAllMutableConfigs();
  std::vector<SymbolId> selectedConfigIds =
      m_compileDesign->getCompiler()->getCommandLineParser()->getUseConfigs();
  std::set<std::string> selectedConfigs;
  for (auto confId : selectedConfigIds) {
    std::string name = st->getSymbol(confId);
    if (name.find('.') == std::string::npos) {
      name = "work@" + name;
    } else {
      name = StringUtils::replaceAll(name, ".", "@");
    }
    selectedConfigs.insert(name);
    bool found = false;
    for (const auto& config : allConfigs) {
      if (config.getName() == name) {
        found = true;
        break;
      }
    }
    if (!found) {
      Location loc(st->registerSymbol(name));
      Error err(ErrorDefinition::CMD_UNDEFINED_CONFIG, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    }
  }

  std::queue<std::string> configq;
  for (auto& config : allConfigs) {
    if (selectedConfigs.find(config.getName()) != selectedConfigs.end()) {
      config.setIsUsed();
      config.setTopLevel(true);
      configq.push(config.getName());
    }
  }
  std::unordered_set<const Config*> configS;
  while (!configq.empty()) {
    std::string configName = configq.front();
    configq.pop();
    Config* conf = configSet->getMutableConfigByName(configName);
    if (conf) {
      if (configS.find(conf) != configS.end()) {
        continue;
      }
      configS.insert(conf);

      conf->setIsUsed();
      for (const auto& usec : conf->getInstanceUseClauses()) {
        if (usec.second.getType() == UseClause::UseConfig) {
          std::string confName = usec.second.getName();
          configq.push(confName);
          Config* conf = configSet->getMutableConfigByName(confName);
          if (!conf) {
            const FileContent* fC = usec.second.getFileContent();
            Location loc(st->registerSymbol(
                             fC->getFileName(usec.second.getNodeId()).string()),
                         fC->Line(usec.second.getNodeId()), 0,
                         st->registerSymbol(confName));
            Error err(ErrorDefinition::ELAB_UNDEFINED_CONFIG, loc);
            m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
          }
        }
      }
    }
  }

  std::vector<std::string> unused;
  for (const auto& config : allConfigs) {
    const std::string& name = config.getName();
    const FileContent* fC = config.getFileContent();
    SymbolId fid =
        st->registerSymbol(fC->getFileName(config.getNodeId()).string());
    unsigned int line = fC->Line(config.getNodeId());
    Location loc(fid, line, 0, st->getId(config.getName()));
    if (!config.isUsed()) {
      Error err(ErrorDefinition::ELAB_CONFIGURATION_IGNORED, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
      unused.push_back(name);
    } else {
      Error err(ErrorDefinition::ELAB_CONFIGURATION_USED, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    }
  }

  // Remove unused configs from set
  for (const auto& name : unused) {
    std::vector<Config>::iterator itr;
    for (itr = allConfigs.begin(); itr != allConfigs.end(); itr++) {
      if ((*itr).getName() == name) {
        allConfigs.erase(itr);
        break;
      }
    }
  }

  // Create top level module list and recurse configs
  for (auto& config : allConfigs) {
    if (config.isTopLevel()) {
      std::string lib = config.getDesignLib();
      std::string top = config.getDesignTop();
      std::string name = lib + "@" + top;
      m_toplevelConfigModules.insert(name);
      m_instConfig.insert(std::make_pair(name, config));
      m_cellConfig.insert(std::make_pair(name, config));

      for (auto& instClause : config.getInstanceUseClauses()) {
        m_instUseClause.insert(
            std::make_pair(lib + "@" + instClause.first, instClause.second));
        if (instClause.second.getType() == UseClause::UseConfig) {
          Config* config =
              configSet->getMutableConfigByName(instClause.second.getName());
          if (config) {
            std::set<Config*> configStack;
            recurseBuildInstanceClause_(lib + "@" + instClause.first, config,
                                        configStack);
          }
        }
      }
      for (auto& cellClause : config.getCellUseClauses()) {
        m_cellUseClause.insert(
            std::make_pair(cellClause.first, cellClause.second));
      }
    }
  }
  return true;
}

void DesignElaboration::recurseBuildInstanceClause_(
    const std::string& parentPath, Config* config,
    std::set<Config*>& configStack) {
  if (configStack.find(config) != configStack.end()) {
    return;
  }
  configStack.insert(config);

  ConfigSet* configSet =
      m_compileDesign->getCompiler()->getDesign()->getConfigSet();
  for (auto& useClause : config->getInstanceUseClauses()) {
    std::string inst = useClause.first;
    std::string fullPath = parentPath + "." + inst;
    m_instUseClause.insert(std::make_pair(fullPath, useClause.second));
    if (useClause.second.getType() == UseClause::UseConfig) {
      Config* config =
          configSet->getMutableConfigByName(useClause.second.getName());
      if (config) {
        recurseBuildInstanceClause_(parentPath + "." + useClause.first, config,
                                    configStack);
      }
    }
  }
  for (auto& useClause : config->getCellUseClauses()) {
    std::string inst = useClause.first;
    std::string fullPath = inst;
    m_cellUseClause.insert(std::make_pair(fullPath, useClause.second));
  }
}

bool DesignElaboration::identifyTopModules_() {
  m_topLevelModules.clear();
  bool modulePresent = false;
  bool toplevelModuleFound = false;
  SymbolTable* st = m_compileDesign->getCompiler()->getSymbolTable();
  std::set<std::string>& userTopList = m_compileDesign->getCompiler()
                                           ->getCommandLineParser()
                                           ->getTopLevelModules();
  auto all_files =
      m_compileDesign->getCompiler()->getDesign()->getAllFileContents();
  typedef std::multimap<std::string,
                        std::pair<const DesignElement*, const FileContent*>>
      ModuleMultiMap;
  ModuleMultiMap all_modules;
  for (auto file : all_files) {
    if (m_compileDesign->getCompiler()->isLibraryFile(file.first)) continue;
    for (const DesignElement* element : file.second->getDesignElements()) {
      const std::string& elemName = st->getSymbol(element->m_name);
      if (element->m_type == DesignElement::Module) {
        if (element->m_parent) {
          // This is a nested element
          continue;
        }
        const std::string& libName = file.second->getLibrary()->getName();
        std::string topname = libName;
        topname += "@" + elemName;

        if (!file.second->getParent()) {
          // Files that have parent are splited files (When a module is too
          // large it is splited)
          all_modules.insert(
              std::make_pair(topname, std::make_pair(element, file.second)));
        }

        modulePresent = true;
        bool used = false;
        for (auto file1 : all_files) {
          if (file1.second->getReferencedObjects().find(elemName) !=
              file1.second->getReferencedObjects().end()) {
            if (m_compileDesign->getCompiler()->isLibraryFile(file1.first))
              continue;
            used = true;
            break;
          }
        }

        if (!used) {
          bool isTop = true;

          if (!m_toplevelConfigModules.empty()) {
            isTop = false;
            if (m_toplevelConfigModules.find(topname) !=
                m_toplevelConfigModules.end()) {
              isTop = true;
            }
          }

          if (isTop) {
            SymbolId topid = st->registerSymbol(topname);
            auto itr = m_uniqueTopLevelModules.find(topname);
            Location loc(
                st->registerSymbol(
                    (file.second->getFileName(element->m_node)).string()),
                element->m_line, 0, topid);
            if (itr == m_uniqueTopLevelModules.end()) {
              bool okModule = true;
              if (!userTopList.empty()) {
                if (userTopList.find(elemName) == userTopList.end())
                  okModule = false;
              }
              if (okModule) {
                m_uniqueTopLevelModules.insert(topname);
                m_topLevelModules.emplace_back(topname, file.second);
                toplevelModuleFound = true;
                Error err(ErrorDefinition::ELAB_TOP_LEVEL_MODULE, loc);
                m_compileDesign->getCompiler()->getErrorContainer()->addError(
                    err);
              }
            }
          }
        }
      }
    }
  }

  // Check for multiple definition
  std::string prevModuleName;
  const DesignElement* prevModuleDefinition = nullptr;
  const FileContent* prevFileContent = nullptr;
  for (ModuleMultiMap::iterator itr = all_modules.begin();
       itr != all_modules.end(); itr++) {
    std::string moduleName = (*itr).first;
    const DesignElement* moduleDefinition = (*itr).second.first;
    const FileContent* fileContent = (*itr).second.second;
    bool done = false;
    if (moduleName == prevModuleName) {
      const FileContent* fC1 = (*itr).second.second;
      NodeId nodeId1 = moduleDefinition->m_node;
      fs::path fileName1 = fC1->getFileName(nodeId1);
      unsigned int line1 = fC1->Line(nodeId1);
      Location loc1(st->registerSymbol(fileName1.string()), line1, 0,
                    st->registerSymbol(moduleName));

      std::vector<Location> locations;

      while (1) {
        const FileContent* fC2 = prevFileContent;
        NodeId nodeId2 = prevModuleDefinition->m_node;
        fs::path fileName2 = fC2->getFileName(nodeId2);
        unsigned int line2 = fC2->Line(nodeId2);
        Location loc2(st->registerSymbol(fileName2.string()), line2, 0,
                      st->registerSymbol(moduleName));

        if ((fileName1 != fileName2) || (line1 != line2)) {
          locations.push_back(loc2);
        }

        itr++;
        if (itr == all_modules.end()) {
          done = true;
          break;
        } else {
          std::string nextModuleName = (*itr).first;
          const DesignElement* nextModuleDefinition = (*itr).second.first;
          const FileContent* nextFileContent = (*itr).second.second;
          prevModuleName = nextModuleName;
          prevModuleDefinition = nextModuleDefinition;
          prevFileContent = nextFileContent;
          if (prevModuleName != moduleName) {
            moduleName = prevModuleName;
            moduleDefinition = prevModuleDefinition;
            fileContent = prevFileContent;
            break;
          }
        }
      }

      if (!locations.empty()) {
        Error err1(ErrorDefinition::ELAB_MULTIPLY_DEFINED_MODULE, loc1,
                   &locations);
        m_compileDesign->getCompiler()->getErrorContainer()->addError(err1);
      }
    }
    prevModuleName = moduleName;
    prevModuleDefinition = moduleDefinition;
    prevFileContent = fileContent;
    if (done) break;
  }

  if (m_topLevelModules.size() > 1) {
    Location loc(0);
    Error err(ErrorDefinition::ELAB_MULTIPLE_TOP_LEVEL_MODULES, loc);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
  }

  // User overrides
  if (!toplevelModuleFound) {
    for (const auto& userM : userTopList) {
      bool found = false;
      for (auto file : all_files) {
        if (m_compileDesign->getCompiler()->isLibraryFile(file.first)) continue;
        for (const DesignElement* element : file.second->getDesignElements()) {
          const std::string& elemName = st->getSymbol(element->m_name);
          if (element->m_type == DesignElement::Module) {
            if (element->m_parent) {
              // This is a nested element
              continue;
            }
            if (userM != elemName) {
              continue;
            }
            found = true;
            Location locUser(0, 0, 0, st->registerSymbol(userM));
            Error errUser(ErrorDefinition::ELAB_TOP_LEVEL_IS_NOT_A_TOP_LEVEL,
                          locUser);
            m_compileDesign->getCompiler()->getErrorContainer()->addError(
                errUser);

            const std::string& libName = file.second->getLibrary()->getName();
            std::string topname = libName;
            topname += "@" + elemName;
            m_uniqueTopLevelModules.insert(topname);
            m_topLevelModules.emplace_back(topname, file.second);
            toplevelModuleFound = true;
            SymbolId topid = st->registerSymbol(topname);
            Location loc(
                st->registerSymbol(
                    (file.second->getFileName(element->m_node)).string()),
                element->m_line, 0, topid);
            Error err(ErrorDefinition::ELAB_TOP_LEVEL_MODULE, loc);
            m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
          }
        }
      }
      if (!found) {
        Location locUser(0, 0, 0, st->registerSymbol(userM));
        Error errUser(ErrorDefinition::ELAB_TOP_LEVEL_DOES_NOT_EXIST, locUser);
        m_compileDesign->getCompiler()->getErrorContainer()->addError(errUser);
      }
    }
  }

  if (modulePresent && (!toplevelModuleFound)) {
    Location loc(0);
    Error err(ErrorDefinition::ELAB_NO_TOP_LEVEL_MODULE, loc);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
  }

  return true;
}

bool DesignElaboration::createBuiltinPrimitives_() {
  m_moduleDefFactory = new ModuleDefinitionFactory();
  Design* design = m_compileDesign->getCompiler()->getDesign();

  // Register built-in primitives
  for (auto type : {"cmos",     "rcmos",    "bufif0",
                    "bufif1",   "notif0",   "notif1",
                    "nmos",     "pmos",     "rnmos",
                    "rpmos",    "and",      "or",
                    "nand",     "nor",      "xor",
                    "xnor",     "buf",      "not",
                    "tranif0",  "tranif1",  "rtranif0",
                    "rtranif1", "tran",     "rtran",
                    "pullup",   "pulldown", "UnsupportedPrimitive"}) {
    std::string name = std::string("work@") + type;
    design->addModuleDefinition(name,
                                m_moduleDefFactory->newModuleDefinition(
                                    nullptr, 0, std::string("work@") + type));
  }

  return true;
}

bool DesignElaboration::elaborateAllModules_(bool onlyTopLevel) {
  bool status = true;
  for (const auto& topmodule : m_topLevelModules) {
    if (!elaborateModule_(topmodule.first, topmodule.second, onlyTopLevel)) {
      status = false;
    }
  }
  return status;
}

Config* DesignElaboration::getInstConfig(const std::string& name) {
  Config* config = nullptr;
  auto itr = m_instConfig.find(name);
  if (itr != m_instConfig.end()) {
    config = &(*itr).second;
  }
  return config;
}

Config* DesignElaboration::getCellConfig(const std::string& name) {
  Config* config = nullptr;
  auto itr = m_cellConfig.find(name);
  if (itr != m_cellConfig.end()) {
    config = &(*itr).second;
  }
  return config;
}

bool DesignElaboration::bindAllInstances_(ModuleInstance* parent,
                                          ModuleInstanceFactory* factory,
                                          Config* config) {
  DesignComponent* def = parent->getDefinition();
  Design* design = m_compileDesign->getCompiler()->getDesign();
  std::vector<ModuleInstance*> parentSubInstances;
  if (def) {
    for (BindStmt* bind : design->getBindStmts(def->getName())) {
      ModuleInstance* bindInstance =
          createBindInstance_(bind, parent, factory, config);
      if (bindInstance) {
        parentSubInstances.push_back(bindInstance);
      }
    }
  }
  for (unsigned int i = 0; i < parent->getNbChildren(); i++) {
    ModuleInstance* child = parent->getChildren(i);
    bindAllInstances_(child, factory, config);
  }
  for (auto inst : parentSubInstances) {
    parent->addSubInstance(inst);
  }
  return true;
}

bool DesignElaboration::elaborateModule_(const std::string& moduleName,
                                         const FileContent* fC,
                                         bool onlyTopLevel) {
  const FileContent::NameIdMap& nameIds = fC->getObjectLookup();
  std::vector<VObjectType> types = {VObjectType::slUdp_instantiation,
                                    VObjectType::slModule_instantiation,
                                    VObjectType::slInterface_instantiation,
                                    VObjectType::slProgram_instantiation};
  std::string libName = fC->getLibrary()->getName();
  Config* config = getInstConfig(moduleName);
  if (config == nullptr) config = getCellConfig(moduleName);
  Design* design = m_compileDesign->getCompiler()->getDesign();
  if (!m_moduleInstFactory) m_moduleInstFactory = new ModuleInstanceFactory();
  for (const auto& nameId : nameIds) {
    if ((fC->Type(nameId.second) == VObjectType::slModule_declaration) &&
        (moduleName == (libName + "@" + nameId.first))) {
      DesignComponent* def = design->getComponentDefinition(moduleName);
      if (onlyTopLevel) {
        ModuleInstance* instance = m_moduleInstFactory->newModuleInstance(
            def, fC, nameId.second, nullptr, moduleName, moduleName);
        design->addTopLevelModuleInstance(instance);
      } else {
        ModuleInstance* instance = design->findInstance(moduleName);
        for (unsigned int i = 0; i < def->getFileContents().size(); i++) {
          std::vector<ModuleInstance*> parentSubInstances;
          NodeId id = def->getNodeIds()[i];
          elaborateInstance_(def->getFileContents()[i], id, 0,
                             m_moduleInstFactory, instance, config,
                             parentSubInstances);
          if (instance)
            bindAllInstances_(instance, m_moduleInstFactory, config);
        }
      }
      break;
    }
  }
  return true;
}

void DesignElaboration::recurseInstanceLoop_(
    std::vector<int>& from, std::vector<int>& to, std::vector<int>& indexes,
    unsigned int pos, DesignComponent* def, const FileContent* fC,
    NodeId subInstanceId, NodeId paramOverride, ModuleInstanceFactory* factory,
    ModuleInstance* parent, Config* config, std::string instanceName,
    const std::string& modName, std::vector<ModuleInstance*>& allSubInstances) {
  if (pos == indexes.size()) {
    // This is where the real logic goes.
    // indexes[i] contain the value of the i-th index.
    for (int index : indexes) {
      if (!instanceName.empty()) {
        if (instanceName[instanceName.size() - 1] == ' ') {
          instanceName.erase(instanceName.end() - 1);
        }
      }
      instanceName = instanceName + "[" + std::to_string(index) + "]";
    }
    ModuleInstance* child = factory->newModuleInstance(
        def, fC, subInstanceId, parent, instanceName, modName);
    VObjectType type = fC->Type(subInstanceId);
    if (def && (type != VObjectType::slGate_instantiation)) {
      for (unsigned int i = 0; i < def->getFileContents().size(); i++) {
        elaborateInstance_(def->getFileContents()[i], def->getNodeIds()[i],
                           paramOverride, factory, child, config,
                           allSubInstances);
      }
    }
    allSubInstances.push_back(child);

  } else {
    for (indexes[pos] = from[pos]; indexes[pos] <= to[pos]; indexes[pos]++) {
      // Recurse for the next level
      recurseInstanceLoop_(from, to, indexes, pos + 1, def, fC, subInstanceId,
                           paramOverride, factory, parent, config, instanceName,
                           modName, allSubInstances);
    }
  }
}

ModuleInstance* DesignElaboration::createBindInstance_(
    BindStmt* bind, ModuleInstance* parent, ModuleInstanceFactory* factory,
    Config* config) {
  ModuleInstance* instance = nullptr;
  const FileContent* fC = bind->getFileContent();
  Library* lib = fC->getLibrary();
  NodeId bindNodeId = bind->getBindId();
  const std::string bindModName =
      lib->getName() + "@" + fC->SymName(bindNodeId);
  NodeId instNameId = bind->getInstanceId();
  const std::string& instName = fC->SymName(instNameId);
  NodeId targetModId = bind->getTargetModId();
  NodeId targetInstId = bind->getTargetInstId();
  const std::string targetName =
      lib->getName() + "@" + fC->SymName(targetModId);
  DesignComponent* def = parent->getDefinition();
  Design* design = m_compileDesign->getCompiler()->getDesign();
  bool instanceMatch = true;
  if (targetInstId) {
    const std::string& targetInstName = fC->SymName(targetInstId);
    instanceMatch = (targetInstName == parent->getInstanceName());
  }
  DesignComponent* targetDef = nullptr;
  if (def && (def->getName() == targetName) && instanceMatch) {
    targetDef = design->getModuleDefinition(bindModName);
    if (targetDef) {
      instance = factory->newModuleInstance(targetDef, fC, bind->getStmtId(),
                                            parent->getParent(), instName,
                                            bindModName);
    } else {
      SymbolTable* st =
          m_compileDesign->getCompiler()->getErrorContainer()->getSymbolTable();
      Location loc(
          st->registerSymbol(fC->getFileName(bind->getStmtId()).string()),
          fC->Line(bind->getStmtId()), 0, st->registerSymbol(bindModName));
      Error err(ErrorDefinition::ELAB_NO_MODULE_DEFINITION, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err, false,
                                                                    false);
    }
  }
  if (instance) {
    std::vector<ModuleInstance*> parentSubInstances;
    instance->setInstanceBinding(parent);
    NodeId parameterOverloading = fC->Sibling(bindNodeId);
    if (fC->Type(parameterOverloading) == slHierarchical_instance) {
      parameterOverloading = 0;
    }
    elaborateInstance_(targetDef->getFileContents()[0],
                       targetDef->getNodeIds()[0], parameterOverloading,
                       factory, instance, config, parentSubInstances);
  }
  return instance;
}

void DesignElaboration::elaborateInstance_(
    const FileContent* fC, NodeId nodeId, NodeId parentParamOverride,
    ModuleInstanceFactory* factory, ModuleInstance* parent, Config* config,
    std::vector<ModuleInstance*>& parentSubInstances) {
  if (!parent) return;

  std::vector<ModuleInstance*>& allSubInstances = parent->getAllSubInstances();
  std::string genBlkBaseName = "genblk";
  unsigned int genBlkIndex = 1;
  bool reuseInstance = false;
  std::string mname;
  std::vector<VObjectType> types;
  std::vector<std::string> params;

  // Scan for parameters, including DefParams
  collectParams_(params, fC, nodeId, parent, parentParamOverride);

  // Loop checking
  bool loopDetected = false;
  ModuleInstance* tmp = parent;
  DesignComponent* parentDef = tmp->getDefinition();
  if (tmp) {
    tmp = tmp->getParent();
  }
  while (tmp) {
    if (tmp->getDefinition() == parentDef) {
      loopDetected = true;
      for (const auto& pvalues : parent->getMappedValues()) {
        const std::string& name = pvalues.first;
        Value* pval = pvalues.second.first;
        Value* val = tmp->getValue(name, m_exprBuilder);
        if (val) {
          if (*pval != *val) {
            loopDetected = false;
            break;
          }
        }
      }
      for (const auto& cvalues : parent->getComplexValues()) {
        const std::string& name = cvalues.first;
        UHDM::expr* pval = cvalues.second;
        UHDM::expr* val = tmp->getComplexValue(name);
        if (val) {
          if (pval != val) {
            loopDetected = false;
            break;
          }
        }
      }
      break;
    }
    tmp = tmp->getParent();
  }
  if (loopDetected) {
    SymbolTable* st =
        m_compileDesign->getCompiler()->getErrorContainer()->getSymbolTable();
    Location loc(
        st->registerSymbol(fC->getFileName(parent->getNodeId()).string()),
        fC->Line(parent->getNodeId()), 0,
        st->registerSymbol(parent->getModuleName()));
    Location loc2(
        st->registerSymbol(
            tmp->getFileContent()->getFileName(tmp->getNodeId()).string()),
        tmp->getFileContent()->Line(tmp->getNodeId()), 0);
    Error err(ErrorDefinition::ELAB_INSTANTIATION_LOOP, loc, loc2);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    return;
  }

  // Apply DefParams
  Design* design = m_compileDesign->getCompiler()->getDesign();
  for (const auto& name : params) {
    DefParam* defparam =
        design->getDefParam(parent->getFullPathName() + "." + name);
    if (defparam) {
      Value* value = defparam->getValue();
      if (value) {
        parent->setValue(name, value, m_exprBuilder);
        defparam->setUsed();
      }
    }
  }
  bindDataTypes_(parent, parent->getDefinition());
  NetlistElaboration* nelab = new NetlistElaboration(m_compileDesign);
  nelab->elaborateInstance(parent);
  delete nelab;

  // Scan for regular instances and generate blocks
  types = {
      VObjectType::slUdp_instantiation, VObjectType::slModule_instantiation,
      VObjectType::slInterface_instantiation,
      VObjectType::slProgram_instantiation, VObjectType::slGate_instantiation,
      VObjectType::slConditional_generate_construct,  // Generate construct are
                                                      // a kind of instantiation
      VObjectType::slGenerate_module_conditional_statement,
      VObjectType::slGenerate_interface_conditional_statement,
      VObjectType::slLoop_generate_construct,
      VObjectType::slGenerate_module_loop_statement,
      VObjectType::slGenerate_interface_loop_statement,
      VObjectType::slPar_block, VObjectType::slSeq_block};

  std::vector<VObjectType> stopPoints = {
      VObjectType::slConditional_generate_construct,
      VObjectType::slGenerate_module_conditional_statement,
      VObjectType::slGenerate_interface_conditional_statement,
      VObjectType::slLoop_generate_construct,
      VObjectType::slGenerate_module_loop_statement,
      VObjectType::slGenerate_interface_loop_statement,
      VObjectType::slPar_block,
      VObjectType::slSeq_block,
      VObjectType::slModule_declaration,
      VObjectType::slBind_directive};

  std::vector<NodeId> subInstances =
      fC->sl_collect_all(nodeId, types, stopPoints);

  for (auto subInstanceId : subInstances) {
    NodeId childId = 0;
    std::string instName;
    std::string modName;
    DesignComponent* def = nullptr;
    ModuleInstance* child = nullptr;
    NodeId paramOverride = 0;
    Config* subConfig = config;
    VObjectType type = fC->Type(subInstanceId);

    if (type == slSeq_block || type == slPar_block) {
      NodeId identifierId = fC->Child(subInstanceId);
      if (fC->Name(identifierId))
        instName = fC->SymName(identifierId);
      else
        instName = "UNNAMED";
    } else if (type == slConditional_generate_construct) {
      NodeId constructId = fC->Child(subInstanceId);
      NodeId condId = fC->Child(constructId);
      NodeId blockId = fC->Sibling(condId);
      NodeId nameId = fC->Child(blockId);
      if (fC->Name(nameId))
        instName = fC->SymName(nameId);
      else
        instName = "UNNAMED";
    } else {
      NodeId instId = fC->sl_collect(subInstanceId, slName_of_instance);
      NodeId identifierId = 0;
      if (instId != InvalidNodeId) {
        identifierId = fC->Child(instId);
        instName = fC->SymName(identifierId);
      }
    }

    // Special module binding for built-in primitives
    if (type == VObjectType::slGate_instantiation) {
      VObjectType gatetype = fC->Type(fC->Child(subInstanceId));
      modName = builtinGateName(gatetype);
      def = design->getComponentDefinition(modName);
      child = factory->newModuleInstance(def, fC, subInstanceId, parent,
                                         instName, modName);
      parent->addSubInstance(child);
      bindDataTypes_(parent, def);
      NetlistElaboration* nelab = new NetlistElaboration(m_compileDesign);
      nelab->elaborateInstance(child);
      delete nelab;
    }
    // Special module binding for generate statements
    else if (type == VObjectType::slConditional_generate_construct ||
             type == VObjectType::slGenerate_module_conditional_statement ||
             type == VObjectType::slGenerate_interface_conditional_statement ||
             type == VObjectType::slLoop_generate_construct ||
             type == VObjectType::slGenerate_module_loop_statement ||
             type == VObjectType::slGenerate_interface_loop_statement) {
      modName = genBlkBaseName + std::to_string(genBlkIndex);
      std::string append = "0";
      while (parent->getValue(modName, m_exprBuilder)) {
        modName = genBlkBaseName + append + std::to_string(genBlkIndex);
        append += "0";
      }
      std::vector<VObjectType> btypes = {
          VObjectType::slGenerate_module_block,
          VObjectType::slGenerate_interface_block,
          VObjectType::slGenerate_block,
          VObjectType::slGenerate_module_named_block,
          VObjectType::slGenerate_interface_named_block};

      std::vector<NodeId> blockIds =
          fC->sl_collect_all(subInstanceId, btypes, true);
      if (!blockIds.empty()) {
        NodeId blockId = blockIds[0];
        NodeId blockNameId = fC->Child(blockId);
        if (fC->Type(blockNameId) == VObjectType::slStringConst) {
          modName = fC->SymName(blockNameId);
        }
      }
      genBlkIndex++;
      instName = modName;
      std::string fullName;
      std::string libName = fC->getLibrary()->getName();
      if (instName == parent->getInstanceName()) {
        fullName += parent->getFullPathName();
        reuseInstance = true;
      } else {
        fullName += parent->getModuleName() + "." + instName;
      }

      NodeId conditionId = fC->Child(subInstanceId);
      if (fC->Type(conditionId) == slIf_generate_construct) {
        NodeId IF = fC->Child(conditionId);
        conditionId = fC->Sibling(IF);
      }
      VObjectType conditionType = fC->Type(conditionId);
      if (conditionType == VObjectType::slGenvar_initialization ||
          conditionType ==
              VObjectType::slGenvar_decl_assignment) {  // For loop stmt

        // Var init
        NodeId varId = fC->Child(conditionId);
        NodeId constExpr = fC->Sibling(varId);

        bool validValue;
        uint64_t initVal = (uint64_t)m_helper.getValue(
            validValue, parentDef, fC, constExpr, m_compileDesign, nullptr,
            parent, true, false);
        Value* initValue = m_exprBuilder.getValueFactory().newLValue();
        initValue->set(initVal);

        std::string name = fC->SymName(varId);
        parent->setValue(name, initValue, m_exprBuilder, fC->Line(varId));

        // End-loop test
        NodeId endLoopTest = fC->Sibling(conditionId);

        // Iteration
        NodeId iteration = fC->Sibling(endLoopTest);
        NodeId var = fC->Child(iteration);
        NodeId assignOp = fC->Sibling(var);
        NodeId expr = fC->Sibling(assignOp);
        if (expr == 0) {  // Unary operator like i++
          expr = var;
        } else if (fC->Type(assignOp) !=
                   slAssignOp_Assign) {  // Operators like +=
          expr = var;
        }
        // Generate block
        NodeId genBlock = fC->Sibling(iteration);

        int64_t condVal =
            m_helper.getValue(validValue, parentDef, fC, endLoopTest,
                              m_compileDesign, nullptr, parent, true, false);
        bool cont = (validValue && (condVal > 0));

        while (cont) {
          Value* currentIndexValue = parent->getValue(name, m_exprBuilder);
          long currVal = currentIndexValue->getValueUL();
          std::string indexedModName = parent->getFullPathName() + "." +
                                       modName + "[" + std::to_string(currVal) +
                                       "]";
          instName = modName + "[" + std::to_string(currVal) + "]";

          def = design->getComponentDefinition(indexedModName);
          if (def == nullptr) {
            def = m_moduleDefFactory->newModuleDefinition(fC, subInstanceId,
                                                          indexedModName);
            if (DesignComponent* defParent = parent->getDefinition())
              def->setParentScope(defParent);
            design->addModuleDefinition(indexedModName, (ModuleDefinition*)def);
          }

          // Compile generate block
          ((ModuleDefinition*)def)->setGenBlockId(genBlock);
          FunctorCompileModule funct(
              m_compileDesign, (ModuleDefinition*)def, design,
              m_compileDesign->getCompiler()->getSymbolTable(),
              m_compileDesign->getCompiler()->getErrorContainer(), parent);
          funct.operator()();

          child = factory->newModuleInstance(def, fC, genBlock, parent,
                                             instName, indexedModName);
          child->setValue(name, m_exprBuilder.clone(currentIndexValue),
                          m_exprBuilder, fC->Line(varId));
          elaborateInstance_(def->getFileContents()[0], genBlock, 0, factory,
                             child, config, allSubInstances);
          parent->addSubInstance(child);

          Value* newVal = m_exprBuilder.evalExpr(fC, expr, parent);
          parent->setValue(name, newVal, m_exprBuilder, fC->Line(varId));

          condVal =
              m_helper.getValue(validValue, parentDef, fC, endLoopTest,
                                m_compileDesign, nullptr, parent, true, false);
          cont = (validValue && (condVal > 0));

          if (!newVal->isValid()) {
            cont = false;
          }
        }
        parent->deleteValue(name, m_exprBuilder);
        continue;

      } else {  // If-Else or Case stmt
        if (fC->Type(conditionId) != VObjectType::slConstant_expression) {
          conditionId = fC->Child(conditionId);
        }
        bool validValue;
        int64_t condVal =
            m_helper.getValue(validValue, parentDef, fC, conditionId,
                              m_compileDesign, nullptr, parent, true, false);

        NodeId tmp = fC->Sibling(conditionId);

        if (fC->Type(tmp) == VObjectType::slCase_generate_item) {  // Case stmt
          NodeId caseItem = tmp;
          bool nomatch = true;
          while (nomatch) {
            NodeId exprItem = fC->Child(caseItem);
            if (fC->Type(exprItem) ==
                VObjectType::slGenerate_block)  // Default block
              nomatch = false;
            while (nomatch) {
              // Find if one of the case expr matches the case expr
              if (fC->Type(exprItem) == VObjectType::slConstant_expression) {
                bool validValue;
                int64_t caseVal = m_helper.getValue(
                    validValue, parentDef, fC, exprItem, m_compileDesign,
                    nullptr, parent, true, false);

                if (condVal == caseVal) {
                  nomatch = false;
                  break;
                }
              } else
                break;
              exprItem = fC->Sibling(exprItem);
            }

            if (nomatch) {
              // Next case stmt
              caseItem = fC->Sibling(caseItem);
              if (!caseItem) break;
              if (fC->Type(caseItem) != VObjectType::slCase_generate_item)
                break;
            } else {
              // We found a match
              while (fC->Type(exprItem) == VObjectType::slConstant_expression)
                exprItem = fC->Sibling(exprItem);
              childId = exprItem;
            }
          }
        } else {              // If-Else stmt
          if (condVal > 0) {  // If branch
            if (tmp)
              childId = tmp;
            else  // There is no If stmt
              continue;
          } else {  // Else branch
            if (tmp == 0) continue;
            bool activeBranch = false;
            while (1) {
              if (tmp) {
                tmp = fC->Sibling(tmp);  // Else
                if (tmp == 0) break;
                tmp = fC->Sibling(tmp);
                int64_t condVal = 0;

                NodeId Generate_block = tmp;
                NodeId Generate_item = fC->Child(Generate_block);
                NodeId Cond = 0;
                if (fC->Type(Generate_item) == slGenerate_item) {
                  NodeId Module_or_generate_item = fC->Child(Generate_item);
                  NodeId Module_common_item =
                      fC->Child(Module_or_generate_item);
                  NodeId Conditional_generate_construct =
                      fC->Child(Module_common_item);
                  NodeId If_generate_construct =
                      fC->Child(Conditional_generate_construct);
                  Cond = fC->Child(If_generate_construct);
                  if (fC->Type(Cond) == VObjectType::slIF) {
                    Cond = fC->Sibling(Cond);
                  }
                  if (fC->Type(Cond) == VObjectType::slConstant_expression) {
                    bool validValue;
                    condVal = m_helper.getValue(validValue, parentDef, fC, Cond,
                                                m_compileDesign, nullptr,
                                                parent, true, false);
                  } else {
                    // It is not an else-if
                    condVal = true;
                  }
                } else if (fC->Type(Generate_item) ==
                           slGenerate_module_conditional_statement) {
                  Cond = fC->Child(Generate_item);
                  if (fC->Type(Cond) == VObjectType::slIF) {
                    Cond = fC->Sibling(Cond);
                  }
                  if (fC->Type(Cond) == VObjectType::slConstant_expression) {
                    bool validValue;
                    condVal = m_helper.getValue(validValue, parentDef, fC, Cond,
                                                m_compileDesign, nullptr,
                                                parent, true, false);
                  } else {
                    // It is not an else-if
                    condVal = true;
                  }

                } else {
                  // It is not an else-if
                  condVal = true;
                }

                if (condVal > 0) {
                  activeBranch = true;
                  childId = tmp;
                  break;
                } else {
                  // Else branch
                  tmp = fC->Sibling(Cond);
                }

              } else {  // There is no Else stmt
                activeBranch = false;
                break;
              }
            }
            if (!activeBranch) continue;

            // refresh instName
            NodeId blockNameId = fC->Child(tmp);
            if (fC->Type(blockNameId) == VObjectType::slStringConst ||
                fC->Type(blockNameId) ==
                    VObjectType::slGenerate_block) {  // if-else
              if (fC->Type(blockNameId) == VObjectType::slGenerate_block) {
                NodeId Generate_item = fC->Child(blockNameId);
                NodeId Module_or_generate_item = fC->Child(Generate_item);
                NodeId Module_common_item = fC->Child(Module_or_generate_item);
                NodeId Conditional_generate_construct =
                    fC->Child(Module_common_item);
                NodeId If_generate_construct =
                    fC->Child(Conditional_generate_construct);
                if (fC->Type(If_generate_construct) ==
                    slIf_generate_construct) {
                  if (fC->Type(childId) == slGenerate_block)
                    childId = fC->Child(childId);
                  blockIds = fC->sl_collect_all(childId, btypes, true);
                  if (!blockIds.empty()) {
                    NodeId blockId = blockIds[0];
                    NodeId blockNameId = fC->Child(blockId);
                    if (fC->Type(blockNameId) == VObjectType::slStringConst) {
                      modName = fC->SymName(blockNameId);
                      subInstanceId = fC->Sibling(blockNameId);
                      childId = subInstanceId;
                    } else {
                      subInstanceId = childId;
                    }
                  }
                } else {
                  subInstanceId = tmp;
                  childId = subInstanceId;
                }
              } else {
                modName = fC->SymName(blockNameId);
                subInstanceId = tmp;
                childId = subInstanceId;
              }

            } else {  // if-else-if
              blockIds = fC->sl_collect_all(childId, btypes, true);
              if (!blockIds.empty()) {
                NodeId blockId = blockIds[0];
                NodeId blockNameId = fC->Child(blockId);
                if (fC->Type(blockNameId) == VObjectType::slStringConst) {
                  modName = fC->SymName(blockNameId);
                  subInstanceId = fC->Sibling(blockNameId);
                  childId = subInstanceId;
                } else {
                  subInstanceId = childId;
                }
              }
            }
            instName = modName;
          }
        }
      }

      libName = fC->getLibrary()->getName();
      // fullName = parent->getModuleName() + "." + instName;
      // def = design->getComponentDefinition(fullName);

      std::string indexedModName = parent->getFullPathName() + "." + modName;
      def = design->getComponentDefinition(indexedModName);
      if (def == nullptr) {
        def = m_moduleDefFactory->newModuleDefinition(fC, subInstanceId,
                                                      indexedModName);
        if (DesignComponent* defParent = parent->getDefinition())
          def->setParentScope(defParent);
        design->addModuleDefinition(indexedModName, (ModuleDefinition*)def);
      }

      // std::cout << "Inst:" << fullName << ", modName:" << modName <<
      // std::endl; for (auto param : parent->getMappedValues()) {
      //  std::cout << param.first << " " << param.second.first->uhdmValue() <<
      //  std::endl;
      //}

      // Compile generate block
      ((ModuleDefinition*)def)->setGenBlockId(childId);
      FunctorCompileModule funct(
          m_compileDesign, (ModuleDefinition*)def, design,
          m_compileDesign->getCompiler()->getSymbolTable(),
          m_compileDesign->getCompiler()->getErrorContainer(), parent);
      funct.operator()();

      child = factory->newModuleInstance(def, fC, subInstanceId, parent,
                                         instName, indexedModName);
      while (childId) {
        elaborateInstance_(def->getFileContents()[0], childId, paramOverride,
                           factory, child, config, allSubInstances);
        childId = fC->Sibling(childId);
        if (fC->Type(childId) == slGenerate_block) {
          NodeId subChild = fC->Child(childId);
          if (fC->Type(subChild) == slGenerate_block) {
            break;
          }
        }
        if (fC->Type(childId) == slGenerate_module_item) {
          NodeId node = fC->Child(childId);
          if (fC->Type(node) == slGenerate_module_conditional_statement) {
            break;
          }
          if (fC->Type(node) == slGenerate_module_block) {
            break;
          }
        }
        if (fC->Type(childId) == slElse) break;
        if (fC->Type(childId) == slEnd) break;
      }
      parent->addSubInstance(child);
    }
    // Named blocks
    else if (type == slSeq_block || type == slPar_block) {
      std::string libName = fC->getLibrary()->getName();
      std::string fullName = parent->getModuleName() + "." + instName;

      def = design->getComponentDefinition(fullName);
      if (def == nullptr) {
        def = m_moduleDefFactory->newModuleDefinition(fC, subInstanceId,
                                                      fullName);
        design->addModuleDefinition(fullName, (ModuleDefinition*)def);
      }

      ModuleInstance* child = factory->newModuleInstance(
          def, fC, subInstanceId, parent, instName, modName);
      elaborateInstance_(def->getFileContents()[0], subInstanceId,
                         paramOverride, factory, child, config,
                         allSubInstances);
      parent->addSubInstance(child);

    }
    // Regular module binding
    else {
      NodeId moduleName =
          fC->sl_collect(subInstanceId, VObjectType::slStringConst);
      std::string libName = fC->getLibrary()->getName();
      mname = fC->SymName(moduleName);

      std::vector<std::string> libs;
      if (config) {
        for (const auto& lib : config->getDefaultLibs()) {
          libs.push_back(lib);
        }
        libs.push_back(libName);
      } else {
        libs.push_back(libName);
      }

      for (const auto& lib : libs) {
        modName = lib + "@" + mname;
        def = design->getComponentDefinition(modName);
        if (def) {
          break;
        } else {
          modName = parent->getDefinition()->getName() + "::" + mname;
          def = design->getComponentDefinition(modName);
          if (def) {
            break;
          }
        }
      }

      auto itr = m_cellUseClause.find(mname);
      if (itr != m_cellUseClause.end()) {
        UseClause& use = (*itr).second;
        switch (use.getType()) {
          case UseClause::UseModule: {
            std::string name = use.getName();
            def = design->getComponentDefinition(name);
            if (def) use.setUsed();
            break;
          }
          case UseClause::UseLib: {
            for (const auto& lib : use.getLibs()) {
              modName = lib + "@" + mname;
              def = design->getComponentDefinition(modName);
              if (def) {
                use.setUsed();
                break;
              }
            }
            break;
          }
          default:
            break;
        }
      }

      if (def) childId = def->getNodeIds()[0];

      NodeId tmpId = fC->Sibling(moduleName);
      VObjectType tmpType = fC->Type(tmpId);
      if (tmpType == VObjectType::slParameter_value_assignment ||
          tmpType == slDelay2) {
        paramOverride = tmpId;
      }

      std::vector<int> from;
      std::vector<int> to;
      std::vector<int> index;

      std::vector<VObjectType> insttypes = {
          VObjectType::slHierarchical_instance,
          VObjectType::slN_input_gate_instance,
          VObjectType::slN_output_gate_instance,
          VObjectType::slPull_gate_instance, VObjectType::slUdp_instance};

      std::vector<NodeId> hierInstIds =
          fC->sl_collect_all(subInstanceId, insttypes, true);

      NodeId hierInstId = InvalidNodeId;
      if (!hierInstIds.empty()) hierInstId = hierInstIds[0];

      if (hierInstId == InvalidNodeId) continue;

      while (hierInstId) {
        NodeId instId = fC->sl_collect(hierInstId, slName_of_instance);
        NodeId identifierId = 0;
        if (instId != InvalidNodeId) {
          identifierId = fC->Child(instId);
          instName = fC->SymName(identifierId);
        }

        auto itr =
            m_instUseClause.find(parent->getFullPathName() + "." + instName);
        if (itr != m_instUseClause.end()) {
          UseClause& use = (*itr).second;
          switch (use.getType()) {
            case UseClause::UseModule: {
              std::string name = use.getName();
              def = design->getComponentDefinition(name);
              if (def) use.setUsed();
              break;
            }
            case UseClause::UseLib: {
              for (const auto& lib : use.getLibs()) {
                modName = lib + "@" + mname;
                def = design->getComponentDefinition(modName);
                if (def) {
                  use.setUsed();
                  break;
                }
                break;
              }
              break;
            }
            case UseClause::UseConfig: {
              std::string useConfig = use.getName();
              Config* config =
                  design->getConfigSet()->getMutableConfigByName(useConfig);
              if (config) {
                subConfig = config;
                std::string lib = config->getDesignLib();
                std::string top = config->getDesignTop();
                modName = lib + "@" + top;
                def = design->getComponentDefinition(modName);
                if (def) use.setUsed();
              }
              break;
            }
            default:
              break;
          }
        }

        if (def)
          childId = def->getNodeIds()[0];
        else {
          SymbolTable* st = m_compileDesign->getCompiler()
                                ->getErrorContainer()
                                ->getSymbolTable();
          Location loc(
              st->registerSymbol(fC->getFileName(subInstanceId).string()),
              fC->Line(subInstanceId), 0, st->registerSymbol(modName));
          Error err(ErrorDefinition::ELAB_NO_MODULE_DEFINITION, loc);
          m_compileDesign->getCompiler()->getErrorContainer()->addError(
              err, false, false);
        }

        NodeId unpackedDimId = 0;

        if (identifierId) unpackedDimId = fC->Sibling(identifierId);

        if (unpackedDimId) {
          // Vector instances
          while (unpackedDimId) {
            if (fC->Type(unpackedDimId) == slUnpacked_dimension) {
              NodeId constantRangeId = fC->Child(unpackedDimId);
              NodeId leftNode = fC->Child(constantRangeId);
              NodeId rightNode = fC->Sibling(leftNode);
              bool validValue;
              int64_t left = m_helper.getValue(validValue, parentDef, fC,
                                               leftNode, m_compileDesign,
                                               nullptr, parent, true, false);
              int64_t right = 0;
              if (rightNode && (fC->Type(rightNode) == slConstant_expression))
                right = m_helper.getValue(validValue, parentDef, fC, rightNode,
                                          m_compileDesign, nullptr, parent,
                                          true, false);
              if (left < right) {
                from.push_back(left);
                to.push_back(right);
                index.push_back(left);
              } else {
                from.push_back(right);
                to.push_back(left);
                index.push_back(right);
              }
            }
            unpackedDimId = fC->Sibling(unpackedDimId);
          }
          recurseInstanceLoop_(from, to, index, 0, def, fC, subInstanceId,
                               paramOverride, factory, parent, subConfig,
                               instName, modName, allSubInstances);
        } else {
          // Simple instance
          if (reuseInstance) {
            child = parent;
            child->setNodeId(subInstanceId);
          } else {
            child = factory->newModuleInstance(def, fC, subInstanceId, parent,
                                               instName, modName);
          }
          if (def && (type != VObjectType::slGate_instantiation)) {
            elaborateInstance_(def->getFileContents()[0], childId,
                               paramOverride, factory, child, subConfig,
                               allSubInstances);
          } else {
            // Build black box model
            std::vector<std::string> params;
            collectParams_(params, fC, subInstanceId, child, paramOverride);
            NetlistElaboration* nelab = new NetlistElaboration(m_compileDesign);
            nelab->elaborateInstance(child);
            delete nelab;
          }
          if (!reuseInstance) parent->addSubInstance(child);
        }

        hierInstId = fC->Sibling(hierInstId);
      }
      // std::cout << "INST: " << modName << " " << instName << " " << def <<
      // std::endl;
    }
  }
}

void DesignElaboration::reportElaboration_() {
  unsigned int nbTopLevelModules = 0;
  unsigned int maxDepth = 0;
  unsigned int numberOfInstances = 0;
  unsigned int numberOfLeafInstances = 0;
  unsigned int nbUndefinedModules = 0;
  unsigned int nbUndefinedInstances = 0;

  m_compileDesign->getCompiler()->getDesign()->reportInstanceTreeStats(
      nbTopLevelModules, maxDepth, numberOfInstances, numberOfLeafInstances,
      nbUndefinedModules, nbUndefinedInstances);

  SymbolTable* symtable = m_compileDesign->getCompiler()->getSymbolTable();

  Location loc1(symtable->registerSymbol(std::to_string(nbTopLevelModules)));
  Error err1(ErrorDefinition::ELAB_NB_TOP_LEVEL_MODULES, loc1);
  m_compileDesign->getCompiler()->getErrorContainer()->addError(err1);

  Location loc2(symtable->registerSymbol(std::to_string(maxDepth)));
  Error err2(ErrorDefinition::ELAB_MAX_INSTANCE_DEPTH, loc2);
  m_compileDesign->getCompiler()->getErrorContainer()->addError(err2);

  Location loc3(symtable->registerSymbol(std::to_string(numberOfInstances)));
  Error err3(ErrorDefinition::ELAB_NB_INSTANCES, loc3);
  m_compileDesign->getCompiler()->getErrorContainer()->addError(err3);

  Location loc4(
      symtable->registerSymbol(std::to_string(numberOfLeafInstances)));
  Error err4(ErrorDefinition::ELAB_NB_LEAF_INSTANCES, loc4);
  m_compileDesign->getCompiler()->getErrorContainer()->addError(err4);

  if (nbUndefinedModules) {
    Location loc5(symtable->registerSymbol(std::to_string(nbUndefinedModules)));
    Error err5(ErrorDefinition::ELAB_NB_UNDEF_MODULES, loc5);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err5);
  }

  if (nbUndefinedInstances) {
    Location loc6(
        symtable->registerSymbol(std::to_string(nbUndefinedInstances)));
    Error err6(ErrorDefinition::ELAB_NB_UNDEF_INSTANCES, loc6);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err6);
  }
  CommandLineParser* cl =
      m_compileDesign->getCompiler()->getCommandLineParser();
  if (cl->getDebugInstanceTree() && (!cl->muteStdout())) {
    std::cout << "Instance tree:" << std::endl;
    std::cout
        << m_compileDesign->getCompiler()->getDesign()->reportInstanceTree();
    std::cout << std::endl;
  }
}

void DesignElaboration::collectParams_(std::vector<std::string>& params,
                                       const FileContent* fC, NodeId nodeId,
                                       ModuleInstance* instance,
                                       NodeId parentParamOverride) {
  if (!nodeId) return;
  if (!instance) return;
  bool en_replay =
      m_compileDesign->getCompiler()->getCommandLineParser()->replay();
  Design* design = m_compileDesign->getCompiler()->getDesign();
  SymbolTable* st = m_compileDesign->getCompiler()->getSymbolTable();
  ErrorContainer* errors = m_compileDesign->getCompiler()->getErrorContainer();
  DesignComponent* module = instance->getDefinition();
  // Parameters imported by package imports
  std::vector<FileCNodeId> pack_imports;
  for (const auto& import :
       fC->getObjects(VObjectType::slPackage_import_item)) {
    pack_imports.push_back(import);
  }
  if (module) {
    for (auto import : module->getObjects(VObjectType::slPackage_import_item)) {
      pack_imports.push_back(import);
    }
  }
  for (const auto& pack_import : pack_imports) {
    NodeId pack_id = pack_import.fC->Child(pack_import.nodeId);
    std::string pack_name = pack_import.fC->SymName(pack_id);
    Package* def = design->getPackage(pack_name);
    if (def) {
      auto& paramSet = def->getObjects(VObjectType::slParam_assignment);
      for (const auto& element : paramSet) {
        const FileContent* packageFile = element.fC;
        NodeId param = element.nodeId;

        NodeId ident = packageFile->Child(param);
        const std::string& name = packageFile->SymName(ident);
        if (UHDM::expr* exp = def->getComplexValue(name)) {
          UHDM::Serializer& s = m_compileDesign->getSerializer();
          UHDM::ElaboratorListener listener(&s);
          UHDM::any* pclone = UHDM::clone_tree(exp, s, &listener);
          instance->setComplexValue(name, (UHDM::expr*)pclone);
        } else {
          Value* value = m_exprBuilder.clone(def->getValue(name));
          if (value)
            instance->setValue(name, value, m_exprBuilder,
                               packageFile->Line(param));
        }
        params.push_back(name);
      }
    } else {
      Location loc(
          st->registerSymbol(pack_import.fC->getFileName(pack_id).string()),
          pack_import.fC->Line(pack_id), 0, st->registerSymbol(pack_name));
      Error err(ErrorDefinition::ELAB_UNDEFINED_PACKAGE, loc);
      errors->addError(err);
    }
  }

  std::vector<std::string> moduleParams;
  if (module) {
    for (FileCNodeId param :
         module->getObjects(VObjectType::slParam_assignment)) {
      NodeId ident = param.fC->Child(param.nodeId);
      std::string name = param.fC->SymName(ident);
      params.push_back(name);
      moduleParams.push_back(name);
    }
  }
  std::set<std::string> overridenParams;
  std::vector<VObjectType> types;
  // Param overrides
  if (parentParamOverride) {
    ModuleInstance* parentInstance = instance->getParent();
    DesignComponent* parentDefinition =
        (instance->getParent()) ? instance->getParent()->getDefinition()
                                : instance->getDefinition();
    if (instance->getInstanceBinding()) {
      parentInstance = instance->getInstanceBinding();
      parentDefinition = parentInstance->getDefinition();
    }
    const FileContent* parentFile =
        instance->getParent()->getDefinition()->getFileContents()[0];
    types = {VObjectType::slOrdered_parameter_assignment,
             VObjectType::slNamed_parameter_assignment};
    std::vector<NodeId> overrideParams =
        parentFile->sl_collect_all(parentParamOverride, types);
    if (parentFile->Type(parentParamOverride) == slDelay2) {
      NodeId tmp = parentFile->Child(parentParamOverride);
      if (parentFile->Type(tmp) == slMintypmax_expression) {
        while (tmp) {
          overrideParams.push_back(tmp);
          tmp = parentFile->Sibling(tmp);
        }
      } else {
        overrideParams.push_back(parentParamOverride);
      }
    }
    unsigned int index = 0;
    for (auto paramAssign : overrideParams) {
      NodeId child = parentFile->Child(paramAssign);
      if (parentFile->Type(paramAssign) == slDelay2) {
        child = paramAssign;
      }
      if (parentFile->Type(child) == VObjectType::slStringConst) {
        // Named param
        std::string name = parentFile->SymName(child);
        overridenParams.insert(name);
        NodeId expr = parentFile->Sibling(child);
        if (expr == 0) {
          Location loc(
              st->registerSymbol(parentFile->getFileName(paramAssign).string()),
              parentFile->Line(paramAssign), parentFile->Column(paramAssign),
              st->registerSymbol(name));
          Error err(ErrorDefinition::ELAB_EMPTY_PARAM_OVERRIDE, loc);
          errors->addError(err);
          continue;
        }
        UHDM::expr* complexV = (UHDM::expr*)m_helper.compileExpression(
            parentDefinition, parentFile, expr, m_compileDesign, nullptr,
            parentInstance, true, false);

        Value* value = nullptr;
        bool complex = false;
        if (complexV) {
          UHDM::UHDM_OBJECT_TYPE exprtype = complexV->UhdmType();
          if (exprtype == UHDM::uhdmconstant) {
            UHDM::constant* c = (UHDM::constant*)complexV;
            if (en_replay && m_helper.errorOnNegativeConstant(
                                 parentDefinition, complexV, m_compileDesign,
                                 parentInstance)) {
              bool replay = false;
              // GDB: p replay=true
              if (replay) {
                m_helper.compileExpression(parentDefinition, parentFile, expr,
                                           m_compileDesign, nullptr,
                                           parentInstance, true, false);

                m_exprBuilder.evalExpr(parentFile, expr, parentInstance, true);
              }
            }
            const std::string& v = c->VpiValue();
            value = m_exprBuilder.fromVpiValue(v, c->VpiSize());
          } else if ((exprtype == UHDM::uhdmoperation) ||
                     (exprtype == UHDM::uhdmfunc_call) ||
                     (exprtype == UHDM::uhdmsys_func_call) ||
                     (exprtype == UHDM::uhdmindexed_part_select) ||
                     (exprtype == UHDM::uhdmhier_path)) {
            if (instance) {
              complex = true;
              if (m_helper.substituteAssignedValue(complexV, m_compileDesign)) {
                instance->setComplexValue(name, complexV);
                instance->setOverridenParam(name);
              } else {
                complexV = (UHDM::expr*)m_helper.compileExpression(
                    parentDefinition, parentFile, expr, m_compileDesign,
                    nullptr, parentInstance, false, false);
                if (complexV->UhdmType() == UHDM::uhdmref_obj) {
                  UHDM::ref_obj* ref = (UHDM::ref_obj*)complexV;
                  if (ref->Actual_group() == nullptr) {
                    ref->Actual_group(m_helper.bindParameter(
                        parentDefinition, parentInstance, ref->VpiName(),
                        m_compileDesign, true));
                  }
                }
                instance->setComplexValue(name, complexV);
                instance->setOverridenParam(name);
              }
            }
          } else if (exprtype == UHDM::uhdmref_obj) {
            bool isTypeParam = false;
            if (module) {
              Parameter* p = module->getParameter(name);
              if (p) isTypeParam = p->isTypeParam();
            }
            if (!isTypeParam) {
              complex = true;
              UHDM::ref_obj* ref = (UHDM::ref_obj*)complexV;
              if (ref->Actual_group() == nullptr) {
                ref->Actual_group(m_helper.bindParameter(
                    parentDefinition, parentInstance, ref->VpiName(),
                    m_compileDesign, true));
              }
              instance->setComplexValue(name, complexV);
              instance->setOverridenParam(name);
            }
          } else if (exprtype == UHDM::uhdmparameter) {
            UHDM::parameter* param = (UHDM::parameter*)complexV;
            const std::string& pname = param->VpiName();
            const UHDM::typespec* tps = param->Typespec();
            const UHDM::instance* pinst = tps->Instance();
            if (pinst->UhdmType() == UHDM::uhdmpackage) {
              Design* design = m_compileDesign->getCompiler()->getDesign();
              if (Package* pack = design->getPackage(pinst->VpiName())) {
                if ((complexV = pack->getComplexValue(pname))) {
                  complex = true;
                  instance->setComplexValue(name, complexV);
                  instance->setOverridenParam(name);
                }
                if (complexV == nullptr) {
                  if ((value = pack->getValue(pname))) {
                    instance->setValue(name, value, m_exprBuilder,
                                       parentFile->Line(expr));
                    instance->setOverridenParam(name);
                  }
                }
              }
            } else if (ValuedComponentI* parent = instance->getParent()) {
              complexV = parent->getComplexValue(pname);
              if (complexV) {
                complex = true;
                instance->setComplexValue(name, complexV);
                instance->setOverridenParam(name);
              } else if ((value = parent->getValue(pname, m_exprBuilder))) {
                instance->setValue(name, value, m_exprBuilder,
                                   parentFile->Line(expr));
                instance->setOverridenParam(name);
              }
            }
          }
        }
        if (complex == false) {
          if (value == nullptr) {
            if (module) {
              Parameter* p = module->getParameter(name);
              bool isTypeParam = false;
              if (p) isTypeParam = p->isTypeParam();
              value = m_exprBuilder.evalExpr(parentFile, expr, parentInstance,
                                             isTypeParam);
              if (en_replay && m_helper.errorOnNegativeConstant(
                                   parentDefinition, value, m_compileDesign,
                                   parentInstance)) {
                bool replay = false;
                // GDB: p replay=true
                if (replay) {
                  m_exprBuilder.evalExpr(parentFile, expr, parentInstance,
                                         isTypeParam);
                }
              }
            }
          }
          if (value == nullptr || (value && !value->isValid())) {
            bool replay = false;
            // GDB: p replay=true
            if (replay) {
              m_helper.compileExpression(parentDefinition, parentFile, expr,
                                         m_compileDesign, nullptr,
                                         parentInstance, true, false);
            }

            const std::string& pname = parentFile->SymName(child);
            NodeId param_expression = parentFile->Sibling(child);
            NodeId data_type = parentFile->Child(param_expression);
            NodeId type = parentFile->Child(data_type);
            Parameter* param =
                new Parameter(parentFile, expr, pname, type, true);
            instance->getTypeParams().push_back(param);
            // Set the invalid value as a marker for netlist elaboration
            instance->setValue(name, value, m_exprBuilder,
                               parentFile->Line(expr));
            instance->setOverridenParam(name);
          } else {
            instance->setValue(name, value, m_exprBuilder,
                               parentFile->Line(expr));
            instance->setOverridenParam(name);
          }
        }
      } else if (module) {
        // Index param
        NodeId expr = child;
        const DesignComponent::ParameterVec& params =
            module->getOrderedParameters();
        Parameter* p = nullptr;
        bool isTypeParam = false;
        if (index < params.size()) {
          p = params.at(index);
          isTypeParam = p->isTypeParam();
        }

        UHDM::expr* complexV = (UHDM::expr*)m_helper.compileExpression(
            parentDefinition, parentFile, expr, m_compileDesign, nullptr,
            parentInstance, true, false);

        Value* value = nullptr;
        bool complex = false;

        std::string name = "OUT_OF_RANGE_PARAM_INDEX";
        if (index < moduleParams.size()) {
          name = moduleParams[index];
          overridenParams.insert(name);
        } else {
          if (parentFile->Type(expr) != slDelay2) {
            Location loc(st->registerSymbol(
                             parentFile->getFileName(paramAssign).string()),
                         parentFile->Line(paramAssign), 0,
                         st->registerSymbol(std::to_string(index)));
            Error err(ErrorDefinition::ELAB_OUT_OF_RANGE_PARAM_INDEX, loc);
            errors->addError(err);
          }
        }

        if (complexV) {
          if (complexV->UhdmType() == UHDM::uhdmconstant) {
            UHDM::constant* c = (UHDM::constant*)complexV;
            const std::string& v = c->VpiValue();
            value = m_exprBuilder.fromVpiValue(v, c->VpiSize());
          } else if (complexV->UhdmType() == UHDM::uhdmoperation) {
            if (instance) {
              complex = true;
              instance->setComplexValue(name, complexV);
              instance->setOverridenParam(name);
              m_helper.reorderAssignmentPattern(module, p->getUhdmParam(),
                                                complexV, m_compileDesign,
                                                instance, 0);
            }
          }
        }
        if (complex == false) {
          if (value == nullptr)
            value = m_exprBuilder.evalExpr(parentFile, expr, parentInstance,
                                           isTypeParam);
        }

        if ((complex == false) && value && value->isValid()) {
          instance->setValue(name, value, m_exprBuilder,
                             parentFile->Line(expr));
          instance->setOverridenParam(name);
        }

        index++;
      }
    }
  }

  // Command line override
  if (instance->getParent() == nullptr) {  // Top level only
    CommandLineParser* cmdLine =
        m_compileDesign->getCompiler()->getCommandLineParser();
    const std::map<SymbolId, std::string>& useroverrides =
        cmdLine->getParamList();
    for (const auto& [nameId, value] : useroverrides) {
      const std::string& name = cmdLine->getSymbolTable().getSymbol(nameId);
      Value* val = m_exprBuilder.fromString(value);
      if (val) {
        instance->setValue(name, val, m_exprBuilder, 0);
        overridenParams.insert(name);
      }
      Parameter* p = module->getParameter(name);
      if (p) {
        p->setTypespec(nullptr);
        if (UHDM::parameter* param =
                any_cast<UHDM::parameter*>(p->getUhdmParam())) {
          param->Typespec(nullptr);
        }
      }
    }
  }

  // Defparams
  types = {VObjectType::slDefparam_assignment};
  std::vector<VObjectType> stopPoints = {
      VObjectType::slConditional_generate_construct,
      VObjectType::slGenerate_module_conditional_statement,
      VObjectType::slGenerate_interface_conditional_statement,
      VObjectType::slLoop_generate_construct,
      VObjectType::slGenerate_module_loop_statement,
      VObjectType::slGenerate_interface_loop_statement,
      VObjectType::slPar_block,
      VObjectType::slSeq_block,
      VObjectType::slModule_declaration};

  std::vector<NodeId> defParams = fC->sl_collect_all(nodeId, types, stopPoints);
  for (auto defParam : defParams) {
    NodeId hIdent = fC->Child(defParam);
    NodeId var = 0;
    fC->Child(hIdent);
    if (fC->Type(hIdent) == slHierarchical_identifier)
      var = fC->Child(hIdent);
    else
      var = hIdent;
    NodeId value = fC->Sibling(hIdent);
    std::string fullPath;
    std::string path;
    while (var) {
      if (fC->Type(var) == slStringConst) {
        fullPath += fC->SymName(var);
      }
      var = fC->Sibling(var);
      bool isString = false;
      if (fC->Type(var) == slStringConst) {
        isString = true;
      }
      if (var && isString) {
        fullPath += ".";
      }
    }
    for (char c : fullPath) {
      if (c == '.') break;
      path += c;
    }
    std::string pathRoot;
    pathRoot = fC->getLibrary()->getName() + "@";
    pathRoot += path;
    path = fullPath;

    // path refers to a sub instance
    std::string prefix;
    if (design->findInstance(pathRoot)) {
      std::string p = design->findInstance(pathRoot)->getFullPathName();
      if (p.find('.') != std::string::npos) {
        prefix = instance->getFullPathName() + ".";
      } else {
        prefix = fC->getLibrary()->getName() + "@";
      }
    } else {
      prefix = instance->getFullPathName() + ".";
    }
    path = prefix + path;
    Value* val = m_exprBuilder.evalExpr(fC, value, instance);
    design->addDefParam(path, fC, hIdent, val);
  }

  if (module) {
    for (FileCNodeId param :
         module->getObjects(VObjectType::slParam_assignment)) {
      NodeId ident = param.fC->Child(param.nodeId);
      std::string name = param.fC->SymName(ident);
      if (overridenParams.find(name) == overridenParams.end()) {
        NodeId exprId = param.fC->Sibling(ident);
        while (param.fC->Type(exprId) == slUnpacked_dimension) {
          exprId = param.fC->Sibling(exprId);
        }
        NodeId Data_type = param.fC->Child(exprId);
        if (param.fC->Type(Data_type) != slData_type) {
          // Regular params
          Parameter* p = module->getParameter(name);
          bool isMultidimension = false;
          if (p) {
            isMultidimension = p->isMultidimension();
          }
          if (exprId) {
            UHDM::expr* expr = (UHDM::expr*)m_helper.compileExpression(
                instance->getDefinition(), param.fC, exprId, m_compileDesign,
                nullptr, instance, !isMultidimension, false);
            Value* value = nullptr;
            bool complex = false;
            UHDM::typespec* ts = nullptr;
            if (p) {
              ts = p->getTypespec();
            }
            if (expr) {
              if (expr->UhdmType() == UHDM::uhdmconstant) {
                UHDM::constant* c = (UHDM::constant*)expr;
                if (ts) {
                  if (ts->UhdmType() != UHDM::uhdmunsupported_typespec) {
                    c->Typespec(ts);
                    m_helper.adjustSize(ts, instance->getDefinition(),
                                        m_compileDesign, instance, c);
                  }
                }

                const std::string& v = c->VpiValue();
                value = m_exprBuilder.fromVpiValue(v, c->VpiSize());
                if (ts)
                  m_helper.valueRange(value, ts, instance->getDefinition(),
                                      m_compileDesign, instance);
              } else if (expr->UhdmType() == UHDM::uhdmoperation) {
                if (instance) {
                  complex = true;
                  instance->setComplexValue(name, expr);
                  UHDM::operation* op = (UHDM::operation*)expr;
                  int opType = op->VpiOpType();
                  if (opType == vpiAssignmentPatternOp) {
                    if (ts) {
                      expr = m_helper.expandPatternAssignment(
                          ts, expr, module, m_compileDesign, instance);
                      if (expr) instance->setComplexValue(name, expr);
                    }
                  }
                  if (p) {
                    if (UHDM::typespec* ts = p->getTypespec()) {
                      if (ts->UhdmType() != UHDM::uhdmunsupported_typespec) {
                        op->Typespec(p->getTypespec());
                      }
                    }
                    m_helper.reorderAssignmentPattern(module, p->getUhdmParam(),
                                                      expr, m_compileDesign,
                                                      instance, 0);
                  }
                }
              }
            }

            if ((!complex) && (value == nullptr)) {
              value = m_exprBuilder.evalExpr(param.fC, exprId, instance, true);
            }
            if ((!complex) && value && value->isValid()) {
              instance->setValue(name, value, m_exprBuilder, fC->Line(ident));
            }
          }
        }
      }
    }
  }
}

void DesignElaboration::checkElaboration_() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  design->checkDefParamUsage();
  checkConfigurations_();

  // Command line override
  CommandLineParser* cmdLine =
      m_compileDesign->getCompiler()->getCommandLineParser();
  const std::map<SymbolId, std::string>& useroverrides =
      cmdLine->getParamList();
  for (const auto& [nameId, value] : useroverrides) {
    bool found = false;
    const std::string& name = cmdLine->getSymbolTable().getSymbol(nameId);
    for (ModuleInstance* inst : design->getTopLevelModuleInstances()) {
      DesignComponent* module = inst->getDefinition();
      Parameter* p = module->getParameter(name);
      if (p != nullptr) {
        found = true;
        break;
      }
    }
    if (!found) {
      Location loc(
          m_compileDesign->getCompiler()->getSymbolTable()->registerSymbol(
              name));
      Error err(ErrorDefinition::ELAB_UNKNOWN_PARAMETER, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    }
  }
}

void DesignElaboration::checkConfigurations_() {
  SymbolTable* st = m_compileDesign->getCompiler()->getSymbolTable();
  for (auto& pathUseC : m_cellUseClause) {
    UseClause& useC = pathUseC.second;
    if (!useC.isUsed()) {
      const FileContent* fC = useC.getFileContent();
      Location loc(
          st->registerSymbol(fC->getFileName(useC.getNodeId()).string()),
          fC->Line(useC.getNodeId()), 0, st->registerSymbol(pathUseC.first));
      Error err(ErrorDefinition::ELAB_USE_CLAUSE_IGNORED, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    }
  }
  for (auto& pathUseC : m_instUseClause) {
    UseClause& useC = pathUseC.second;
    if (!useC.isUsed()) {
      const FileContent* fC = useC.getFileContent();
      Location loc(
          st->registerSymbol(fC->getFileName(useC.getNodeId()).string()),
          fC->Line(useC.getNodeId()), 0, st->registerSymbol(pathUseC.first));
      Error err(ErrorDefinition::ELAB_USE_CLAUSE_IGNORED, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    }
  }
}

void DesignElaboration::reduceUnnamedBlocks_() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  std::queue<ModuleInstance*> queue;
  for (auto instance : design->getTopLevelModuleInstances()) {
    queue.push(instance);
  }

  while (!queue.empty()) {
    ModuleInstance* current = queue.front();
    queue.pop();
    if (current == nullptr) continue;
    for (unsigned int i = 0; i < current->getNbChildren(); i++) {
      queue.push(current->getChildren(i));
    }
    const FileContent* fC = current->getFileContent();
    NodeId id = current->getNodeId();
    VObjectType type = fC->Type(id);

    ModuleInstance* parent = current->getParent();
    if (parent) {
      const FileContent* fCP = parent->getFileContent();
      NodeId idP = parent->getNodeId();
      VObjectType typeP = fCP->Type(idP);

      if ((type == VObjectType::slConditional_generate_construct ||
           type == VObjectType::slGenerate_module_conditional_statement ||
           type == VObjectType::slLoop_generate_construct ||
           type == VObjectType::slGenerate_module_loop_statement ||
           type == VObjectType::slGenerate_interface_loop_statement) &&
          (typeP == VObjectType::slConditional_generate_construct ||
           typeP == VObjectType::slGenerate_module_conditional_statement ||
           typeP == VObjectType::slGenerate_interface_conditional_statement ||
           typeP == VObjectType::slLoop_generate_construct ||
           typeP == VObjectType::slGenerate_module_loop_statement ||
           typeP == VObjectType::slGenerate_interface_loop_statement)) {
        std::string fullModName = current->getModuleName();
        fullModName = StringUtils::leaf(fullModName);
        std::string fullModNameP = parent->getModuleName();
        fullModNameP = StringUtils::leaf(fullModNameP);
        if (fullModName.find("genblk") != std::string::npos) {
          if (fullModName == fullModNameP)
            parent->getParent()->overrideParentChild(parent->getParent(),
                                                     parent, current);
        } else {
          if (fullModNameP.find("genblk") != std::string::npos)
            parent->getParent()->overrideParentChild(parent->getParent(),
                                                     parent, current);
        }
      }
    }
  }
}

void DesignElaboration::bind_ports_nets_(std::vector<Signal*>& ports,
                                         std::vector<Signal*>& signals,
                                         const FileContent* fC,
                                         ModuleInstance* instance,
                                         DesignComponent* mod) {
  for (Signal* port : ports) {
    bindPortType_(port, fC, port->getNodeId(), nullptr, instance, mod,
                  ErrorDefinition::COMP_UNDEFINED_TYPE);
  }
  for (Signal* signal : signals) {
    bindPortType_(signal, signal->getFileContent(), signal->getNodeId(),
                  nullptr, instance, mod, ErrorDefinition::COMP_UNDEFINED_TYPE);
  }
}

bool DesignElaboration::bindDataTypes_(ModuleInstance* instance,
                                       DesignComponent* component) {
  if (component == nullptr) return true;
  if (component->getFileContents().empty()) return true;
  const FileContent* fC = component->getFileContents()[0];
  std::vector<Signal*>& ports = component->getPorts();  // Always empty
  std::vector<Signal*>& signals =
      component->getSignals();  // Variables actually
  bind_ports_nets_(ports, signals, fC, instance, component);
  return true;
}

bool DesignElaboration::bindPackagesDataTypes_() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  auto packages = design->getPackageDefinitions();
  for (const auto& packNamePair : packages) {
    Package* package = packNamePair.second;
    const FileContent* fC = package->getFileContents()[0];
    std::vector<Signal*>& ports = package->getPorts();  // Always empty
    std::vector<Signal*>& signals =
        package->getSignals();  // Variables actually
    bind_ports_nets_(ports, signals, fC, nullptr, package);
  }
  return true;
}

bool DesignElaboration::bindDataTypes_() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  auto packages = design->getPackageDefinitions();
  for (const auto& packNamePair : packages) {
    Package* package = packNamePair.second;
    const FileContent* fC = package->getFileContents()[0];
    std::vector<Signal*>& ports = package->getPorts();  // Always empty
    std::vector<Signal*>& signals =
        package->getSignals();  // Variables actually
    bind_ports_nets_(ports, signals, fC, nullptr, package);
  }

  auto modules = design->getModuleDefinitions();
  for (const auto& modNamePair : modules) {
    ModuleDefinition* mod = modNamePair.second;
    VObjectType compType = mod->getType();
    if (mod->getFileContents().empty()) {
      // Built-in primitive
    } else if (compType == VObjectType::slModule_declaration ||
               compType == VObjectType::slInterface_declaration ||
               compType == VObjectType::slConditional_generate_construct ||
               compType == VObjectType::slLoop_generate_construct ||
               compType == VObjectType::slGenerate_item ||
               compType ==
                   VObjectType::slGenerate_module_conditional_statement ||
               compType ==
                   VObjectType::slGenerate_interface_conditional_statement ||
               compType == VObjectType::slGenerate_module_loop_statement ||
               compType == VObjectType::slGenerate_interface_loop_statement ||
               compType == VObjectType::slGenerate_module_named_block ||
               compType == VObjectType::slGenerate_interface_named_block ||
               compType == VObjectType::slGenerate_module_block ||
               compType == VObjectType::slGenerate_interface_block ||
               compType == VObjectType::slGenerate_module_item ||
               compType == VObjectType::slGenerate_interface_item ||
               compType == VObjectType::slGenerate_block) {
      const FileContent* fC = mod->getFileContents()[0];
      std::vector<Signal*>& ports = mod->getPorts();
      std::vector<Signal*>& signals = mod->getSignals();
      bind_ports_nets_(ports, signals, fC, nullptr, mod);
    }
  }
  auto programs = design->getProgramDefinitions();
  for (const auto& programPair : programs) {
    Program* prog = programPair.second;
    const FileContent* fC = prog->getFileContents()[0];
    std::vector<Signal*>& ports = prog->getPorts();
    std::vector<Signal*>& signals = prog->getSignals();
    bind_ports_nets_(ports, signals, fC, nullptr, prog);
  }
  return true;
}

void DesignElaboration::createFileList_() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  std::queue<ModuleInstance*> queue;
  std::set<const FileContent*> files;
  for (const auto& pack : design->getPackageDefinitions()) {
    if (!pack.second->getFileContents().empty()) {
      if (pack.second->getFileContents()[0] != nullptr)
        files.insert(pack.second->getFileContents()[0]);
    }
  }

  for (auto instance : design->getTopLevelModuleInstances()) {
    queue.push(instance);
  }

  while (!queue.empty()) {
    ModuleInstance* current = queue.front();
    DesignComponent* def = current->getDefinition();
    queue.pop();
    if (current == nullptr) continue;
    for (unsigned int i = 0; i < current->getNbChildren(); i++) {
      queue.push(current->getChildren(i));
    }
    const FileContent* fC = current->getFileContent();
    if (fC) {
      files.insert(fC);
    }
    if (def) {
      for (auto f : def->getFileContents()) {
        if (f) {
          files.insert(f);
        }
      }
    }
  }
  CommandLineParser* cmdLine =
      m_compileDesign->getCompiler()->getCommandLineParser();

  if (cmdLine->writePpOutput() || (cmdLine->writePpOutputFileId() != 0)) {
    const fs::path directory =
        cmdLine->getSymbolTable().getSymbol(cmdLine->getFullCompileDir());
    std::ofstream ofs;
    fs::path fileList = directory / "file_elab.lst";
    ofs.open(fileList);
    const std::map<fs::path, std::vector<fs::path>>& ppFileName =
        m_compileDesign->getCompiler()->getPPFileMap();
    if (ofs.good()) {
      for (auto fC : files) {
        auto itr = ppFileName.find(fC->getFileName());
        if (itr != ppFileName.end()) {
          for (const auto& f : itr->second) {
            ofs << f << std::flush << std::endl;
          }
        }
      }
      ofs.close();
    } else {
      std::cout << "Could not create filelist: " << fileList << std::endl;
    }
  }
}
}  // namespace SURELOG
