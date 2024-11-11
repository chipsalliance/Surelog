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
 * File:   SLAPI.cpp
 * Author: alain
 *
 * Created on May 13, 2017, 4:42 PM
 */

#include "Surelog/API/SLAPI.h"

#ifdef SURELOG_WITH_PYTHON
#include "Surelog/API/SV3_1aPythonListener.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/SourceCompile/PythonListen.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#endif

#include <antlr4-runtime.h>

#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

#include "Surelog/Common/FileSystem.h"
#include "Surelog/Design/Design.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/Waiver.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Testbench/Program.h"
#include "Surelog/Utils/ParseUtils.h"
#include "Surelog/Utils/StringUtils.h"

namespace SURELOG {
void SLsetWaiver(const char* messageId, const char* fileName, uint32_t line,
                 const char* objectName) {
  if (fileName == nullptr && line == 0 && objectName == nullptr) {
    Waiver::setWaiver(messageId, "", 0, "");
  } else if (line == 0 && objectName == nullptr) {
    Waiver::setWaiver(messageId, "", 0, fileName);
  } else if (objectName == nullptr) {
    Waiver::setWaiver(messageId, fileName, line, "");
  } else {
    Waiver::setWaiver(messageId, fileName, line, objectName);
  }
}

void SLregisterNewErrorType(const char* messageId, const char* text,
                            const char* secondLine) {
  //[WARNI:PP0103]
  std::string errorId = messageId;
  errorId = StringUtils::rtrim_until(errorId, ']');
  errorId = StringUtils::ltrim_until(errorId, '[');
  ErrorDefinition::ErrorType type = ErrorDefinition::getErrorType(messageId);
  ErrorDefinition::ErrorSeverity severity =
      ErrorDefinition::getErrorSeverity(errorId.substr(0, 5));
  ErrorDefinition::ErrorCategory category =
      ErrorDefinition::getCategory(errorId.substr(6, 2));
  ErrorDefinition::rec(type, severity, category, text, secondLine);
}

void SLoverrideSeverity(const char* messageId, const char* severity) {
  ErrorDefinition::setSeverity(ErrorDefinition::getErrorType(messageId),
                               ErrorDefinition::getErrorSeverity(severity));
}

static bool IsEmpty(const char* str) { return !(str && *str); }

void SLaddError(ErrorContainer* errors, const char* messageId,
                const char* fileName, uint32_t line, uint32_t col,
                const char* objectName) {
  if (errors == nullptr) return;
  FileSystem* const fileSystem = FileSystem::getInstance();
  SymbolTable* symbolTable = errors->getSymbolTable();
  const PathId fileId = IsEmpty(fileName)
                            ? BadPathId
                            : fileSystem->toPathId(fileName, symbolTable);
  const SymbolId objectId = IsEmpty(objectName)
                                ? BadSymbolId
                                : symbolTable->registerSymbol(objectName);
  Location loc(fileId, line, col, objectId);

  ErrorDefinition::ErrorType type = ErrorDefinition::getErrorType(messageId);
  Error err(type, loc);
  errors->addError(err, false, false);
}

void SLaddMLError(ErrorContainer* errors, const char* messageId,
                  const char* fileName1, uint32_t line1, uint32_t col1,
                  const char* objectName1, const char* fileName2,
                  uint32_t line2, uint32_t col2, const char* objectName2) {
  if (errors == nullptr) return;
  FileSystem* const fileSystem = FileSystem::getInstance();
  SymbolTable* symbolTable = errors->getSymbolTable();
  const PathId fileId1 = IsEmpty(fileName1)
                             ? BadPathId
                             : fileSystem->toPathId(fileName1, symbolTable);
  const SymbolId objectId1 = IsEmpty(objectName1)
                                 ? BadSymbolId
                                 : symbolTable->registerSymbol(objectName1);
  Location loc1(fileId1, line1, col1, objectId1);

  PathId fileId2 = IsEmpty(fileName2)
                       ? BadPathId
                       : fileSystem->toPathId(fileName2, symbolTable);
  SymbolId objectId2 = IsEmpty(objectName2)
                           ? BadSymbolId
                           : symbolTable->registerSymbol(objectName2);
  Location loc2(fileId2, line2, col2, objectId2);

  ErrorDefinition::ErrorType type = ErrorDefinition::getErrorType(messageId);
  Error err(type, loc2, loc2);
  errors->addError(err, false, false);
}

void SLaddErrorContext(SV3_1aPythonListener* prog,
                       antlr4::ParserRuleContext* context,
                       const char* messageId, const char* objectName,
                       bool printColumn) {
#ifdef SURELOG_WITH_PYTHON
  SV3_1aPythonListener* listener = prog;
  antlr4::ParserRuleContext* ctx = context;
  ErrorContainer* errors =
      listener->getPythonListen()->getCompileSourceFile()->getErrorContainer();
  ParseUtils::LineColumn lineCol =
      ParseUtils::getLineColumn(listener->getTokenStream(), ctx);
  ErrorDefinition::ErrorType type = ErrorDefinition::getErrorType(messageId);

  Location loc(
      listener->getPythonListen()->getParseFile()->getFileId(lineCol.first),
      listener->getPythonListen()->getParseFile()->getLineNb(lineCol.first),
      printColumn ? lineCol.second : 0,
      listener->getPythonListen()
          ->getCompileSourceFile()
          ->getSymbolTable()
          ->registerSymbol(objectName));
  Error err(type, loc);
  errors->addError(err, false, false);
#else
  std::cerr << "SLaddErrorContext(): Python support not compiled in\n";
#endif
}

void SLaddMLErrorContext(SV3_1aPythonListener* prog,
                         antlr4::ParserRuleContext* context1,
                         antlr4::ParserRuleContext* context2,
                         const char* messageId, const char* objectName1,
                         const char* objectName2, bool printColumn) {
#ifdef SURELOG_WITH_PYTHON
  SV3_1aPythonListener* listener = prog;
  antlr4::ParserRuleContext* ctx1 = context1;
  antlr4::ParserRuleContext* ctx2 = context2;
  ErrorContainer* errors =
      listener->getPythonListen()->getCompileSourceFile()->getErrorContainer();
  ParseUtils::LineColumn lineCol1 =
      ParseUtils::getLineColumn(listener->getTokenStream(), ctx1);
  ParseUtils::LineColumn lineCol2 =
      ParseUtils::getLineColumn(listener->getTokenStream(), ctx2);
  ErrorDefinition::ErrorType type = ErrorDefinition::getErrorType(messageId);

  Location loc1(
      listener->getPythonListen()->getParseFile()->getFileId(lineCol1.first),
      listener->getPythonListen()->getParseFile()->getLineNb(lineCol1.first),
      printColumn ? lineCol1.second : 0,
      listener->getPythonListen()
          ->getCompileSourceFile()
          ->getSymbolTable()
          ->registerSymbol(objectName1));

  Location loc2(
      listener->getPythonListen()->getParseFile()->getFileId(lineCol2.first),
      listener->getPythonListen()->getParseFile()->getLineNb(lineCol2.first),
      printColumn ? lineCol2.second : 0,
      listener->getPythonListen()
          ->getCompileSourceFile()
          ->getSymbolTable()
          ->registerSymbol(objectName2));
  Error err(type, loc1, loc2);
  errors->addError(err, false, false);
#else
  std::cerr << "SLaddMLErrorContext(): Python support not compiled in\n";
#endif
}

std::string SLgetFile(SV3_1aPythonListener* prog,
                      antlr4::ParserRuleContext* context) {
#ifdef SURELOG_WITH_PYTHON
  FileSystem* const fileSystem = FileSystem::getInstance();
  SV3_1aPythonListener* listener = prog;
  ParseFile* parseFile = listener->getPythonListen()->getParseFile();
  return std::string(fileSystem->toPath(parseFile->getFileId(0)));
#else
  std::cerr << "SLgetFile(): Python support not compiled in\n";
  return "";
#endif
}

int32_t SLgetLine(SV3_1aPythonListener* prog,
                  antlr4::ParserRuleContext* context) {
#ifdef SURELOG_WITH_PYTHON
  SV3_1aPythonListener* listener = prog;
  antlr4::ParserRuleContext* ctx = context;
  ParseUtils::LineColumn lineCol =
      ParseUtils::getLineColumn(listener->getTokenStream(), ctx);
  return lineCol.first;
#else
  std::cerr << "SLgetLine(): Python support not compiled in\n";
  return 0;
#endif
}

int32_t SLgetColumn(SV3_1aPythonListener* prog,
                    antlr4::ParserRuleContext* context) {
#ifdef SURELOG_WITH_PYTHON
  SV3_1aPythonListener* listener = prog;
  antlr4::ParserRuleContext* ctx = context;
  ParseUtils::LineColumn lineCol =
      ParseUtils::getLineColumn(listener->getTokenStream(), ctx);
  return lineCol.second;
#else
  std::cerr << "SLgetColumn(): Python support not compiled in\n";
  return 0;
#endif
}

std::string SLgetText(SV3_1aPythonListener* /*prog*/,
                      antlr4::ParserRuleContext* context) {
  antlr4::ParserRuleContext* ctx = context;
  std::vector<antlr4::Token*> tokens = ParseUtils::getFlatTokenList(ctx);
  std::string text;
  for (auto token : tokens) {
    text += token->getText() + " ";
  }
  return text;
}

std::vector<std::string> SLgetTokens(SV3_1aPythonListener* /*prog*/,
                                     antlr4::ParserRuleContext* context) {
  antlr4::ParserRuleContext* ctx = context;
  std::vector<antlr4::Token*> tokens = ParseUtils::getFlatTokenList(ctx);
  std::vector<std::string> body_tokens;
  body_tokens.reserve(tokens.size());
  for (auto token : tokens) {
    body_tokens.push_back(token->getText());
  }
  return body_tokens;
}

antlr4::ParserRuleContext* SLgetParentContext(
    SV3_1aPythonListener* /*prog*/, antlr4::ParserRuleContext* context) {
  antlr4::ParserRuleContext* ctx = context;
  return (antlr4::ParserRuleContext*)ctx->parent;
}

std::vector<antlr4::ParserRuleContext*> SLgetChildrenContext(
    SV3_1aPythonListener* /*prog*/, antlr4::ParserRuleContext* context) {
  antlr4::ParserRuleContext* ctx = context;
  std::vector<antlr4::ParserRuleContext*> children;

  for (antlr4::tree::ParseTree* child : ctx->children) {
    // Get the i-th child node of `parent`.
    antlr4::tree::TerminalNode* node =
        dynamic_cast<antlr4::tree::TerminalNode*>(child);
    if (node) {
      // Terminal node
    } else {
      // Rule
      children.push_back((antlr4::ParserRuleContext*)child);
    }
  }
  return children;
}

RawNodeId SLgetRootNode(FileContent* fC) {
  if (!fC) return InvalidNodeId;
  return fC->getRootNode();
}

std::string SLgetFile(FileContent* fC, RawNodeId id) {
  if (!fC) return "";
  return std::string(
      FileSystem::getInstance()->toPath(fC->getFileId(NodeId(id))));
}

uint32_t SLgetType(FileContent* fC, RawNodeId id) {
  if (!fC) return 0;
  return static_cast<uint32_t>(fC->Type(NodeId(id)));
}

RawNodeId SLgetChild(FileContent* fC, RawNodeId index) {
  if (!fC) return InvalidNodeId;
  return fC->Child(NodeId(index));
}

RawNodeId SLgetSibling(FileContent* fC, RawNodeId index) {
  if (!fC) return InvalidNodeId;
  return fC->Sibling(NodeId(index));
}

RawNodeId SLgetParent(FileContent* fC, RawNodeId index) {
  if (!fC) return InvalidNodeId;
  return fC->Parent(NodeId(index));
}

uint32_t SLgetLine(FileContent* fC, RawNodeId index) {
  if (!fC) return 0;
  return fC->Line(NodeId(index));
}

std::string SLgetName(FileContent* fC, RawNodeId index) {
  if (!fC) return "";
  return std::string(fC->SymName(NodeId(index)));
}

RawNodeId SLgetChild(FileContent* fC, RawNodeId parent, uint32_t type) {
  if (!fC) return InvalidNodeId;
  return fC->sl_get(NodeId(parent), (VObjectType)type);
}

RawNodeId SLgetParent(FileContent* fC, RawNodeId parent, uint32_t type) {
  if (!fC) return InvalidNodeId;
  return fC->sl_parent(NodeId(parent), (VObjectType)type);
}

static std::vector<RawNodeId> transform(const std::vector<NodeId>& input) {
  std::vector<RawNodeId> output;
  output.reserve(input.size());
  std::transform(input.begin(), input.end(), std::back_inserter(output),
                 [](NodeId id) { return (RawNodeId)id; });
  return output;
}

std::vector<RawNodeId> SLgetAll(FileContent* fC, RawNodeId parent,
                                uint32_t type) {
  if (!fC) return {};
  return transform(fC->sl_get_all(NodeId(parent), (VObjectType)type));
}

std::vector<RawNodeId> SLgetAll(FileContent* fC, RawNodeId parent,
                                const std::vector<uint32_t>& types) {
  if (!fC) return {};
  VObjectTypeUnorderedSet vtypes;
  vtypes.reserve(types.size());
  for (auto type : types) vtypes.emplace((VObjectType)type);
  return transform(fC->sl_get_all(NodeId(parent), vtypes));
}

RawNodeId SLcollect(FileContent* fC, RawNodeId parent, uint32_t type) {
  if (!fC) return {};
  return fC->sl_collect(NodeId(parent), (VObjectType)type);
}

std::vector<RawNodeId> SLcollectAll(FileContent* fC, RawNodeId parent,
                                    uint32_t type, bool first) {
  if (fC)
    return transform(
        fC->sl_collect_all(NodeId(parent), (VObjectType)type, first));
  else
    return {};
}

std::vector<RawNodeId> SLcollectAll(FileContent* fC, RawNodeId parent,
                                    const std::vector<uint32_t>& types,
                                    bool first) {
  if (!fC) return {};
  VObjectTypeUnorderedSet vtypes;
  vtypes.reserve(types.size());
  for (auto type : types) vtypes.emplace((VObjectType)type);
  return transform(fC->sl_collect_all(NodeId(parent), vtypes, first));
}

std::vector<RawNodeId> SLcollectAll(FileContent* fC, RawNodeId parent,
                                    const std::vector<uint32_t>& types,
                                    const std::vector<uint32_t>& stopPoints,
                                    bool first) {
  if (!fC) return {};
  VObjectTypeUnorderedSet vtypes;
  vtypes.reserve(types.size());
  for (auto type : types) vtypes.emplace((VObjectType)type);
  VObjectTypeUnorderedSet vstops;
  vstops.reserve(stopPoints.size());
  for (auto type : stopPoints) vstops.emplace((VObjectType)type);
  return transform(fC->sl_collect_all(NodeId(parent), vtypes, vstops, first));
}

uint32_t SLgetnModuleDefinition(Design* design) {
  if (!design) return 0;
  return design->getModuleDefinitions().size();
}

uint32_t SLgetnProgramDefinition(Design* design) {
  if (!design) return 0;
  return design->getProgramDefinitions().size();
}

uint32_t SLgetnPackageDefinition(Design* design) {
  if (!design) return 0;
  return design->getPackageDefinitions().size();
}

uint32_t SLgetnClassDefinition(Design* design) {
  if (!design) return 0;
  return design->getUniqueClassDefinitions().size();
}

uint32_t SLgetnTopModuleInstance(Design* design) {
  if (!design) return 0;
  return design->getTopLevelModuleInstances().size();
}

ModuleDefinition* SLgetModuleDefinition(Design* design, uint32_t index) {
  if (!design) return nullptr;
  ModuleNameModuleDefinitionMap::iterator itr =
      design->getModuleDefinitions().begin();
  for (uint32_t i = 0; i < index; i++) itr++;
  return (*itr).second;
}

Program* SLgetProgramDefinition(Design* design, uint32_t index) {
  if (!design) return nullptr;
  ProgramNameProgramDefinitionMap::iterator itr =
      design->getProgramDefinitions().begin();
  for (uint32_t i = 0; i < index; i++) itr++;
  return (*itr).second;
}

Package* SLgetPackageDefinition(Design* design, uint32_t index) {
  if (!design) return nullptr;
  PackageNamePackageDefinitionMultiMap::iterator itr =
      design->getPackageDefinitions().begin();
  for (uint32_t i = 0; i < index; i++) itr++;
  return (*itr).second;
}

ClassDefinition* SLgetClassDefinition(Design* design, uint32_t index) {
  if (!design) return nullptr;
  ClassNameClassDefinitionMap::iterator itr =
      design->getUniqueClassDefinitions().begin();
  for (uint32_t i = 0; i < index; i++) itr++;
  return (*itr).second;
}

ModuleInstance* SLgetTopModuleInstance(Design* design, uint32_t index) {
  if (!design) return nullptr;
  return design->getTopLevelModuleInstances()[index];
}

std::string SLgetModuleName(ModuleDefinition* module) {
  if (!module) return "";
  return std::string(module->getName());
}

template <typename ClassOrPackageOrProgram>
static bool ModuleHasFirstFileContent(const ClassOrPackageOrProgram* module) {
  if (!module) return false;
  if (module->getFileContents().empty()) return false;
  return module->getFileContents()[0] != nullptr;
}

std::string SLgetModuleFile(ModuleDefinition* module) {
  if (!ModuleHasFirstFileContent(module)) return "";
  return std::string(FileSystem::getInstance()->toPath(
      module->getFileContents()[0]->getFileId(module->getNodeIds()[0])));
}

uint32_t SLgetModuleLine(ModuleDefinition* module) {
  if (!ModuleHasFirstFileContent(module)) return 0;
  return module->getFileContents()[0]->Line(module->getNodeIds()[0]);
}

VObjectType SLgetModuleType(ModuleDefinition* module) {
  if (!module) return VObjectType::slNoType;
  return module->getType();
}

FileContent* SLgetModuleFileContent(ModuleDefinition* module) {
  if (!ModuleHasFirstFileContent(module)) return nullptr;
  // TODO(alain): fix const cast.
  return const_cast<FileContent*>(module->getFileContents()[0]);
}

RawNodeId SLgetModuleRootNode(ModuleDefinition* module) {
  if (!module || module->getNodeIds().empty()) return InvalidNodeId;
  return module->getNodeIds()[0];
}

std::string SLgetClassName(ClassDefinition* module) {
  if (!module) return "";
  return std::string(module->getName());
}

std::string SLgetClassFile(ClassDefinition* module) {
  if (!ModuleHasFirstFileContent(module)) return "";
  return std::string(FileSystem::getInstance()->toPath(
      module->getFileContents()[0]->getFileId(module->getNodeIds()[0])));
}

uint32_t SLgetClassLine(ClassDefinition* module) {
  if (!ModuleHasFirstFileContent(module)) return 0;
  return module->getFileContents()[0]->Line(module->getNodeIds()[0]);
}

VObjectType SLgetClassType(ClassDefinition* module) {
  if (!module) return VObjectType::slNoType;
  return module->getType();
}

FileContent* SLgetClassFileContent(ClassDefinition* module) {
  if (!ModuleHasFirstFileContent(module)) return nullptr;
  // TODO(Alain): Fix api.
  return const_cast<FileContent*>(module->getFileContents()[0]);
}

RawNodeId SLgetClassRootNode(ClassDefinition* module) {
  if (!module || module->getNodeIds().empty()) return InvalidNodeId;
  return module->getNodeIds()[0];
}

std::string SLgetPackageName(Package* module) {
  if (!module) return "";
  return std::string(module->getName());
}

std::string SLgetPackageFile(Package* module) {
  if (!ModuleHasFirstFileContent(module)) return "";
  return std::string(FileSystem::getInstance()->toPath(
      module->getFileContents()[0]->getFileId(module->getNodeIds()[0])));
}

uint32_t SLgetPackageLine(Package* module) {
  if (!ModuleHasFirstFileContent(module)) return 0;
  return module->getFileContents()[0]->Line(module->getNodeIds()[0]);
}

VObjectType SLgetPackageType(Package* module) {
  if (!module) return VObjectType::slNoType;
  return module->getType();
}

FileContent* SLgetPackageFileContent(Package* module) {
  if (!ModuleHasFirstFileContent(module)) return nullptr;
  return const_cast<FileContent*>(module->getFileContents()[0]);
}

RawNodeId SLgetPackageRootNode(Package* module) {
  if (!module || module->getNodeIds().empty()) return InvalidNodeId;
  return module->getNodeIds()[0];
}

std::string SLgetProgramName(Program* module) {
  if (!module) return "";
  return std::string(module->getName());
}

std::string SLgetProgramFile(Program* module) {
  if (!ModuleHasFirstFileContent(module)) return "";
  return std::string(FileSystem::getInstance()->toPath(
      module->getFileContents()[0]->getFileId(module->getNodeIds()[0])));
}

uint32_t SLgetProgramLine(Program* module) {
  if (!ModuleHasFirstFileContent(module)) return 0;
  return module->getFileContents()[0]->Line(module->getNodeIds()[0]);
}

VObjectType SLgetProgramType(Program* module) {
  if (!module) return VObjectType::slNoType;
  return module->getType();
}

FileContent* SLgetProgramFileContent(Program* module) {
  if (!ModuleHasFirstFileContent(module)) return nullptr;
  return const_cast<FileContent*>(module->getFileContents()[0]);
}

RawNodeId SLgetProgramRootNode(Program* module) {
  if (!module || module->getNodeIds().empty()) return InvalidNodeId;
  return module->getNodeIds()[0];
}

VObjectType SLgetInstanceType(ModuleInstance* instance) {
  if (!instance) return VObjectType::slNoType;
  return instance->getType();
}

VObjectType SLgetInstanceModuleType(ModuleInstance* instance) {
  if (!instance) return VObjectType::slNoType;
  return instance->getModuleType();
}

std::string SLgetInstanceName(ModuleInstance* instance) {
  if (!instance) return "";
  return instance->getInstanceName();
}

std::string SLgetInstanceFullPathName(ModuleInstance* instance) {
  if (!instance) return "";
  return instance->getFullPathName();
}

std::string SLgetInstanceModuleName(ModuleInstance* instance) {
  if (!instance) return "";
  return std::string(instance->getModuleName());
}

DesignComponent* SLgetInstanceDefinition(ModuleInstance* instance) {
  if (!instance) return nullptr;
  return instance->getDefinition();
}

std::string SLgetInstanceFileName(ModuleInstance* instance) {
  if (!instance) return "";
  return std::string(FileSystem::getInstance()->toPath(
      instance->getFileContent()->getFileId(instance->getNodeId())));
}

FileContent* SLgetInstanceFileContent(ModuleInstance* instance) {
  if (!instance) return nullptr;
  // TODO(Alain): fix to return const
  return const_cast<FileContent*>(instance->getFileContent());
}

RawNodeId SLgetInstanceNodeId(ModuleInstance* instance) {
  if (!instance) return InvalidNodeId;
  return instance->getNodeId();
}

uint32_t SLgetInstanceLine(ModuleInstance* instance) {
  if (!instance) return 0;
  return instance->getLineNb();
}

uint32_t SLgetnInstanceChildren(ModuleInstance* instance) {
  if (!instance) return 0;
  return instance->getNbChildren();
}

ModuleInstance* SLgetInstanceChildren(ModuleInstance* instance, uint32_t i) {
  if (!instance) return nullptr;
  return instance->getChildren(i);
}

ModuleInstance* SLgetInstanceParent(ModuleInstance* instance) {
  if (!instance) return nullptr;
  return instance->getParent();
}
}  // namespace SURELOG
