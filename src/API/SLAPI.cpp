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
#include "API/SLAPI.h"

#include <string.h>

#include <cstdlib>
#include <iostream>

#include "API/PythonAPI.h"
#ifdef SURELOG_WITH_PYTHON
#include "API/SV3_1aPythonListener.h"
#endif

#include "CommandLine/CommandLineParser.h"
#include "Design/FileContent.h"
#include "ErrorReporting/ErrorContainer.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/Waiver.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/SymbolTable.h"
#include "Testbench/ClassDefinition.h"
#include "Utils/FileUtils.h"
#include "Utils/ParseUtils.h"
#include "Utils/StringUtils.h"
#include "antlr4-runtime.h"
#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"

namespace SURELOG {
void SLsetWaiver(const char* messageId, const char* fileName, unsigned int line,
                 const char* objectName) {
  if (fileName == 0 && line == 0 && objectName == 0) {
    Waiver::setWaiver(messageId, "", 0, "");
  } else if (line == 0 && objectName == 0) {
    Waiver::setWaiver(messageId, "", 0, fileName);
  } else if (objectName == 0) {
    Waiver::setWaiver(messageId, fileName, line, "");
  } else {
    Waiver::setWaiver(messageId, fileName, line, objectName);
  }
}

void SLregisterNewErrorType(const char* messageId, const char* text,
                            const char* secondLine) {
  //[WARNI:PP0103]
  std::string errorId = messageId;
  errorId = StringUtils::rtrim(errorId, ']');
  errorId = StringUtils::ltrim(errorId, '[');
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

void SLaddError(ErrorContainer* errors, const char* messageId,
                const char* fileName, unsigned int line, unsigned int col,
                const char* objectName) {
  if (errors == NULL) return;
  SymbolTable* symbolTable = errors->getSymbolTable();
  SymbolId fileId = 0;
  if (fileName && (strcmp(fileName, "")))
    fileId = symbolTable->registerSymbol(fileName);
  SymbolId objectId = 0;
  if (objectName && (strcmp(objectName, "")))
    objectId = symbolTable->registerSymbol(objectName);
  Location loc(fileId, line, col, objectId);

  ErrorDefinition::ErrorType type = ErrorDefinition::getErrorType(messageId);
  Error err(type, loc);
  errors->addError(err, false, false);
}

void SLaddMLError(ErrorContainer* errors, const char* messageId,
                  const char* fileName1, unsigned int line1, unsigned int col1,
                  const char* objectName1, const char* fileName2,
                  unsigned int line2, unsigned int col2,
                  const char* objectName2) {
  if (errors == NULL) return;
  SymbolTable* symbolTable = errors->getSymbolTable();
  SymbolId fileId1 = 0;
  if (fileName1 && (strcmp(fileName1, "")))
    fileId1 = symbolTable->registerSymbol(fileName1);
  SymbolId objectId1 = 0;
  if (objectName1 && (strcmp(objectName1, "")))
    objectId1 = symbolTable->registerSymbol(objectName1);
  Location loc1(fileId1, line1, col1, objectId1);

  SymbolId fileId2 = 0;
  if (fileName2 && (strcmp(fileName2, "")))
    fileId2 = symbolTable->registerSymbol(fileName2);
  SymbolId objectId2 = 0;
  if (objectName2 && (strcmp(objectName2, "")))
    objectId2 = symbolTable->registerSymbol(objectName2);
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
  SV3_1aPythonListener* listener = (SV3_1aPythonListener*)prog;
  antlr4::ParserRuleContext* ctx = (antlr4::ParserRuleContext*)context;
  ErrorContainer* errors =
      listener->getPythonListen()->getCompileSourceFile()->getErrorContainer();
  std::pair<int, int> lineCol =
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
  SV3_1aPythonListener* listener = (SV3_1aPythonListener*)prog;
  antlr4::ParserRuleContext* ctx1 = (antlr4::ParserRuleContext*)context1;
  antlr4::ParserRuleContext* ctx2 = (antlr4::ParserRuleContext*)context2;
  ErrorContainer* errors =
      listener->getPythonListen()->getCompileSourceFile()->getErrorContainer();
  std::pair<int, int> lineCol1 =
      ParseUtils::getLineColumn(listener->getTokenStream(), ctx1);
  std::pair<int, int> lineCol2 =
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
  SV3_1aPythonListener* listener = (SV3_1aPythonListener*)prog;
  std::string file =
      listener->getPythonListen()->getParseFile()->getFileName(0);
  return file;
#else
  std::cerr << "SLgetFile(): Python support not compiled in\n";
  return "";
#endif
}

int SLgetLine(SV3_1aPythonListener* prog, antlr4::ParserRuleContext* context) {
#ifdef SURELOG_WITH_PYTHON
  SV3_1aPythonListener* listener = (SV3_1aPythonListener*)prog;
  antlr4::ParserRuleContext* ctx = (antlr4::ParserRuleContext*)context;
  std::pair<int, int> lineCol =
      ParseUtils::getLineColumn(listener->getTokenStream(), ctx);
  return lineCol.first;
#else
  std::cerr << "SLgetLine(): Python support not compiled in\n";
  return 0;
#endif
}

int SLgetColumn(SV3_1aPythonListener* prog,
                antlr4::ParserRuleContext* context) {
#ifdef SURELOG_WITH_PYTHON
  SV3_1aPythonListener* listener = (SV3_1aPythonListener*)prog;
  antlr4::ParserRuleContext* ctx = (antlr4::ParserRuleContext*)context;
  std::pair<int, int> lineCol =
      ParseUtils::getLineColumn(listener->getTokenStream(), ctx);
  return lineCol.second;
#else
  std::cerr << "SLgetColumn(): Python support not compiled in\n";
  return 0;
#endif
}

std::string SLgetText(SV3_1aPythonListener* /*prog*/,
                      antlr4::ParserRuleContext* context) {
  antlr4::ParserRuleContext* ctx = (antlr4::ParserRuleContext*)context;
  std::vector<antlr4::Token*> tokens = ParseUtils::getFlatTokenList(ctx);
  std::string text;
  for (auto token : tokens) {
    text += token->getText() + " ";
  }
  return text;
}

std::vector<std::string> SLgetTokens(SV3_1aPythonListener* /*prog*/,
                                     antlr4::ParserRuleContext* context) {
  antlr4::ParserRuleContext* ctx = (antlr4::ParserRuleContext*)context;
  std::vector<antlr4::Token*> tokens = ParseUtils::getFlatTokenList(ctx);
  std::vector<std::string> body_tokens;
  for (auto token : tokens) {
    body_tokens.push_back(token->getText());
  }
  return body_tokens;
}

antlr4::ParserRuleContext* SLgetParentContext(
    SV3_1aPythonListener* /*prog*/, antlr4::ParserRuleContext* context) {
  antlr4::ParserRuleContext* ctx = (antlr4::ParserRuleContext*)context;
  return (antlr4::ParserRuleContext*)ctx->parent;
}

std::vector<antlr4::ParserRuleContext*> SLgetChildrenContext(
    SV3_1aPythonListener* /*prog*/, antlr4::ParserRuleContext* context) {
  antlr4::ParserRuleContext* ctx = (antlr4::ParserRuleContext*)context;
  std::vector<antlr4::ParserRuleContext*> children;

  for (unsigned int i = 0; i < ctx->children.size(); i++) {
    // Get the i-th child node of `parent`.
    antlr4::tree::ParseTree* child = ctx->children[i];
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

NodeId SLgetRootNode(FileContent* fC) {
  if (!fC) return 0;
  return fC->getRootNode();
}

std::string SLgetFile(FileContent* fC, NodeId id) {
  if (!fC) return "";
  return std::string(fC->getSymbolTable()->getSymbol(fC->getFileId(id)));
}

unsigned int SLgetType(FileContent* fC, NodeId id) {
  if (!fC) return 0;
  return fC->Type(id);
}

NodeId SLgetChild(FileContent* fC, NodeId index) {
  if (!fC) return 0;
  return fC->Child(index);
}

NodeId SLgetSibling(FileContent* fC, NodeId index) {
  if (!fC) return 0;
  return fC->Sibling(index);
}

NodeId SLgetParent(FileContent* fC, NodeId index) {
  if (!fC) return 0;
  return fC->Parent(index);
}

unsigned int SLgetLine(FileContent* fC, NodeId index) {
  if (!fC) return 0;
  return fC->Line(index);
}

std::string SLgetName(FileContent* fC, NodeId index) {
  if (!fC) return "";
  return std::string(fC->SymName(index));
}

NodeId SLgetChild(FileContent* fC, NodeId parent, unsigned int type) {
  if (!fC) return 0;
  return fC->sl_get(parent, (VObjectType)type);
}

NodeId SLgetParent(FileContent* fC, NodeId parent, unsigned int type) {
  if (!fC) return 0;
  return fC->sl_parent(parent, (VObjectType)type);
}

std::vector<unsigned int> SLgetAll(FileContent* fC, NodeId parent,
                                   unsigned int type) {
  if (!fC) return {};
  return fC->sl_get_all(parent, (VObjectType)type);
}

std::vector<unsigned int> SLgetAll(FileContent* fC, NodeId parent,
                                   std::vector<unsigned int> types) {
  if (!fC) return {};
  std::vector<VObjectType> vtypes;
  for (auto type : types) vtypes.push_back((VObjectType)type);
  return fC->sl_get_all(parent, vtypes);
}

NodeId SLcollect(FileContent* fC, NodeId parent, unsigned int type) {
  if (!fC) return {};
  return fC->sl_collect(parent, (VObjectType)type);
}

std::vector<unsigned int> SLcollectAll(FileContent* fC, NodeId parent,
                                       unsigned int type, bool first) {
  if (fC)
    return fC->sl_collect_all(parent, (VObjectType)type, first);
  else
    return {};
}

std::vector<unsigned int> SLcollectAll(FileContent* fC, NodeId parent,
                                       std::vector<unsigned int> types,
                                       bool first) {
  if (!fC) return {};
  std::vector<VObjectType> vtypes;
  for (auto type : types) vtypes.push_back((VObjectType)type);
  return fC->sl_collect_all(parent, vtypes, first);
}

std::vector<unsigned int> SLcollectAll(FileContent* fC, NodeId parent,
                                       std::vector<unsigned int> types,
                                       std::vector<unsigned int> stopPoints,
                                       bool first) {
  if (!fC) return {};
  std::vector<VObjectType> vtypes;
  for (auto type : types) vtypes.push_back((VObjectType)type);
  std::vector<VObjectType> vstops;
  for (auto type : stopPoints) vstops.push_back((VObjectType)type);
  return fC->sl_collect_all(parent, vtypes, vstops, first);
}

unsigned int SLgetnModuleDefinition(Design* design) {
  if (!design) return 0;
  return design->getModuleDefinitions().size();
}

unsigned int SLgetnProgramDefinition(Design* design) {
  if (!design) return 0;
  return design->getProgramDefinitions().size();
}

unsigned int SLgetnPackageDefinition(Design* design) {
  if (!design) return 0;
  return design->getPackageDefinitions().size();
}

unsigned int SLgetnClassDefinition(Design* design) {
  if (!design) return 0;
  return design->getUniqueClassDefinitions().size();
}

unsigned int SLgetnTopModuleInstance(Design* design) {
  if (!design) return 0;
  return design->getTopLevelModuleInstances().size();
}

ModuleDefinition* SLgetModuleDefinition(Design* design, unsigned int index) {
  if (!design) return 0;
  ModuleNameModuleDefinitionMap::iterator itr =
      design->getModuleDefinitions().begin();
  for (unsigned int i = 0; i < index; i++) itr++;
  return (*itr).second;
}

Program* SLgetProgramDefinition(Design* design, unsigned int index) {
  if (!design) return 0;
  ProgramNameProgramDefinitionMap::iterator itr =
      design->getProgramDefinitions().begin();
  for (unsigned int i = 0; i < index; i++) itr++;
  return (*itr).second;
}

Package* SLgetPackageDefinition(Design* design, unsigned int index) {
  if (!design) return 0;
  PackageNamePackageDefinitionMultiMap::iterator itr =
      design->getPackageDefinitions().begin();
  for (unsigned int i = 0; i < index; i++) itr++;
  return (*itr).second;
}

ClassDefinition* SLgetClassDefinition(Design* design, unsigned int index) {
  if (!design) return 0;
  ClassNameClassDefinitionMap::iterator itr =
      design->getUniqueClassDefinitions().begin();
  for (unsigned int i = 0; i < index; i++) itr++;
  return (*itr).second;
}

ModuleInstance* SLgetTopModuleInstance(Design* design, unsigned int index) {
  if (!design) return 0;
  return design->getTopLevelModuleInstances()[index];
}

std::string SLgetModuleName(ModuleDefinition* module) {
  if (!module) return "";
  return std::string(module->getName());
}

std::string SLgetModuleFile(ModuleDefinition* module) {
  if (!module) return "";
  if (module->getFileContents().size())
    return std::string(
        module->getFileContents()[0]->getFileName(module->getNodeIds()[0]));
  else
    return "";
}

unsigned int SLgetModuleLine(ModuleDefinition* module) {
  if (!module) return 0;
  if (module->getFileContents().size())
    return module->getFileContents()[0]->Line(module->getNodeIds()[0]);
  else
    return 0;
}

VObjectType SLgetModuleType(ModuleDefinition* module) {
  if (!module) return VObjectType::slNoType;
  return module->getType();
}

FileContent* SLgetModuleFileContent(ModuleDefinition* module) {
  if (!module) return NULL;
  if (module->getFileContents().size())
    // TODO(alain): fix const cast.
    return const_cast<FileContent*>(module->getFileContents()[0]);
  else
    return NULL;
}

NodeId SLgetModuleRootNode(ModuleDefinition* module) {
  if (!module) return 0;
  if (module->getFileContents().size())
    return module->getNodeIds()[0];
  else
    return 0;
}

std::string SLgetClassName(ClassDefinition* module) {
  if (!module) return "";
  return std::string(module->getName());
}

std::string SLgetClassFile(ClassDefinition* module) {
  if (!module) return "";
  if (module->getFileContents().size() && module->getFileContents()[0])
    return std::string(
        module->getFileContents()[0]->getFileName(module->getNodeIds()[0]));
  else
    return "";
}

unsigned int SLgetClassLine(ClassDefinition* module) {
  if (!module) return 0;
  if (module->getFileContents().size() && module->getFileContents()[0])
    return module->getFileContents()[0]->Line(module->getNodeIds()[0]);
  else
    return 0;
}

VObjectType SLgetClassType(ClassDefinition* module) {
  if (!module) return VObjectType::slNoType;
  return module->getType();
}

FileContent* SLgetClassFileContent(ClassDefinition* module) {
  if (!module) return 0;
  if (module->getFileContents().size() && module->getFileContents()[0])
    // TODO(Alain): Fix api.
    return const_cast<FileContent*>(module->getFileContents()[0]);
  else
    return NULL;
}

NodeId SLgetClassRootNode(ClassDefinition* module) {
  if (!module) return 0;
  if (module->getFileContents().size() && module->getFileContents()[0])
    return module->getNodeIds()[0];
  else
    return 0;
}

std::string SLgetPackageName(Package* module) {
  if (!module) return "";
  return std::string(module->getName());
}

std::string SLgetPackageFile(Package* module) {
  if (!module) return "";
  if (module->getFileContents().size())
    return std::string(
        module->getFileContents()[0]->getFileName(module->getNodeIds()[0]));
  else
    return "";
}

unsigned int SLgetPackageLine(Package* module) {
  if (!module) return 0;
  if (module->getFileContents().size())
    return module->getFileContents()[0]->Line(module->getNodeIds()[0]);
  else
    return 0;
}

VObjectType SLgetPackageType(Package* module) {
  if (!module) return VObjectType::slNoType;
  return module->getType();
}

FileContent* SLgetPackageFileContent(Package* module) {
  if (!module) return 0;
  if (module->getFileContents().size())
    return const_cast<FileContent*>(module->getFileContents()[0]);
  else
    return NULL;
}

NodeId SLgetPackageRootNode(Package* module) {
  if (!module) return 0;
  if (module->getFileContents().size())
    return module->getNodeIds()[0];
  else
    return 0;
}

std::string SLgetProgramName(Program* module) {
  if (!module) return "";
  return std::string(module->getName());
}

std::string SLgetProgramFile(Program* module) {
  if (!module) return "";
  if (module->getFileContents().size())
    return std::string(
        module->getFileContents()[0]->getFileName(module->getNodeIds()[0]));
  else
    return "";
}

unsigned int SLgetProgramLine(Program* module) {
  if (!module) return 0;
  if (module->getFileContents().size())
    return module->getFileContents()[0]->Line(module->getNodeIds()[0]);
  else
    return 0;
}

VObjectType SLgetProgramType(Program* module) {
  if (!module) return VObjectType::slNoType;
  return module->getType();
}

FileContent* SLgetProgramFileContent(Program* module) {
  if (!module) return 0;
  if (module->getFileContents().size())
    return const_cast<FileContent*>(module->getFileContents()[0]);
  else
    return NULL;
}

NodeId SLgetProgramRootNode(Program* module) {
  if (!module) return 0;
  if (module->getFileContents().size())
    return module->getNodeIds()[0];
  else
    return 0;
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
  return instance->getModuleName();
}

DesignComponent* SLgetInstanceDefinition(ModuleInstance* instance) {
  if (!instance) return NULL;
  return instance->getDefinition();
}

std::string SLgetInstanceFileName(ModuleInstance* instance) {
  if (!instance) return "";
  return std::string(
      instance->getFileContent()->getFileName(instance->getNodeId()));
}

FileContent* SLgetInstanceFileContent(ModuleInstance* instance) {
  if (!instance) return NULL;
  // TODO(Alain): fix to return const
  return const_cast<FileContent*>(instance->getFileContent());
}

NodeId SLgetInstanceNodeId(ModuleInstance* instance) {
  if (!instance) return 0;
  return instance->getNodeId();
}

unsigned int SLgetInstanceLine(ModuleInstance* instance) {
  if (!instance) return 0;
  return instance->getLineNb();
}

unsigned int SLgetnInstanceChildren(ModuleInstance* instance) {
  if (!instance) return 0;
  return instance->getNbChildren();
}

ModuleInstance* SLgetInstanceChildren(ModuleInstance* instance,
                                      unsigned int i) {
  if (!instance) return NULL;
  return instance->getChildren(i);
}

ModuleInstance* SLgetInstanceParent(ModuleInstance* instance) {
  if (!instance) return NULL;
  return instance->getParent();
}
}  // namespace SURELOG
