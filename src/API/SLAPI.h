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
 * File:   SLAPI.h
 * Author: alain
 *
 * Created on May 13, 2017, 9:46 AM
 */

#ifndef SLAPI_H
#define SLAPI_H

#include <string>
#include <vector>

#include "ParserRuleContext.h"  // Antlr runtime
#include "SourceCompile/VObjectTypes.h"

namespace SURELOG {
typedef uint32_t NodeId;  // as defined in SourceCompile/SymbolTable.h
class ModuleDefinition;
class FileContent;
class SV3_1aPythonListener;
class Design;
class ModuleDefinition;
class Program;
class Package;
class ClassDefinition;
class ModuleInstance;
class DesignComponent;
class ErrorContainer;

typedef std::vector<unsigned int> UIntVector;

/* Error DB API  */
void SLsetWaiver(const char* messageId, const char* fileName = 0,
                 unsigned int line = 0, const char* objectName = 0);

void SLoverrideSeverity(const char* messageId, const char* severity);

void SLregisterNewErrorType(const char* messageId, const char* text,
                            const char* secondLine);

void SLaddError(ErrorContainer* container, const char* messageId,
                const char* fileName, unsigned int line, unsigned int col,
                const char* objectName);

void SLaddErrorContext(SV3_1aPythonListener* prog,
                       antlr4::ParserRuleContext* context,
                       const char* messageId, const char* objectName,
                       bool printColumn = 0);

void SLaddMLErrorContext(SV3_1aPythonListener* prog,
                         antlr4::ParserRuleContext* context1,
                         antlr4::ParserRuleContext* context2,
                         const char* messageId, const char* objectName1,
                         const char* objectName2, bool printColumn = 0);

void SLaddMLError(ErrorContainer* container, const char* messageId,
                  const char* fileName1, unsigned int line1, unsigned int col1,
                  const char* objectName1, const char* fileName2,
                  unsigned int line2, unsigned int col2,
                  const char* objectName2);

/* File Listener API */
std::string SLgetFile(SV3_1aPythonListener* prog,
                      antlr4::ParserRuleContext* context);

int SLgetLine(SV3_1aPythonListener* prog, antlr4::ParserRuleContext* context);

int SLgetColumn(SV3_1aPythonListener* prog, antlr4::ParserRuleContext* context);

std::string SLgetText(SV3_1aPythonListener* prog,
                      antlr4::ParserRuleContext* context);

std::vector<std::string> SLgetTokens(SV3_1aPythonListener* prog,
                                     antlr4::ParserRuleContext* context);

antlr4::ParserRuleContext* SLgetParentContext(
    SV3_1aPythonListener* prog, antlr4::ParserRuleContext* context);

std::vector<antlr4::ParserRuleContext*> SLgetChildrenContext(
    SV3_1aPythonListener* prog, antlr4::ParserRuleContext* context);

/* Parser API */
NodeId SLgetRootNode(FileContent* fC);

std::string SLgetFile(FileContent* fC, NodeId id);

NodeId SLgetChild(FileContent* fC, NodeId index);

NodeId SLgetSibling(FileContent* fC, NodeId index);

NodeId SLgetParent(FileContent* fC, NodeId index);

unsigned int SLgetLine(FileContent* fC, NodeId index);

std::string SLgetName(FileContent* fC, NodeId index);

unsigned int SLgetType(FileContent* fC, NodeId index);

NodeId SLgetChild(FileContent* fC, NodeId parent,
                  unsigned int type);  // Get first child item of type

NodeId SLgetParent(FileContent* fC, NodeId parent,
                   unsigned int type);  // Get first parent item of type

UIntVector SLgetAll(FileContent* fC, NodeId parent,
                    unsigned int type);  // get all child items of type

UIntVector SLgetAll(FileContent* fC, NodeId parent,
                    UIntVector types);  // get all child items of types

NodeId SLcollect(
    FileContent* fC, NodeId parent,
    unsigned int type);  // Recursively search for first item of type

UIntVector SLcollectAll(
    FileContent* fC, NodeId parent, unsigned int type,
    bool first);  // Recursively search for all items of type

UIntVector SLcollectAll(
    FileContent* fC, NodeId parent, UIntVector types,
    bool first);  // Recursively search for all items of types

UIntVector SLcollectAll(FileContent* fC, NodeId parent, UIntVector types,
                        UIntVector stopPoints, bool first);
// Recursively search for all items of types
// and stops at types stopPoints
/* Design API */
unsigned int SLgetnModuleDefinition(Design* design);

unsigned int SLgetnProgramDefinition(Design* design);

unsigned int SLgetnPackageDefinition(Design* design);

unsigned int SLgetnClassDefinition(Design* design);

unsigned int SLgetnTopModuleInstance(Design* design);

ModuleDefinition* SLgetModuleDefinition(Design* design, unsigned int index);

Program* SLgetProgramDefinition(Design* design, unsigned int index);

Package* SLgetPackageDefinition(Design* design, unsigned int index);

ClassDefinition* SLgetClassDefinition(Design* design, unsigned int index);

ModuleInstance* SLgetTopModuleInstance(Design* design, unsigned int index);

std::string SLgetModuleName(ModuleDefinition* module);

std::string SLgetModuleFile(ModuleDefinition* module);

VObjectType SLgetModuleType(ModuleDefinition* module);

unsigned int SLgetModuleLine(ModuleDefinition* module);

FileContent* SLgetModuleFileContent(ModuleDefinition* module);

NodeId SLgetModuleRootNode(ModuleDefinition* module);

std::string SLgetClassName(ClassDefinition* def);

std::string SLgetClassFile(ClassDefinition* def);

VObjectType SLgetClassType(ClassDefinition* def);

unsigned int SLgetClassLine(ClassDefinition* def);

FileContent* SLgetClassFileContent(ClassDefinition* def);

NodeId SLgetClassRootNode(ClassDefinition* def);

std::string SLgetPackageName(Package* def);

std::string SLgetPackageFile(Package* def);

VObjectType SLgetPackageType(Package* def);

unsigned int SLgetPackageLine(Package* def);

FileContent* SLgetPackageFileContent(Package* def);

NodeId SLgetPackageRootNode(Package* def);

std::string SLgetProgramName(Program* def);

std::string SLgetProgramFile(Program* def);

VObjectType SLgetProgramType(Program* def);

unsigned int SLgetProgramLine(Program* def);

FileContent* SLgetProgramFileContent(Program* def);

NodeId SLgetProgramRootNode(Program* def);

VObjectType SLgetInstanceType(ModuleInstance* instance);

VObjectType SLgetInstanceModuleType(ModuleInstance* instance);

std::string SLgetInstanceName(ModuleInstance* instance);

std::string SLgetInstanceFullPathName(ModuleInstance* instance);

std::string SLgetInstanceModuleName(ModuleInstance* instance);

DesignComponent* SLgetInstanceDefinition(ModuleInstance* instance);

std::string SLgetInstanceFileName(ModuleInstance* instance);

FileContent* SLgetInstanceFileContent(ModuleInstance* instance);

NodeId SLgetInstanceNodeId(ModuleInstance* instance);

unsigned int SLgetInstanceLine(ModuleInstance* instance);

unsigned int SLgetnInstanceChildren(ModuleInstance* instance);

ModuleInstance* SLgetInstanceChildren(ModuleInstance* instance, unsigned int i);

ModuleInstance* SLgetInstanceParent(ModuleInstance* instance);

}  // namespace SURELOG

#endif
