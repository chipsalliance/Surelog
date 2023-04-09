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

#ifndef SURELOG_SLAPI_H
#define SURELOG_SLAPI_H
#pragma once

#include <Surelog/Common/NodeId.h>
#include <Surelog/SourceCompile/VObjectTypes.h>

#include <string>
#include <vector>

namespace antlr4 {
class ParserRuleContext;
}

namespace SURELOG {

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

typedef std::vector<uint32_t> UIntVector;

/* Error DB API  */
void SLsetWaiver(const char* messageId, const char* fileName = 0,
                 uint32_t line = 0, const char* objectName = 0);

void SLoverrideSeverity(const char* messageId, const char* severity);

void SLregisterNewErrorType(const char* messageId, const char* text,
                            const char* secondLine);

void SLaddError(ErrorContainer* container, const char* messageId,
                const char* fileName, uint32_t line, uint32_t col,
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
                  const char* fileName1, uint32_t line1, uint32_t col1,
                  const char* objectName1, const char* fileName2,
                  uint32_t line2, uint32_t col2,
                  const char* objectName2);

/* File Listener API */
std::string SLgetFile(SV3_1aPythonListener* prog,
                      antlr4::ParserRuleContext* context);

int32_t SLgetLine(SV3_1aPythonListener* prog, antlr4::ParserRuleContext* context);

int32_t SLgetColumn(SV3_1aPythonListener* prog, antlr4::ParserRuleContext* context);

std::string SLgetText(SV3_1aPythonListener* prog,
                      antlr4::ParserRuleContext* context);

std::vector<std::string> SLgetTokens(SV3_1aPythonListener* prog,
                                     antlr4::ParserRuleContext* context);

antlr4::ParserRuleContext* SLgetParentContext(
    SV3_1aPythonListener* prog, antlr4::ParserRuleContext* context);

std::vector<antlr4::ParserRuleContext*> SLgetChildrenContext(
    SV3_1aPythonListener* prog, antlr4::ParserRuleContext* context);

/* Parser API */
RawNodeId SLgetRootNode(FileContent* fC);

std::string SLgetFile(FileContent* fC, RawNodeId id);

RawNodeId SLgetChild(FileContent* fC, RawNodeId index);

RawNodeId SLgetSibling(FileContent* fC, RawNodeId index);

RawNodeId SLgetParent(FileContent* fC, RawNodeId index);

uint32_t SLgetLine(FileContent* fC, RawNodeId index);

std::string SLgetName(FileContent* fC, RawNodeId index);

uint32_t SLgetType(FileContent* fC, RawNodeId index);

RawNodeId SLgetChild(FileContent* fC, RawNodeId parent,
                  uint32_t type);  // Get first child item of type

RawNodeId SLgetParent(FileContent* fC, RawNodeId parent,
                   uint32_t type);  // Get first parent item of type

UIntVector SLgetAll(FileContent* fC, RawNodeId parent,
                    uint32_t type);  // get all child items of type

UIntVector SLgetAll(FileContent* fC, RawNodeId parent,
                    const UIntVector& types);  // get all child items of types

RawNodeId SLcollect(
    FileContent* fC, RawNodeId parent,
    uint32_t type);  // Recursively search for first item of type

UIntVector SLcollectAll(
    FileContent* fC, RawNodeId parent, uint32_t type,
    bool first);  // Recursively search for all items of type

UIntVector SLcollectAll(
    FileContent* fC, RawNodeId parent, const UIntVector& types,
    bool first);  // Recursively search for all items of types

UIntVector SLcollectAll(FileContent* fC, RawNodeId parent,
                        const UIntVector& types,
                        const UIntVector& stopPoints, bool first);
// Recursively search for all items of types
// and stops at types stopPoints
/* Design API */
uint32_t SLgetnModuleDefinition(Design* design);

uint32_t SLgetnProgramDefinition(Design* design);

uint32_t SLgetnPackageDefinition(Design* design);

uint32_t SLgetnClassDefinition(Design* design);

uint32_t SLgetnTopModuleInstance(Design* design);

ModuleDefinition* SLgetModuleDefinition(Design* design, uint32_t index);

Program* SLgetProgramDefinition(Design* design, uint32_t index);

Package* SLgetPackageDefinition(Design* design, uint32_t index);

ClassDefinition* SLgetClassDefinition(Design* design, uint32_t index);

ModuleInstance* SLgetTopModuleInstance(Design* design, uint32_t index);

std::string SLgetModuleName(ModuleDefinition* module);

std::string SLgetModuleFile(ModuleDefinition* module);

VObjectType SLgetModuleType(ModuleDefinition* module);

uint32_t SLgetModuleLine(ModuleDefinition* module);

FileContent* SLgetModuleFileContent(ModuleDefinition* module);

RawNodeId SLgetModuleRootNode(ModuleDefinition* module);

std::string SLgetClassName(ClassDefinition* def);

std::string SLgetClassFile(ClassDefinition* def);

VObjectType SLgetClassType(ClassDefinition* def);

uint32_t SLgetClassLine(ClassDefinition* def);

FileContent* SLgetClassFileContent(ClassDefinition* def);

RawNodeId SLgetClassRootNode(ClassDefinition* def);

std::string SLgetPackageName(Package* def);

std::string SLgetPackageFile(Package* def);

VObjectType SLgetPackageType(Package* def);

uint32_t SLgetPackageLine(Package* def);

FileContent* SLgetPackageFileContent(Package* def);

RawNodeId SLgetPackageRootNode(Package* def);

std::string SLgetProgramName(Program* def);

std::string SLgetProgramFile(Program* def);

VObjectType SLgetProgramType(Program* def);

uint32_t SLgetProgramLine(Program* def);

FileContent* SLgetProgramFileContent(Program* def);

RawNodeId SLgetProgramRootNode(Program* def);

VObjectType SLgetInstanceType(ModuleInstance* instance);

VObjectType SLgetInstanceModuleType(ModuleInstance* instance);

std::string SLgetInstanceName(ModuleInstance* instance);

std::string SLgetInstanceFullPathName(ModuleInstance* instance);

std::string SLgetInstanceModuleName(ModuleInstance* instance);

DesignComponent* SLgetInstanceDefinition(ModuleInstance* instance);

std::string SLgetInstanceFileName(ModuleInstance* instance);

FileContent* SLgetInstanceFileContent(ModuleInstance* instance);

RawNodeId SLgetInstanceNodeId(ModuleInstance* instance);

uint32_t SLgetInstanceLine(ModuleInstance* instance);

uint32_t SLgetnInstanceChildren(ModuleInstance* instance);

ModuleInstance* SLgetInstanceChildren(ModuleInstance* instance, uint32_t i);

ModuleInstance* SLgetInstanceParent(ModuleInstance* instance);

}  // namespace SURELOG

#endif  // SURELOG_SLAPI_H
