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

#ifndef SURELOG_PUBLIC_H
#define SURELOG_PUBLIC_H

// Header file for Surelog library

#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/ErrorContainer.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/Location.h"
#include "ErrorReporting/Waiver.h"
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/VObjectTypes.h"

#ifdef PYTHON_NEEDED
// Python API (optional - needed to be enabled early in the main
//             with PythonAPI::init if needed)
#include "API/PythonAPI.h"
// Limited C-like API
#include "API/SLAPI.h"
#endif

// Full C++ DataModel API
#include "API/Surelog.h"
#include "Common/ClockingBlockHolder.h"
#include "Config/Config.h"
#include "Config/ConfigSet.h"
#include "Design/ClockingBlock.h"
#include "Design/DataType.h"
#include "Design/DefParam.h"
#include "Design/Design.h"
#include "Design/DesignComponent.h"
#include "Design/DesignElement.h"
#include "Design/Enum.h"
#include "Design/FileCNodeId.h"
#include "Design/FileContent.h"
#include "Design/Function.h"
#include "Design/Instance.h"
#include "Design/ModuleDefinition.h"
#include "Design/ModuleInstance.h"
#include "Design/Parameter.h"
#include "Design/Scope.h"
#include "Design/Signal.h"
#include "Design/Statement.h"
#include "Design/Task.h"
#include "Design/TfPortItem.h"
#include "Design/TimeInfo.h"
#include "Design/VObject.h"
#include "Design/ValuedComponentI.h"
#include "DesignCompile/CompileHelper.h"
#include "Expression/ExprBuilder.h"
#include "Expression/Value.h"
#include "Library/Library.h"
#include "Library/LibrarySet.h"
#include "Package/Package.h"
#include "Testbench/ClassDefinition.h"
#include "Testbench/ClassObject.h"
#include "Testbench/Constraint.h"
#include "Testbench/CoverGroupDefinition.h"
#include "Testbench/FunctionMethod.h"
#include "Testbench/Program.h"
#include "Testbench/Property.h"
#include "Testbench/TaskMethod.h"
#include "Testbench/TypeDef.h"
#include "Testbench/Variable.h"

#endif
