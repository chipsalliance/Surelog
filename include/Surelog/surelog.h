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

#ifndef SURELOG_PUBLIC_SURELOG_H
#define SURELOG_PUBLIC_SURELOG_H
#pragma once

// Header file for Surelog library

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/ErrorReporting/Waiver.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"

#ifdef PYTHON_NEEDED
// Python API (optional - needed to be enabled early in the main
//             with PythonAPI::init if needed)
#include "Surelog/API/PythonAPI.h"
// Limited C-like API
#include "Surelog/API/SLAPI.h"
#endif

// Full C++ DataModel API
#include "Surelog/API/Surelog.h"
#include "Surelog/Common/ClockingBlockHolder.h"
#include "Surelog/Config/Config.h"
#include "Surelog/Config/ConfigSet.h"
#include "Surelog/Design/ClockingBlock.h"
#include "Surelog/Design/DataType.h"
#include "Surelog/Design/DefParam.h"
#include "Surelog/Design/Design.h"
#include "Surelog/Design/DesignComponent.h"
#include "Surelog/Design/DesignElement.h"
#include "Surelog/Design/Enum.h"
#include "Surelog/Design/FileCNodeId.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/Function.h"
#include "Surelog/Design/Instance.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/Design/Scope.h"
#include "Surelog/Design/Signal.h"
#include "Surelog/Design/Statement.h"
#include "Surelog/Design/Task.h"
#include "Surelog/Design/TfPortItem.h"
#include "Surelog/Design/TimeInfo.h"
#include "Surelog/Design/VObject.h"
#include "Surelog/Design/ValuedComponentI.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/Expression/ExprBuilder.h"
#include "Surelog/Expression/Value.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Library/LibrarySet.h"
#include "Surelog/Package/Package.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Testbench/ClassObject.h"
#include "Surelog/Testbench/Constraint.h"
#include "Surelog/Testbench/CoverGroupDefinition.h"
#include "Surelog/Testbench/FunctionMethod.h"
#include "Surelog/Testbench/Program.h"
#include "Surelog/Testbench/Property.h"
#include "Surelog/Testbench/TaskMethod.h"
#include "Surelog/Testbench/TypeDef.h"
#include "Surelog/Testbench/Variable.h"

#endif  // SURELOG_PUBLIC_SURELOG_H
