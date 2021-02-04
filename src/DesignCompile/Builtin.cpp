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
 * File:   Builtin.cpp
 * Author: alain
 *
 * Created on May 30, 2019, 6:36 PM
 */
#include "SourceCompile/VObjectTypes.h"
#include "Design/VObject.h"
#include "Library/Library.h"
#include "Design/Signal.h"
#include "Design/FileContent.h"
#include "Design/ClockingBlock.h"
#include "SourceCompile/SymbolTable.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/Location.h"
#include "ErrorReporting/Error.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/Compiler.h"
#include "DesignCompile/CompileDesign.h"
#include "Testbench/ClassDefinition.h"
#include "DesignCompile/CompileClass.h"
#include "DesignCompile/Builtin.h"
#include "headers/Serializer.h"
#include "headers/class_defn.h"

#include <string_view>

using namespace SURELOG;

static VObjectType convert(std::string_view type) {
  VObjectType result = VObjectType::slNoType;
  if (type == "int")
    result = VObjectType::slIntegerAtomType_Int;
  else if (type == "generic")
    result = VObjectType::slGenericElementType;
  return result;
}

void Builtin::addBuiltins() {
  static const std::vector<std::vector<std::string>> functionDef = {
      {"builtin", "array", "generic", "find"},
      {"builtin", "array", "int", "find_index"},
      {"builtin", "array", "int", "find_first"},
      {"builtin", "array", "int", "find_first_index"},
      {"builtin", "array", "int", "find_last"},
      {"builtin", "array", "int", "find_last_index"},
      {"builtin", "array", "int", "min"},
      {"builtin", "array", "int", "max"},
      {"builtin", "array", "int", "unique"},
      {"builtin", "array", "int", "unique_index"},
      {"builtin", "array", "void", "reverse"},
      {"builtin", "array", "void", "sort"},
      {"builtin", "array", "void", "rsort"},
      {"builtin", "array", "void", "shuffle"},
      {"builtin", "array", "void", "sum"},
      {"builtin", "array", "void", "product"},
      {"builtin", "array", "void", "and"},
      {"builtin", "array", "void", "or"},
      {"builtin", "array", "void", "xor"},
      {"builtin", "array", "void", "delete"},

      {"builtin", "queue", "int", "size"},
      {"builtin", "queue", "void", "insert", "int", "generic"},
      {"builtin", "queue", "void", "delete", "int"},
      {"builtin", "queue", "generic", "pop_front"},
      {"builtin", "queue", "generic", "pop_back"},
      {"builtin", "queue", "void", "push_front", "generic"},
      {"builtin", "queue", "void", "push_back", "generic"},

      {"builtin", "string", "int", "len"},
      {"builtin", "string", "void", "putc", "int", "int"},
      {"builtin", "string", "int", "getc", "int"},
      {"builtin", "string", "string", "toupper"},
      {"builtin", "string", "string", "tolower"},
      {"builtin", "string", "int", "compare", "string"},
      {"builtin", "string", "int", "icompare", "string"},
      {"builtin", "string", "string", "substr", "int", "int"},
      {"builtin", "string", "int", "atoi"},
      {"builtin", "string", "real", "atoreal"},
      {"builtin", "string", "void", "itoa", "int"},
      {"builtin", "string", "void", "hextoa", "int"},
      {"builtin", "string", "void", "bintoa", "int"},
      {"builtin", "string", "void", "realtoa", "real"},

      {"builtin", "system", "void", "display", "generic"},
      {"builtin", "system", "void", "write", "generic"},
      {"builtin", "system", "void", "strobe", "generic"},
      {"builtin", "system", "void", "monitor", "generic"},
      {"builtin", "system", "void", "monitoron", "generic"},
      {"builtin", "system", "void", "monitoroff", "generic"},
      {"builtin", "system", "void", "displayb", "generic"},
      {"builtin", "system", "void", "writeb", "generic"},
      {"builtin", "system", "void", "strobeb", "generic"},
      {"builtin", "system", "void", "monitorb", "generic"},
      {"builtin", "system", "void", "displayo", "generic"},
      {"builtin", "system", "void", "writeo", "generic"},
      {"builtin", "system", "void", "strobeo", "generic"},
      {"builtin", "system", "void", "monitoro", "generic"},
      {"builtin", "system", "void", "displayh", "generic"},
      {"builtin", "system", "void", "writeh", "generic"},
      {"builtin", "system", "void", "strobeh", "generic"},
      {"builtin", "system", "void", "monitorh", "generic"},
      {"builtin", "system", "void", "fopen", "generic"},
      {"builtin", "system", "void", "fclose", "generic"},
      {"builtin", "system", "void", "frewind", "generic"},
      {"builtin", "system", "void", "fflush", "generic"},
      {"builtin", "system", "void", "fseek", "generic"},
      {"builtin", "system", "void", "ftell", "generic"},
      {"builtin", "system", "void", "fdisplay", "generic"},
      {"builtin", "system", "void", "fwrite", "generic"},
      {"builtin", "system", "void", "swrite", "generic"},
      {"builtin", "system", "void", "fstrobe", "generic"},
      {"builtin", "system", "void", "fmonitor", "generic"},
      {"builtin", "system", "void", "fread", "generic"},
      {"builtin", "system", "void", "fscanf", "generic"},
      {"builtin", "system", "void", "fdisplayb", "generic"},
      {"builtin", "system", "void", "fwriteb", "generic"},
      {"builtin", "system", "void", "swriteb", "generic"},
      {"builtin", "system", "void", "fstrobeb", "generic"},
      {"builtin", "system", "void", "fmonitorb", "generic"},
      {"builtin", "system", "void", "fdisplayo", "generic"},
      {"builtin", "system", "void", "fwriteo", "generic"},
      {"builtin", "system", "void", "swriteo", "generic"},
      {"builtin", "system", "void", "fstrobeo", "generic"},
      {"builtin", "system", "void", "fmonitoro", "generic"},
      {"builtin", "system", "void", "fdisplayh", "generic"},
      {"builtin", "system", "void", "fwriteh", "generic"},
      {"builtin", "system", "void", "swriteh", "generic"},
      {"builtin", "system", "void", "fstrobeh", "generic"},
      {"builtin", "system", "void", "fmonitorh", "generic"},
      {"builtin", "system", "void", "sscanf", "generic"},
      {"builtin", "system", "void", "sdf_annotate", "generic"},
      {"builtin", "system", "void", "sformat", "generic"},
      {"builtin", "system", "void", "cast", "generic"},
      {"builtin", "system", "void", "assertkill", "generic"},
      {"builtin", "system", "void", "assertoff", "generic"},
      {"builtin", "system", "void", "asserton", "generic"},
      {"builtin", "system", "void", "bits", "generic"},
      {"builtin", "system", "void", "bitstoshortreal", "generic"},
      {"builtin", "system", "void", "countones", "generic"},
      {"builtin", "system", "void", "coverage_control", "generic"},
      {"builtin", "system", "void", "coverage_merge", "generic"},
      {"builtin", "system", "void", "coverage_save", "generic"},
      {"builtin", "system", "void", "dimensions", "generic"},
      {"builtin", "system", "void", "error", "generic"},
      {"builtin", "system", "void", "exit", "generic"},
      {"builtin", "system", "void", "fatal", "generic"},
      {"builtin", "system", "void", "fell", "generic"},
      {"builtin", "system", "void", "get_coverage", "generic"},
      {"builtin", "system", "void", "high", "generic"},
      {"builtin", "system", "void", "increment", "generic"},
      {"builtin", "system", "void", "info", "generic"},
      {"builtin", "system", "void", "isunbounded", "generic"},
      {"builtin", "system", "void", "isunknown", "generic"},
      {"builtin", "system", "void", "left", "generic"},
      {"builtin", "system", "void", "load_coverage_db", "generic"},
      {"builtin", "system", "void", "low", "generic"},
      {"builtin", "system", "void", "onehot", "generic"},
      {"builtin", "system", "void", "past", "generic"},
      {"builtin", "system", "void", "readmemb", "generic"},
      {"builtin", "system", "void", "readmemh", "generic"},
      {"builtin", "system", "void", "right", "generic"},
      {"builtin", "system", "void", "root", "generic"},
      {"builtin", "system", "void", "rose", "generic"},
      {"builtin", "system", "void", "sampled", "generic"},
      {"builtin", "system", "void", "set_coverage_db_name", "generic"},
      {"builtin", "system", "void", "shortrealtobits", "generic"},
      {"builtin", "system", "void", "size", "generic"},
      {"builtin", "system", "void", "stable", "generic"},
      {"builtin", "system", "void", "typename", "generic"},
      {"builtin", "system", "void", "typeof", "generic"},
      {"builtin", "system", "void", "unit", "generic"},
      {"builtin", "system", "void", "urandom", "generic"},
      {"builtin", "system", "void", "urandom_range", "generic"},
      {"builtin", "system", "void", "warning", "generic"},
      {"builtin", "system", "void", "writememb", "generic"},
      {"builtin", "system", "void", "writememh", "generic"},
      {"builtin", "system", "void", "value$plusargs", "generic"},

  };

  UHDM::Serializer& s = m_compiler->getSerializer();
  for (const auto& function : functionDef) {
    const std::string& packageName = function[0];
    const std::string& className = function[1];
    const std::string& returnTypeName = function[2];
    const std::string& functionName = function[3];
    Package* package = m_design->getPackage(packageName);
    if (package == NULL) {
      package = new Package(packageName, NULL, NULL, 0);
      UHDM::package* pack = s.MakePackage();
      pack->VpiName(package->getName());
      package->setUhdmInstance(pack);
      m_design->addPackageDefinition(packageName, package);
    }
    const std::string fullClassName = packageName + "::" + className;
    ClassDefinition* classDef = m_design->getClassDefinition(fullClassName);
    if (classDef == NULL) {
      classDef =
          new ClassDefinition(className, NULL, package, NULL, 0, NULL, s.MakeClass_defn());
      m_design->addClassDefinition(fullClassName, classDef);
      package->addClassDefinition(className, classDef);
    }

    DataType* dtype =
        new DataType(NULL, 0, returnTypeName, convert(returnTypeName));
    FunctionMethod* method =
        new FunctionMethod(classDef, NULL, 0, functionName, dtype, false, false,
                           false, false, false, false);
    classDef->insertFunction(method);
  }
}
