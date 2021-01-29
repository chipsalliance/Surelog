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
 * File:   CompileExpression.cpp
 * Author: alain
 *
 * Created on May 14, 2019, 8:03 PM
 */
#include <iostream>
#include <bitset> 
#include "Utils/FileUtils.h"
#include "Utils/StringUtils.h"
#include "Expression/Value.h"
#include "Expression/ExprBuilder.h"
#include "Design/Enum.h"
#include "Design/Function.h"
#include "Testbench/Property.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/Compiler.h"
#include "Design/Design.h"
#include "Testbench/TypeDef.h"
#include "Design/Struct.h"
#include "Design/Union.h"
#include "Design/SimpleType.h"
#include "DesignCompile/CompileHelper.h"
#include "CompileDesign.h"
#include "uhdm.h"
#include "clone_tree.h"
#include "ElaboratorListener.h"
#include "expr.h"
#include "UhdmWriter.h"
#include "Utils/StringUtils.h"
#include "Utils/NumUtils.h"
#include "ErrorReporting/ErrorContainer.h"
#include "DesignCompile/CompileDesign.h"
#include "CommandLine/CommandLineParser.h"

using namespace SURELOG;
using namespace UHDM;

class FScope {
 public:
  FScope() {}
  std::map<std::string, any*> vars;
};

typedef std::vector<FScope*> Scopes;

void EvalStmt(Scopes& scopes, DesignComponent* component, CompileDesign* compileDesign, ValuedComponentI* instance, const any* stmt) {
  UHDM_OBJECT_TYPE stt = stmt->UhdmType();
  switch (stt) {
    case uhdmif_else: {
      break;  
    }
    default:
      break;
  }
}

expr* CompileHelper::EvalFunc(UHDM::function* func, std::vector<any*>* args, bool& invalidValue, DesignComponent* component,
               CompileDesign* compileDesign, ValuedComponentI* instance, const std::string& fileName, int lineNumber, any* pexpr) {
  Scopes scopes;
  FScope* scope = new FScope();
  if ((func == nullptr)) {
    invalidValue = true;
    return nullptr;
  }
  scope->vars.insert(std::make_pair(func->VpiName(), nullptr));
  if (func->Io_decls()) {
    unsigned int index = 0;  
    for (auto io : *func->Io_decls()) {
      if (args && (index < args->size()))
        scope->vars.insert(std::make_pair(io->VpiName(), args->at(index)));
      index++;
    }
  }
  scopes.push_back(scope);
  if (const UHDM::any* the_stmt = func->Stmt()) {
    UHDM_OBJECT_TYPE stt = the_stmt->UhdmType();
    switch (stt) {
      case uhdmbegin: {
        UHDM::begin* st = (UHDM::begin*)the_stmt;
        for (auto stmt : *st->Stmts()) {
          EvalStmt(scopes, component, compileDesign, instance, stmt);
        }
        break;
      }
      default: {
        EvalStmt(scopes, component, compileDesign, instance, the_stmt);
        break;
      }
    }
  }
  return (expr*) (*scope->vars.find(func->VpiName())).second;
}
