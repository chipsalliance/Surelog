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

void CompileHelper::EvalStmt(const std::string funcName, Scopes& scopes, bool& invalidValue, DesignComponent* component, CompileDesign* compileDesign,
              ValuedComponentI* instance, const std::string& fileName, int lineNumber, const any* stmt) {
  UHDM_OBJECT_TYPE stt = stmt->UhdmType();
  switch (stt) {
    case uhdmif_else: {
      if_else* st = (if_else*) stmt;
      expr* cond = (expr*) st->VpiCondition();
      unsigned long long val = get_value(invalidValue, reduceExpr(cond, invalidValue, component, 
                                          compileDesign, scopes.back(), fileName, lineNumber, nullptr));
      if (val) {
        EvalStmt(funcName, scopes, invalidValue, component, compileDesign, scopes.back(), fileName, lineNumber, st->VpiStmt());
      } else {
        EvalStmt(funcName, scopes, invalidValue, component, compileDesign, scopes.back(), fileName, lineNumber, st->VpiElseStmt());
      }                                   
      break;  
    }
    case uhdmif_stmt: {
      if_stmt* st = (if_stmt*) stmt;
      expr* cond = (expr*) st->VpiCondition();
      unsigned long long val = get_value(invalidValue, reduceExpr(cond, invalidValue, component, 
                                          compileDesign, scopes.back(), fileName, lineNumber, nullptr));
      if (val) {
        EvalStmt(funcName, scopes, invalidValue, component, compileDesign, scopes.back(), fileName, lineNumber, st->VpiStmt());
      }                                  
      break;  
    }
    case uhdmbegin: {
      begin* st = (begin*) stmt;
      //FScope* scope = new FScope(component, instance);
      //scopes.push_back(scope);
      if (st->Stmts()) {
        for (auto bst : *st->Stmts()) {
          EvalStmt(funcName, scopes, invalidValue, component, compileDesign, scopes.back(), fileName, lineNumber, bst);
        }
      }
      //delete scopes.back();
      //scopes.pop_back();
      break;
    }
    case uhdmassignment: {
      assignment* st = (assignment*) stmt;
      const std::string lhs = st->Lhs()->VpiName();
      expr* rhs = (expr*) st->Rhs();
      unsigned long long val = get_value(invalidValue, reduceExpr(rhs, invalidValue, component, 
                                          compileDesign, scopes.back(), fileName, lineNumber, nullptr));
      Value* value = m_exprBuilder.getValueFactory().newLValue();
      value->set(val, Value::Type::Integer, 32);
      instance->setValue(lhs,value, m_exprBuilder);
      break;
    }
    case uhdmassign_stmt: {
      assign_stmt* st = (assign_stmt*) stmt;
      const std::string lhs = st->Lhs()->VpiName();
      expr* rhs = (expr*) st->Rhs();
      unsigned long long val = get_value(invalidValue, reduceExpr(rhs, invalidValue, component, 
                                          compileDesign, scopes.back(), fileName, lineNumber, nullptr));
      Value* value = m_exprBuilder.getValueFactory().newLValue();
      value->set(val, Value::Type::Integer, 32);
      instance->setValue(lhs,value, m_exprBuilder);
      break;
    }
    case uhdmfor_stmt: {
      for_stmt* st = (for_stmt*) stmt;
      if (st->VpiForInitStmt()) {
        EvalStmt(funcName, scopes, invalidValue, component, compileDesign, scopes.back(), fileName, lineNumber, st->VpiForInitStmt());
      }
      if (st->VpiForInitStmts()) {
        for(auto s : *st->VpiForInitStmts()) {
          EvalStmt(funcName, scopes, invalidValue, component, compileDesign, scopes.back(), fileName, lineNumber, s);
        }
      }
      while (1) {
        expr* cond = (expr*)st->VpiCondition();
        if (cond) {
          unsigned long long val = get_value(
              invalidValue,
              reduceExpr(cond, invalidValue, component, compileDesign,
                         scopes.back(), fileName, lineNumber, nullptr));
          if (val == 0) {
            break;
          }
        }
        EvalStmt(funcName, scopes, invalidValue, component, compileDesign, scopes.back(), fileName, lineNumber, st->VpiStmt());
        if (st->VpiForIncStmt()) {
          EvalStmt(funcName, scopes, invalidValue, component, compileDesign,
                   scopes.back(), fileName, lineNumber, st->VpiForIncStmt());
        }
        if (st->VpiForIncStmts()) {
          for (auto s : *st->VpiForIncStmts()) {
            EvalStmt(funcName, scopes, invalidValue, component, compileDesign,
                     scopes.back(), fileName, lineNumber, s);
          }
        }
      }
      break;
    }
    case uhdmreturn_stmt: {
      return_stmt* st = (return_stmt*) stmt;
      expr* cond = (expr*)st->VpiCondition();
      if (cond) {
        unsigned long long val =
            get_value(invalidValue,
                      reduceExpr(cond, invalidValue, component, compileDesign,
                                 scopes.back(), fileName, lineNumber, nullptr));
        Value* value = m_exprBuilder.getValueFactory().newLValue();
        value->set(val, Value::Type::Integer, 32);
        instance->setValue(funcName,value, m_exprBuilder);
      }
      break;
    }
    default:
      invalidValue = true;
      break;
  }
}

expr* CompileHelper::EvalFunc(UHDM::function* func, std::vector<any*>* args, bool& invalidValue, DesignComponent* component,
               CompileDesign* compileDesign, ValuedComponentI* instance, const std::string& fileName, int lineNumber, any* pexpr) {
  if ((func == nullptr)) {
    invalidValue = true;
    return nullptr;
  }
  Serializer& s = compileDesign->getSerializer();
  const std::string name = func->VpiName();
  // set internal scope stack
  Scopes scopes;
  FScope* scope = new FScope(component, instance);
  // default return value is invalid
  Value* defaultV = m_exprBuilder.fromString("INT:0");
  defaultV->setInvalid();
  scope->setValue(name,defaultV, m_exprBuilder);
  // set args 
  if (func->Io_decls()) {
    unsigned int index = 0;  
    for (auto io : *func->Io_decls()) {
      if (args && (index < args->size())) {
        const std::string ioname = io->VpiName();
        expr* ioexp = (expr*) args->at(index);
        unsigned long long val = get_value(invalidValue, reduceExpr(ioexp, invalidValue, component, 
                                          compileDesign, instance, fileName, lineNumber, pexpr));
        Value* argval = m_exprBuilder.getValueFactory().newLValue();
        argval->set(val, Value::Type::Integer, 32);
        scope->setValue(ioname,argval, m_exprBuilder);
      }
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
          EvalStmt(name, scopes, invalidValue, component, compileDesign, scope, fileName, lineNumber, stmt);
        }
        break;
      }
      default: {
        EvalStmt(name, scopes, invalidValue, component, compileDesign, scope, fileName, lineNumber, the_stmt);
        break;
      }
    }
  }
  // return value
  Value* result = scope->getValue(name);
  if (result && result->isValid()) {
    constant* c = s.MakeConstant();
    c->VpiValue(result->uhdmValue());
    invalidValue = false;
    return c;
  } else {
    return nullptr;
  }
}
