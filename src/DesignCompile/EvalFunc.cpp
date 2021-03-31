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
#include "Design/Parameter.h"
#include "Design/ParamAssign.h"

using namespace SURELOG;
using namespace UHDM;

void CompileHelper::EvalStmt(const std::string funcName, Scopes& scopes, bool& invalidValue, bool& continue_flag, bool& break_flag, 
                             DesignComponent* component, CompileDesign* compileDesign,
              ValuedComponentI* instance, const std::string& fileName, int lineNumber, const any* stmt) {
  if (invalidValue) {
    return;
  }
  UHDM_OBJECT_TYPE stt = stmt->UhdmType();
  switch (stt) {
    case uhdmif_else: {
      if_else* st = (if_else*) stmt;
      expr* cond = (expr*) st->VpiCondition();
      int64_t val = get_value(invalidValue, reduceExpr(cond, invalidValue, component, 
                                          compileDesign, scopes.back(), fileName, lineNumber, nullptr));
      if (val > 0) {
        EvalStmt(funcName, scopes, invalidValue, continue_flag, break_flag, component, compileDesign, scopes.back(), fileName, lineNumber, st->VpiStmt());
      } else {
        EvalStmt(funcName, scopes, invalidValue, continue_flag, break_flag, component, compileDesign, scopes.back(), fileName, lineNumber, st->VpiElseStmt());
      }                                   
      break;  
    }
    case uhdmif_stmt: {
      if_stmt* st = (if_stmt*) stmt;
      expr* cond = (expr*) st->VpiCondition();
      int64_t val = get_value(invalidValue, reduceExpr(cond, invalidValue, component, 
                                          compileDesign, scopes.back(), fileName, lineNumber, nullptr));
      if (val > 0) {
        EvalStmt(funcName, scopes, invalidValue, continue_flag, break_flag, component, compileDesign, scopes.back(), fileName, lineNumber, st->VpiStmt());
      }                                  
      break;  
    }
    case uhdmbegin: {
      begin* st = (begin*) stmt;
      if (st->Stmts()) {
        for (auto bst : *st->Stmts()) {
          EvalStmt(funcName, scopes, invalidValue, continue_flag, break_flag, component, compileDesign, scopes.back(), fileName, lineNumber, bst);
          if (continue_flag) {
            return;
          }
          if (break_flag) {
            return;
          }
        }
      }
      break;
    }
    case uhdmnamed_begin: {
      named_begin* st = (named_begin*) stmt;
      if (st->Stmts()) {
        for (auto bst : *st->Stmts()) {
          EvalStmt(funcName, scopes, invalidValue, continue_flag, break_flag, component, compileDesign, scopes.back(), fileName, lineNumber, bst);
          if (continue_flag) {
            return;
          }
          if (break_flag) {
            return;
          }
        }
      }
      break;
    }
    case uhdmassignment: {
      assignment* st = (assignment*) stmt;
      const std::string lhs = st->Lhs()->VpiName();
      expr* rhs = (expr*) st->Rhs();
      expr* rhsexp = reduceExpr(rhs, invalidValue, component, 
                                          compileDesign, scopes.back(), fileName, lineNumber, nullptr);

      bool invalidValueI = false;
      bool invalidValueD = false;
      int64_t valI = get_value(invalidValueI, rhsexp);
      long double valD = 0;
      if (invalidValueI) {
        valD = get_double(invalidValueD, rhsexp);
      }
      if (invalidValueI && invalidValueD) {
        instance->setComplexValue(lhs, rhsexp);
      } else if (invalidValueI) {
        Value* value = m_exprBuilder.getValueFactory().newLValue();
        value->set((double) valD);
        instance->setValue(lhs, value, m_exprBuilder);
      } else {
        Value* value = m_exprBuilder.getValueFactory().newLValue();
        value->set(valI, Value::Type::Integer, 32);
        instance->setValue(lhs, value, m_exprBuilder);
      }
      if (invalidValueI && invalidValueD)
        invalidValue = true;
      break;
    }
    case uhdmassign_stmt: {
      assign_stmt* st = (assign_stmt*) stmt;
      const std::string lhs = st->Lhs()->VpiName();
      expr* rhs = (expr*) st->Rhs();
      expr* rhsexp = reduceExpr(rhs, invalidValue, component, 
                                          compileDesign, scopes.back(), fileName, lineNumber, nullptr);
      bool invalidValueI = false;
      bool invalidValueD = false;
      int64_t valI = get_value(invalidValueI, rhsexp);
      long double valD = 0;
      if (invalidValueI) {
        valD = get_double(invalidValueD, rhsexp);
      }
      if (invalidValueI && invalidValueD) {
        instance->setComplexValue(lhs, rhsexp);
      } else if (invalidValueI) {
        Value* value = m_exprBuilder.getValueFactory().newLValue();
        value->set((double) valD);
        instance->setValue(lhs, value, m_exprBuilder);
      } else {
        Value* value = m_exprBuilder.getValueFactory().newLValue();
        value->set(valI, Value::Type::Integer, 32);
        instance->setValue(lhs, value, m_exprBuilder);
      }
      if (invalidValueI && invalidValueD)
        invalidValue = true;
      break;
    }
    case uhdmfor_stmt: {
      for_stmt* st = (for_stmt*) stmt;
      if (st->VpiForInitStmt()) {
        EvalStmt(funcName, scopes, invalidValue, continue_flag, break_flag, component, compileDesign, scopes.back(), fileName, lineNumber, st->VpiForInitStmt());
      }
      if (st->VpiForInitStmts()) {
        for(auto s : *st->VpiForInitStmts()) {
          EvalStmt(funcName, scopes, invalidValue, continue_flag, break_flag, component, compileDesign, scopes.back(), fileName, lineNumber, s);
        }
      }
      while (1) {
        expr* cond = (expr*)st->VpiCondition();
        if (cond) {
          int64_t val = get_value(
              invalidValue,
              reduceExpr(cond, invalidValue, component, compileDesign,
                         scopes.back(), fileName, lineNumber, nullptr));
          if (val == 0) {
            break;
          }
          if (invalidValue)
            break;
        }
        EvalStmt(funcName, scopes, invalidValue, continue_flag, break_flag, component, compileDesign, scopes.back(), fileName, lineNumber, st->VpiStmt());
        if (invalidValue)
          break;
        if (continue_flag) {
          continue_flag = false;
          continue;
        }
        if (break_flag) {
          break_flag = false;
          break;
        }
        if (st->VpiForIncStmt()) {
          EvalStmt(funcName, scopes, invalidValue, continue_flag, break_flag, component, compileDesign,
                   scopes.back(), fileName, lineNumber, st->VpiForIncStmt());
        }
        if (invalidValue)
          break;
        if (st->VpiForIncStmts()) {
          for (auto s : *st->VpiForIncStmts()) {
            EvalStmt(funcName, scopes, invalidValue, continue_flag, break_flag, component, compileDesign,
                     scopes.back(), fileName, lineNumber, s);
          }
        }
        if (invalidValue)
          break;
      }
      break;
    }
    case uhdmreturn_stmt: {
      return_stmt* st = (return_stmt*) stmt;
      expr* cond = (expr*)st->VpiCondition();
      if (cond) {
        expr* rhsexp = reduceExpr(cond, invalidValue, component, compileDesign,
                                  scopes.back(), fileName, lineNumber, nullptr);
        bool invalidValueI = false;
        bool invalidValueD = false;
        int64_t valI = get_value(invalidValueI, rhsexp);
        long double valD = 0;
        if (invalidValueI) {
          valD = get_double(invalidValueD, rhsexp);
        }
        if (invalidValueI && invalidValueD) {
          instance->setComplexValue(funcName, rhsexp);
        } else if (invalidValueI) {
          Value* value = m_exprBuilder.getValueFactory().newLValue();
          value->set((double)valD);
          instance->setValue(funcName, value, m_exprBuilder);
        } else {
          Value* value = m_exprBuilder.getValueFactory().newLValue();
          value->set(valI, Value::Type::Integer, 32);
          instance->setValue(funcName, value, m_exprBuilder);
        }
        if (invalidValueI && invalidValueD) invalidValue = true;
      }
      break;
    }
    case uhdmwhile_stmt: {
      while_stmt* st = (while_stmt*) stmt;
      expr* cond = (expr*)st->VpiCondition();
      if (cond) {
        while (1) {
          int64_t val = get_value(
              invalidValue,
              reduceExpr(cond, invalidValue, component, compileDesign,
                         scopes.back(), fileName, lineNumber, nullptr));
          if (invalidValue) 
            break;
          if (val == 0) {
            break;
          }
          EvalStmt(funcName, scopes, invalidValue, continue_flag, break_flag, component, compileDesign, scopes.back(), fileName, lineNumber, st->VpiStmt());
          if (invalidValue) 
            break;
          if (continue_flag) {
            continue_flag = false;
            continue;
          }
          if (break_flag) {
            break_flag = false;
            break;
          }  
        }
      }
      break;
    }
    case uhdmdo_while: {
      do_while* st = (do_while*) stmt;
      expr* cond = (expr*)st->VpiCondition();
      if (cond) {
        while (1) {
          EvalStmt(funcName, scopes, invalidValue, continue_flag, break_flag, component, compileDesign, scopes.back(), fileName, lineNumber, st->VpiStmt());
          if (invalidValue) 
            break;
          if (continue_flag) {
            continue_flag = false;
            continue;
          }
          if (break_flag) {
            break_flag = false;
            break;
          }
          int64_t val = get_value(
              invalidValue,
              reduceExpr(cond, invalidValue, component, compileDesign,
                         scopes.back(), fileName, lineNumber, nullptr));
         if (invalidValue) 
            break;               
          if (val == 0) {
            break;
          }
        }
      }
      break;
    }
    case uhdmcontinue_stmt: {
      continue_flag = true;
      break;
    }
    case uhdmbreak_stmt: {
      break_flag = true;
      break;
    }
    case uhdmoperation: {
      operation* op = (operation*)stmt;
      // ++, -- ops
      reduceExpr(op, invalidValue, component, compileDesign, scopes.back(),
                 fileName, lineNumber, nullptr);
      break;
    }
    default: {
      invalidValue = true;
      ErrorContainer* errors =
          compileDesign->getCompiler()->getErrorContainer();
      SymbolTable* symbols = compileDesign->getCompiler()->getSymbolTable();
      std::string fileContent = FileUtils::getFileContent(stmt->VpiFile());
      std::string lineText =
          StringUtils::getLineInString(fileContent, stmt->VpiLineNo());
      Location loc(
          symbols->registerSymbol(fileName),
          lineNumber, stmt->VpiColumnNo(),
          symbols->registerSymbol(lineText));
      Error err(ErrorDefinition::UHDM_UNSUPPORTED_STMT, loc);
      errors->addError(err);
      break;
    }
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
  FScope* scope = new FScope((instance) ? instance : component, component);
  // default return value is invalid
  Value* defaultV = m_exprBuilder.fromVpiValue("INT:0");
  defaultV->setInvalid();
  scope->setValue(name,defaultV, m_exprBuilder);
  // set args 
  if (func->Io_decls()) {
    unsigned int index = 0;  
    for (auto io : *func->Io_decls()) {
      if (args && (index < args->size())) {
        const std::string ioname = io->VpiName();
        expr* ioexp = (expr*) args->at(index);
        expr* exparg = reduceExpr(ioexp, invalidValue, component, 
                                          compileDesign, instance, fileName, lineNumber, pexpr);
        bool invalidValueI = false;
        bool invalidValueD = false;
        int64_t valI = get_value(invalidValueI, exparg);
        long double valD = 0;
        if (invalidValueI) {
          valD = get_double(invalidValueD, exparg);
        }
        if (invalidValueI && invalidValueD) {
          scope->setComplexValue(ioname, ioexp);
        } else if (invalidValueI) {
          Value* argval = m_exprBuilder.getValueFactory().newLValue();
          argval->set((double) valD);
          scope->setValue(ioname,argval, m_exprBuilder);
        } else {
          Value* argval = m_exprBuilder.getValueFactory().newLValue();
          argval->set(valI, Value::Type::Integer, 32);
          scope->setValue(ioname,argval, m_exprBuilder);
        }
      }
      index++;
    }
  } else {
    return nullptr;
  }
  scopes.push_back(scope);
  if (const UHDM::any* the_stmt = func->Stmt()) {
    UHDM_OBJECT_TYPE stt = the_stmt->UhdmType();
    switch (stt) {
      case uhdmbegin: {
        UHDM::begin* st = (UHDM::begin*)the_stmt;
        bool continue_flag = false;
        bool break_flag = false;
        for (auto stmt : *st->Stmts()) {
          EvalStmt(name, scopes, invalidValue, continue_flag, break_flag, component, compileDesign, scope, fileName, lineNumber, stmt);
          if (continue_flag || break_flag) {
            ErrorContainer* errors =
                compileDesign->getCompiler()->getErrorContainer();
            SymbolTable* symbols =
                compileDesign->getCompiler()->getSymbolTable();
            std::string fileContent =
                FileUtils::getFileContent(stmt->VpiFile());
            std::string lineText = StringUtils::getLineInString(
                fileContent, stmt->VpiLineNo());
            Location loc(symbols->registerSymbol(the_stmt->VpiFile()), stmt->VpiLineNo(), stmt->VpiColumnNo(),
                         symbols->registerSymbol(lineText));
            Error err(ErrorDefinition::UHDM_UNSUPPORTED_STMT, loc);
            errors->addError(err);
          }
        }
        break;
      }
      case uhdmnamed_begin: {
        UHDM::named_begin* st = (UHDM::named_begin*)the_stmt;
        bool continue_flag = false;
        bool break_flag = false;
        for (auto stmt : *st->Stmts()) {
          EvalStmt(name, scopes, invalidValue, continue_flag, break_flag, component, compileDesign, scope, fileName, lineNumber, stmt);
          if (continue_flag || break_flag) {
            ErrorContainer* errors =
                compileDesign->getCompiler()->getErrorContainer();
            SymbolTable* symbols =
                compileDesign->getCompiler()->getSymbolTable();
            std::string fileContent =
                FileUtils::getFileContent(stmt->VpiFile());
            std::string lineText = StringUtils::getLineInString(
                fileContent, stmt->VpiLineNo());
            Location loc(symbols->registerSymbol(stmt->VpiFile()), stmt->VpiLineNo(), stmt->VpiColumnNo(),
                         symbols->registerSymbol(lineText));
            Error err(ErrorDefinition::UHDM_UNSUPPORTED_STMT, loc);
            errors->addError(err);
          }
        }
        break;
      }
      default: {
        bool continue_flag = false;
        bool break_flag = false;
        EvalStmt(name, scopes, invalidValue, continue_flag, break_flag, component, compileDesign, scope, fileName, lineNumber, the_stmt);
        if (continue_flag || break_flag) {
          ErrorContainer* errors =
              compileDesign->getCompiler()->getErrorContainer();
          SymbolTable* symbols = compileDesign->getCompiler()->getSymbolTable();
          std::string fileContent = FileUtils::getFileContent(the_stmt->VpiFile());
          std::string lineText =
              StringUtils::getLineInString(fileContent, the_stmt->VpiLineNo());
          Location loc(symbols->registerSymbol(the_stmt->VpiFile()), the_stmt->VpiLineNo(), the_stmt->VpiColumnNo(),
                       symbols->registerSymbol(lineText));
          Error err(ErrorDefinition::UHDM_UNSUPPORTED_STMT, loc);
          errors->addError(err);
        }
        break;
      }
    }
  }
  // return value
  Value* result = scope->getValue(name);
  if (result && result->isValid()) {
    constant* c = s.MakeConstant();
    c->VpiValue(result->uhdmValue());
    c->VpiDecompile(result->decompiledValue());
    c->VpiConstType(result->vpiValType());
    c->VpiSize(result->getSize());
    invalidValue = false;
    return c;
  } else {
    return nullptr;
  }
}

void CompileHelper::evalScheduledExprs(DesignComponent* component,
                                       CompileDesign* compileDesign) {
  for (auto& nameEval : component->getScheduledParamExprEval()) {
    const std::string& name = nameEval.first;
    ExprEval& expr_eval = nameEval.second;
    bool invalidValue = false;
    expr* result =
        reduceExpr(expr_eval.m_expr, invalidValue, component, compileDesign,
                   expr_eval.m_instance, expr_eval.m_fileName,
                   expr_eval.m_lineNumber, expr_eval.m_pexpr);
    if (result && result->UhdmType() == uhdmconstant) {
      UHDM::constant* c = (UHDM::constant*)result;
      Value* val = m_exprBuilder.fromVpiValue(c->VpiValue());
      component->setValue(name, val, m_exprBuilder);
      for (ParamAssign* pass : component->getParamAssignVec()) {
        if (param_assign* upass = pass->getUhdmParamAssign()) {
          if (upass->Lhs()->VpiName() == name) {
            upass->Rhs(result);
            break;
          }
        }
      }
    }
  }
}
