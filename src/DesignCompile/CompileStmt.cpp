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
 * File:   CompileStmt.cpp
 * Author: alain
 *
 * Created on May 14, 2019, 8:03 PM
 */
#include <iostream>
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
#include "Testbench/ClassDefinition.h"
#include "DesignCompile/CompileHelper.h"
#include "CompileDesign.h"
#include "uhdm.h"
#include "expr.h"
#include "UhdmWriter.h"
#include "ErrorReporting/ErrorContainer.h"
#include "ElaboratorListener.h"

using namespace SURELOG;
using namespace UHDM;

VectorOfany* CompileHelper::compileStmt(
  DesignComponent* component,
  const FileContent* fC, NodeId the_stmt,
  CompileDesign* compileDesign, UHDM::any* pstmt, ValuedComponentI* instance) {
  VectorOfany* results = nullptr;
  UHDM::Serializer& s = compileDesign->getSerializer();
  VObjectType type = fC->Type(the_stmt);
  UHDM::VectorOfattribute* attributes = nullptr;
  if (type == VObjectType::slAttribute_instance) {
    attributes = compileAttributes(component, fC, the_stmt, compileDesign);
    while (fC->Type(the_stmt) == slAttribute_instance)
      the_stmt = fC->Sibling(the_stmt);
  }
  type = fC->Type(the_stmt);
  UHDM::any* stmt = nullptr;
  switch (type) {
  case VObjectType::slStatement_or_null: {
    NodeId child =  fC->Child(the_stmt);
    if (child == 0) {
      // That is the null statement (no statement)
      return nullptr;
    }
    results = compileStmt(component, fC, child, compileDesign, pstmt, instance);
    break;
  }
  case VObjectType::slBlock_item_declaration:
  case VObjectType::slTf_item_declaration:
  case VObjectType::slStatement:
  case VObjectType::slJump_statement:
  case VObjectType::slStatement_item:
  case VObjectType::slImmediate_assertion_statement:
  case VObjectType::slProcedural_assertion_statement:
  case VObjectType::slLoop_statement: {
	  results = compileStmt(component, fC, fC->Child(the_stmt), compileDesign, pstmt, instance);
    break;
  }
  case VObjectType::slInc_or_dec_expression: {
    stmt = compileExpression(component, fC, the_stmt, compileDesign, pstmt, instance, false);
    break;
  }
  case VObjectType::slProcedural_timing_control_statement: {
    UHDM::atomic_stmt* dc = compileProceduralTimingControlStmt(component, fC, fC->Child(the_stmt), compileDesign, pstmt, instance);
    stmt = dc;
    break;
  }
  case VObjectType::slNonblocking_assignment: {
    NodeId Operator_assignment  = the_stmt;
    UHDM::assignment* assign = compileBlockingAssignment(component, fC,
                Operator_assignment, false, compileDesign, pstmt, instance);
    stmt = assign;
    break;
  }
  case VObjectType::slBlocking_assignment: 
  case VObjectType::slOperator_assignment: {
    NodeId Operator_assignment = fC->Child(the_stmt);
    UHDM::assignment* assign = compileBlockingAssignment(component, fC,
                Operator_assignment, true, compileDesign, pstmt, instance);
    stmt = assign;
    break;
  }
  case VObjectType::slSubroutine_call_statement: {
	  NodeId Subroutine_call = fC->Child(the_stmt);
    stmt = compileTfCall(component, fC, Subroutine_call ,compileDesign);
  	break;
  }
  case VObjectType::slSystem_task: {
    stmt = compileTfCall(component, fC, the_stmt, compileDesign);
    break;
  }
  case VObjectType::slConditional_statement: {
	  NodeId Conditional_statement = the_stmt;
    NodeId Cond_predicate = fC->Child(Conditional_statement);
	  UHDM::atomic_stmt* cstmt = compileConditionalStmt(component, fC,
                                   Cond_predicate, compileDesign, pstmt, instance);
  	stmt = cstmt;
  	break;
  }
  case VObjectType::slCond_predicate: {
    NodeId Cond_predicate = the_stmt;
	  UHDM::atomic_stmt* cstmt = compileConditionalStmt(component, fC,
                                   Cond_predicate, compileDesign, pstmt, instance);
  	stmt = cstmt;
  	break;
  }
  case VObjectType::slCase_statement: {
    NodeId Case_statement = the_stmt;
	  UHDM::atomic_stmt* cstmt = compileCaseStmt(component, fC,
                                   Case_statement, compileDesign, pstmt, instance);
  	stmt = cstmt;
    break;
  }
  case VObjectType::slSeq_block: {
	  NodeId item = fC->Child(the_stmt);
	  VectorOfany* stmts = s.MakeAnyVec();
    if (fC->Type(item) == VObjectType::slStringConst) {
      UHDM::named_begin* begin = s.MakeNamed_begin();
      begin->Stmts(stmts);
      begin->VpiParent(pstmt);
      stmt = begin;
      begin->VpiName(fC->SymName(item));
      item = fC->Sibling(item);
    } else {
      UHDM::begin* begin = s.MakeBegin();
      begin->Stmts(stmts);
      begin->VpiParent(pstmt);
      stmt = begin;
    }
	  while (item) {
      if (item && (fC->Type(item) == VObjectType::slEnd)) {
        break;
      }
	    VectorOfany* cstmts = compileStmt(component, fC, item, compileDesign, stmt, instance);
	    if (cstmts) {
        for (any* cstmt : *cstmts) {
	        stmts->push_back(cstmt);
          cstmt->VpiParent(stmt);
        }
      }
	    item = fC->Sibling(item);
  	}
	  break;
  }
  case VObjectType::slPar_block: {
	  NodeId item = fC->Child(the_stmt);
	  VectorOfany* stmts = s.MakeAnyVec();
    if (fC->Type(item) == VObjectType::slStringConst) {
      UHDM::named_fork* fork = s.MakeNamed_fork();
      fork->Stmts(stmts);
      fork->VpiParent(pstmt);
      stmt = fork;
      fork->VpiName(fC->SymName(item));
      item = fC->Sibling(item);
    } else {
      UHDM::fork_stmt* fork = s.MakeFork_stmt();
      fork->Stmts(stmts);
      fork->VpiParent(pstmt);
      stmt = fork;
    }
	  while (item) {
      VectorOfany* cstmts = compileStmt(component, fC, item, compileDesign, stmt, instance);
	    if (cstmts) {
        for (any* cstmt : *cstmts) {
	        stmts->push_back(cstmt);
          cstmt->VpiParent(stmt);
        }
      }
	    item = fC->Sibling(item);
      if (item) {
        VObjectType jointype = fC->Type(item);
        int vpijointype = 0;
        if (jointype == VObjectType::slJoin_keyword) {
          vpijointype = vpiJoin;
          if (stmt->UhdmType() == uhdmnamed_fork) {
            ((UHDM::named_fork*)stmt)->VpiJoinType(vpijointype);
          } else {
            ((UHDM::fork_stmt*)stmt)->VpiJoinType(vpijointype);
          }
          break;
        } else if (jointype == VObjectType::slJoin_any_keyword) {
          vpijointype = vpiJoinAny;
          if (stmt->UhdmType() == uhdmnamed_fork) {
            ((UHDM::named_fork*)stmt)->VpiJoinType(vpijointype);
          } else {
            ((UHDM::fork_stmt*)stmt)->VpiJoinType(vpijointype);
          }
          break;
        } else if (jointype == VObjectType::slJoin_none_keyword) {
          vpijointype = vpiJoinNone;
          if (stmt->UhdmType() == uhdmnamed_fork) {
            ((UHDM::named_fork*)stmt)->VpiJoinType(vpijointype);
          } else {
            ((UHDM::fork_stmt*)stmt)->VpiJoinType(vpijointype);
          }
          break;
        }
      }
  	}
	  break;
  }
  case VObjectType::slForever: {
    UHDM::forever_stmt* forever = s.MakeForever_stmt();
    NodeId item = fC->Sibling(the_stmt);
    VectorOfany* forev = compileStmt(component, fC, item, compileDesign, forever, instance);
    if (forev) {
      any* stmt = (*forev)[0];
      stmt->VpiParent(forever);
      forever->VpiStmt(stmt);
    }
    stmt = forever;
    break;
  }
  case VObjectType::slForeach: {
    UHDM::foreach_stmt* foreach = s.MakeForeach_stmt();
    NodeId Ps_or_hierarchical_array_identifier = fC->Sibling(the_stmt);
    UHDM::any* var = compileVariable(component, fC, fC->Child(Ps_or_hierarchical_array_identifier), compileDesign, foreach, nullptr, true, false);
    NodeId Loop_variables = fC->Sibling(Ps_or_hierarchical_array_identifier);
    UHDM::any* loop_var = compileVariable(component, fC, fC->Child(Loop_variables), compileDesign, foreach, nullptr, true, false);
    NodeId Statement = fC->Sibling(Loop_variables);
    VectorOfany* forev = compileStmt(component, fC, Statement, compileDesign, foreach, instance);
    if (forev) {
      any* stmt = (*forev)[0];
      stmt->VpiParent(foreach);
      foreach->VpiStmt(stmt);
    }
    if (var)
      var->VpiParent(foreach);
    if (loop_var)
      loop_var->VpiParent(foreach);
    foreach->Variable((variables*) var);
    VectorOfany* loop_vars = s.MakeAnyVec();
    loop_vars->push_back(loop_var);
    foreach->VpiLoopVars(loop_vars);
    stmt = foreach;
    break;
  }
  case VObjectType::slProcedural_continuous_assignment: {
    any* conta = compileProceduralContinuousAssign(component, fC, the_stmt, compileDesign);
    stmt = conta;
    break;
  }
  case VObjectType::slParameter_declaration:
  case VObjectType::slLocal_parameter_declaration: {
    NodeId Data_type_or_implicit = fC->Child(the_stmt);
    UHDM::typespec* ts =
        compileTypespec(component, fC, fC->Child(Data_type_or_implicit),
                        compileDesign, nullptr, nullptr, true);
    NodeId List_of_param_assignments = fC->Sibling(Data_type_or_implicit);
    NodeId Param_assignment = fC->Child(List_of_param_assignments);
    UHDM::VectorOfany* param_assigns = s.MakeAnyVec();
    while (Param_assignment) {
      NodeId name = fC->Child(Param_assignment);
      NodeId value = fC->Sibling(name);
      expr* unpacked = nullptr;
      UHDM::parameter* param = s.MakeParameter();
      param->VpiFile(fC->getFileName());
      param->VpiLineNo(fC->Line(Param_assignment));
      param->VpiColumnNo(fC->Column(Param_assignment));
      // Unpacked dimensions
      if (fC->Type(value) == VObjectType::slUnpacked_dimension) {
        int unpackedSize;
        std::vector<UHDM::range*>* unpackedDimensions =
            compileRanges(component, fC, value, compileDesign, param, nullptr,
                          true, unpackedSize, false);
        param->Ranges(unpackedDimensions);
        param->VpiSize(unpackedSize);
        while (fC->Type(value) == VObjectType::slUnpacked_dimension) {
          value = fC->Sibling(value);
        }
      }    
      param->VpiLocalParam(true);
      UHDM::param_assign* param_assign = s.MakeParam_assign();
      param_assign->VpiFile(fC->getFileName());
      param_assign->VpiLineNo(fC->Line(Param_assignment));
      param_assign->VpiColumnNo(fC->Column(Param_assignment));
      param_assigns->push_back(param_assign);
      param->VpiName(fC->SymName(name));
      param->Typespec(ts);
      param->Expr(unpacked);
      param_assign->Lhs(param);
      param_assign->Rhs((expr*)compileExpression(
          component, fC, value, compileDesign, nullptr, nullptr, true));
      Param_assignment = fC->Sibling(Param_assignment);
    }
    results = param_assigns;
    break;
  }
  case VObjectType::slRepeat: {
    NodeId cond = fC->Sibling(the_stmt);
    UHDM::any* cond_exp = compileExpression(component, fC, cond, compileDesign);
    NodeId rstmt = fC->Sibling(cond);
    UHDM::repeat* repeat = s.MakeRepeat();
    repeat->VpiCondition((UHDM::expr*) cond_exp);
    if (cond_exp)
      cond_exp->VpiParent(repeat);
    VectorOfany* repeat_stmts = compileStmt(component, fC, rstmt, compileDesign, repeat, instance);
    if (repeat_stmts) {
      any* stmt = (*repeat_stmts)[0];
      repeat->VpiStmt(stmt);
      stmt->VpiParent(repeat);
    }
    stmt = repeat;
    break;
  }
  case VObjectType::slWhile: {
    NodeId cond = fC->Sibling(the_stmt);
    UHDM::any* cond_exp = compileExpression(component, fC, cond, compileDesign);
    NodeId rstmt = fC->Sibling(cond);
    UHDM::while_stmt* while_st = s.MakeWhile_stmt();
    while_st->VpiCondition((UHDM::expr*) cond_exp);
    if (cond_exp)
      cond_exp->VpiParent(while_st);
    VectorOfany* while_stmts = compileStmt(component, fC, rstmt, compileDesign, while_st, instance);
    if (while_stmts) {
      any* stmt = (*while_stmts)[0];
      while_st->VpiStmt(stmt);
      stmt->VpiParent(while_st);
    }
    stmt = while_st;
    break;
  }
  case VObjectType::slDo: {
    NodeId Statement_or_null = fC->Sibling(the_stmt);
    NodeId Condition = fC->Sibling(Statement_or_null);
    NodeId Statement = fC->Child(Statement_or_null);
    UHDM::do_while* do_while = s.MakeDo_while();
    if (Statement) {
      VectorOfany* while_stmts = compileStmt(component, fC, Statement, compileDesign, do_while, instance);
      if (while_stmts && while_stmts->size()) {
        any* stmt = (*while_stmts)[0];
        do_while->VpiStmt(stmt);
        stmt->VpiParent(do_while);
      }
    }
    UHDM::any* cond_exp = compileExpression(component, fC, Condition, compileDesign);
    do_while->VpiCondition((UHDM::expr*) cond_exp);
    if (cond_exp)
      cond_exp->VpiParent(do_while);
    stmt = do_while;
    break;
  }
  case VObjectType::slWait_statement: {
    NodeId Expression = fC->Child(the_stmt);
    if (Expression == 0) {
      // wait fork
      UHDM::wait_fork* waitst = s.MakeWait_fork();
      stmt = waitst;
    } else if (fC->Type(Expression) == slExpression) {
      // wait
      NodeId Statement_or_null = fC->Sibling(Expression);
      UHDM::wait_stmt* waitst = s.MakeWait_stmt();
      NodeId Statement = fC->Child(Statement_or_null);
      if (Statement) {
        VectorOfany* while_stmts =
            compileStmt(component, fC, Statement, compileDesign, waitst, instance);
        if (while_stmts && while_stmts->size()) {
          any* stmt = (*while_stmts)[0];
          waitst->VpiStmt(stmt);
          stmt->VpiParent(waitst);
        }
      }
      UHDM::any* cond_exp =
          compileExpression(component, fC, Expression, compileDesign);
      waitst->VpiCondition((UHDM::expr*)cond_exp);
      if (cond_exp) cond_exp->VpiParent(waitst);
      stmt = waitst;
    } else {
      // wait order
      UHDM::ordered_wait* waitst = s.MakeOrdered_wait();
      stmt = waitst;
      VectorOfany* conditions = s.MakeAnyVec();
      waitst->VpiConditions(conditions);
      NodeId Hierarchical_identifier = Expression;
      while (Hierarchical_identifier && (fC->Type(Hierarchical_identifier) == slHierarchical_identifier)) {
        UHDM::any* cond_exp =
          compileExpression(component, fC, Hierarchical_identifier, compileDesign);
        conditions->push_back(cond_exp);
        Hierarchical_identifier = fC->Sibling(Hierarchical_identifier);
      }
      NodeId Action_block = Hierarchical_identifier;
      NodeId Stmt = fC->Child(Action_block);
      if (fC->Type(Stmt) == slStatement_or_null) {
        // If only
        VectorOfany* if_stmts =
            compileStmt(component, fC, Stmt, compileDesign, waitst, instance);
        if (if_stmts && if_stmts->size()) {
          any* stmt = (*if_stmts)[0];
          waitst->VpiStmt(stmt);
          stmt->VpiParent(waitst);
        }
      } else if (fC->Type(Stmt) == slElse) {
        // Else Only
        Stmt = fC->Sibling(Stmt);
        VectorOfany* if_stmts =
            compileStmt(component, fC, Stmt, compileDesign, waitst, instance);
        if (if_stmts && if_stmts->size()) {
          any* stmt = (*if_stmts)[0];
          waitst->VpiElseStmt(stmt);
          stmt->VpiParent(waitst);
        }
      } else {
        // if else
        VectorOfany* if_stmts =
            compileStmt(component, fC, Stmt, compileDesign, waitst, instance);
        if (if_stmts && if_stmts->size()) {
          any* stmt = (*if_stmts)[0];
          waitst->VpiStmt(stmt);
          stmt->VpiParent(waitst);
        }
        NodeId Else = fC->Sibling(Stmt);
        Stmt = fC->Sibling(Else);
        VectorOfany* else_stmts =
            compileStmt(component, fC, Stmt, compileDesign, waitst, instance);
        if (else_stmts && else_stmts->size()) {
          any* stmt = (*else_stmts)[0];
          waitst->VpiElseStmt(stmt);
          stmt->VpiParent(waitst);
        }
      }
    }
    break;
  }
  case VObjectType::slEvent_trigger: {
    UHDM::event_stmt* estmt = s.MakeEvent_stmt();
    NodeId Trigger_type = fC->Child(the_stmt);
    if (fC->Type(Trigger_type) != slNonBlockingTriggerEvent) {
      estmt->VpiBlocking(true);
    }
    stmt = estmt;
    NodeId Hierarchical_identifier = fC->Sibling(Trigger_type);
    expr* exp = (expr*) compileExpression(component, fC, Hierarchical_identifier, compileDesign);
    estmt->VpiName(exp->VpiName());
    break;
  }
  case VObjectType::slFor: {
    UHDM::any* loop = compileForLoop(component, fC, the_stmt, compileDesign);
    stmt = loop;
    break;
  }
  case VObjectType::slReturnStmt: {
    UHDM::return_stmt* return_stmt = s.MakeReturn_stmt();
    NodeId cond = fC->Sibling(the_stmt);
    if (cond) {
      expr* exp = (expr*) compileExpression(component, fC, cond, compileDesign);
      if (exp)
        exp->VpiParent(return_stmt);
      return_stmt->VpiCondition(exp);
    }
    stmt = return_stmt;
    break;
  }
  case VObjectType::slBreakStmt: {
    UHDM::break_stmt* bstmt = s.MakeBreak_stmt();
    stmt = bstmt;
    break;
  }
  case VObjectType::slDisable_statement: {
    // TODO: flavors
    UHDM::disable* disable = s.MakeDisable();
    stmt = disable;
  }
  case VObjectType::slContinueStmt: {
    UHDM::continue_stmt* cstmt = s.MakeContinue_stmt();
    stmt = cstmt;
    break;
  }
  case VObjectType::slSimple_immediate_assertion_statement: {
    stmt = compileSimpleImmediateAssertion(component, fC, fC->Child(the_stmt), compileDesign, pstmt, nullptr);
    break;
  }
  case VObjectType::slDeferred_immediate_assertion_statement: {
    stmt = compileDeferredImmediateAssertion(component, fC, fC->Child(the_stmt), compileDesign, pstmt, nullptr);
    break;
  }
  case VObjectType::slConcurrent_assertion_statement: {
    stmt = compileConcurrentAssertion(component, fC, fC->Child(the_stmt), compileDesign, pstmt, nullptr);
    break;
  }
  case VObjectType::slData_declaration: {
    results = compileDataDeclaration(component, fC, fC->Child(the_stmt), compileDesign, pstmt);
    break;
  }
  case VObjectType::slStringConst: {
    const std::string& label = fC->SymName(the_stmt);
    VectorOfany* stmts = compileStmt(component, fC, fC->Sibling(the_stmt), compileDesign, pstmt, instance);
    if (stmts) {
      for(any* st : *stmts) {
        if (UHDM::atomic_stmt* stm = dynamic_cast<atomic_stmt*> (st))
          stm->VpiName(label);
        else if (UHDM::concurrent_assertions* stm = dynamic_cast<concurrent_assertions*> (st))
          stm->VpiName(label);
      }
    }
    results = stmts;
    break;
  }
  default:
    break;
  }
  if (stmt) {
    if (attributes) {
      // Only attach attributes to following stmt
      if (UHDM::atomic_stmt* stm = dynamic_cast<atomic_stmt*> (stmt))
        stm->Attributes(attributes);
    }
    stmt->VpiFile(fC->getFileName(the_stmt));
    stmt->VpiLineNo(fC->Line(the_stmt));
    stmt->VpiColumnNo(fC->Column(the_stmt));
    stmt->VpiParent(pstmt);
    results = s.MakeAnyVec();
    results->push_back(stmt);
  } else if (results) {
    if (attributes) {
      for (any* st : *results) {
        if (UHDM::atomic_stmt* stm = dynamic_cast<atomic_stmt*>(st))
          stm->Attributes(attributes);
      }
    }
  } else {
    VObjectType stmttype = fC->Type(the_stmt);
    if ((stmttype != VObjectType::slEnd) &&
        (stmttype != VObjectType::slJoin_keyword) &&
        (stmttype != VObjectType::slJoin_any_keyword) &&
        (stmttype != VObjectType::slJoin_none_keyword)) {
      ErrorContainer* errors =
          compileDesign->getCompiler()->getErrorContainer();
      SymbolTable* symbols = compileDesign->getCompiler()->getSymbolTable();
      unsupported_stmt* ustmt = s.MakeUnsupported_stmt();
      std::string fileContent = FileUtils::getFileContent(fC->getFileName());
      std::string lineText =
          StringUtils::getLineInString(fileContent, fC->Line(the_stmt));
      Location loc(
          symbols->registerSymbol(fC->getFileName(the_stmt)),
          fC->Line(the_stmt), 0,
          symbols->registerSymbol(std::string("<") + fC->printObject(the_stmt) +
                                  std::string("> ") + lineText));
      Error err(ErrorDefinition::UHDM_UNSUPPORTED_STMT, loc);
      errors->addError(err);
      ustmt->VpiValue("STRING:" + lineText);
      ustmt->VpiFile(fC->getFileName(the_stmt));
      ustmt->VpiLineNo(fC->Line(the_stmt));
      ustmt->VpiColumnNo(fC->Column(the_stmt));
      ustmt->VpiParent(pstmt);
      stmt = ustmt;
      // std::cout << "UNSUPPORTED STATEMENT: " << fC->getFileName(the_stmt)
      // << ":" << fC->Line(the_stmt) << ":" << std::endl; std::cout << " -> "
      // << fC->printObject(the_stmt) << std::endl;
    }
  }
  return results;
}

VectorOfany* CompileHelper::compileDataDeclaration(DesignComponent* component,
                                                   const FileContent* fC,
                                                   NodeId nodeId,
                                                   CompileDesign* compileDesign,
                                                   UHDM::any* pstmt) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  VectorOfany* results = nullptr;
  VObjectType type = fC->Type(nodeId);
  bool automatic_status = false;
  bool const_status = false;
  if (type == slLifetime_Automatic) {
    nodeId = fC->Sibling(nodeId);
    automatic_status = true;
    type = fC->Type(nodeId);
  }
  if (type == slLifetime_Static) {
    nodeId = fC->Sibling(nodeId);
    automatic_status = false;
    type = fC->Type(nodeId);
  }
  if (type == slConst_type) {
    nodeId = fC->Sibling(nodeId);
    const_status = true;
    type = fC->Type(nodeId);
  }
  switch (type) {
    case VObjectType::slVariable_declaration: {
      NodeId Data_type = fC->Child(nodeId);
      //typespec* ts = compileTypespec(component, fC, Data_type, compileDesign);
      NodeId List_of_variable_decl_assignments = fC->Sibling(Data_type);
      if (fC->Type(List_of_variable_decl_assignments) ==
          VObjectType::slPacked_dimension) {
        List_of_variable_decl_assignments =
            fC->Sibling(List_of_variable_decl_assignments);
      }
      NodeId Variable_decl_assignment =
          fC->Child(List_of_variable_decl_assignments);
      while (Variable_decl_assignment) {
        NodeId Var = fC->Child(Variable_decl_assignment);
        NodeId tmp = fC->Sibling(Var);
        std::vector<UHDM::range*>* unpackedDimensions = nullptr;
        if (fC->Type(tmp) != slExpression) {
          int unpackedSize;
          unpackedDimensions = compileRanges(component, fC, tmp, compileDesign,
                                   nullptr, nullptr, false, unpackedSize, false);
        }
        while (tmp && (fC->Type(tmp) != slExpression)) {
          tmp = fC->Sibling(tmp);
        }
        NodeId Expression = tmp;

        variables* var = (variables*)compileVariable(
            component, fC, Data_type, compileDesign, pstmt, nullptr, false, false);

        if (var) {
          var->VpiConstantVariable(const_status);
          var->VpiAutomatic(automatic_status);
          var->VpiName(fC->SymName(Var));

          if (unpackedDimensions) {
            array_var* arr = s.MakeArray_var();
            arr->Ranges(unpackedDimensions);
            VectorOfvariables* vars = s.MakeVariablesVec();
            arr->Variables(vars);
            vars->push_back(var);
            var = arr;
          }
        }

        if (results == nullptr) {
          results = s.MakeAnyVec();
        }
        assign_stmt* assign_stmt = s.MakeAssign_stmt();
        if (var) {
          var->VpiParent(assign_stmt);
        }
        assign_stmt->Lhs(var);
        results->push_back(assign_stmt);
        if (Expression) {
          expr* rhs =
            (expr*)compileExpression(component, fC, Expression, compileDesign);
          if (rhs)
            rhs->VpiParent(assign_stmt);
          assign_stmt->Rhs(rhs);
        }

        Variable_decl_assignment = fC->Sibling(Variable_decl_assignment);
      }
      break;
    }
    case VObjectType::slType_declaration: {
      if (pstmt) {
        // Keep type declaration local to the current stmt
        component = nullptr;
      }
      /* const DataType* dt = */ compileTypeDef(component, fC, fC->Parent(nodeId), compileDesign, pstmt);
      if (results == nullptr) {
        results = s.MakeAnyVec();
        // Return an empty list of statements.
        // Type declaration are not executable statements.
      }
      break;
    }
    default:
      break;
  }
  return results;
}

UHDM::atomic_stmt* CompileHelper::compileConditionalStmt(
  DesignComponent* component, const FileContent* fC,
  NodeId Cond_predicate,
  CompileDesign* compileDesign, UHDM::any* pstmt, ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  int qualifier = 0;
  if (fC->Type(Cond_predicate) == slUnique_priority) {
    NodeId Qualifier = fC->Child(Cond_predicate);
    if (fC->Type(Qualifier) == slUnique) {
      qualifier = vpiUniqueQualifier;
    } else if (fC->Type(Qualifier) == slPriority) {
      qualifier = vpiPriorityQualifier;
    } else if (fC->Type(Qualifier) == slUnique0) {
      qualifier = vpiUniqueQualifier;
    }
    Cond_predicate = fC->Sibling(Cond_predicate);
  }
  UHDM::any* cond_exp = compileExpression(component, fC, Cond_predicate, compileDesign, pstmt, instance);
  NodeId If_branch_stmt = fC->Sibling(Cond_predicate);
  NodeId Else_branch_stmt = fC->Sibling(If_branch_stmt);
  UHDM::atomic_stmt* result_stmt = nullptr;
  if (Else_branch_stmt != 0) {
    UHDM::if_else* cond_stmt = s.MakeIf_else();
    cond_stmt->VpiQualifier(qualifier);
    cond_stmt->VpiCondition((UHDM::expr*) cond_exp);
    if (cond_exp)
      cond_exp->VpiParent(cond_stmt);
    VectorOfany* if_stmts = compileStmt(component, fC, If_branch_stmt, compileDesign, cond_stmt, instance);
    UHDM::any* if_stmt  = nullptr;
    if (if_stmts)
      if_stmt = (*if_stmts)[0];
    cond_stmt->VpiStmt(if_stmt);
    if (if_stmt)
      if_stmt->VpiParent(cond_stmt);
    VectorOfany* else_stmts = compileStmt(component, fC, Else_branch_stmt, compileDesign, cond_stmt, instance);
    UHDM::any* else_stmt = nullptr;
    if (else_stmts)
      else_stmt = (*else_stmts)[0];
    cond_stmt->VpiElseStmt(else_stmt);
    if (else_stmt)
      else_stmt->VpiParent(cond_stmt);
    result_stmt = cond_stmt;
  } else {
    UHDM::if_stmt* cond_stmt = s.MakeIf_stmt();
    cond_stmt->VpiQualifier(qualifier);
    cond_stmt->VpiCondition((UHDM::expr*) cond_exp);
    if (cond_exp)
      cond_exp->VpiParent(cond_stmt);
    VectorOfany* if_stmts = compileStmt(component, fC, If_branch_stmt, compileDesign, cond_stmt, instance);
    UHDM::any* if_stmt  = nullptr;
    if (if_stmts)
      if_stmt = (*if_stmts)[0];
    cond_stmt->VpiStmt(if_stmt);
    if (if_stmt)
      if_stmt->VpiParent(cond_stmt);
    result_stmt = cond_stmt;
  }
  return result_stmt;
}


UHDM::atomic_stmt* CompileHelper::compileEventControlStmt(
  DesignComponent* component, const FileContent* fC,
  NodeId Procedural_timing_control,
  CompileDesign* compileDesign, UHDM::any* pstmt, ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  /*
  n<#100> u<70> t<IntConst> p<71> l<7>
  n<> u<71> t<Delay_control> p<72> c<70> l<7>
  n<> u<72> t<Procedural_timing_control> p<88> c<71> s<87> l<7>
  */
  NodeId Event_control = fC->Child(Procedural_timing_control);

  NodeId Event_expression = fC->Child(Event_control);
  UHDM::event_control* event = s.MakeEvent_control();
  if (Event_expression) {
    UHDM::any* exp = compileExpression(component, fC, Event_expression, compileDesign);
    event->VpiCondition(exp);
    if (exp)
      exp->VpiParent(event);
  } // else @(*) : no event expression
  NodeId Statement_or_null = fC->Sibling(Procedural_timing_control);
  VectorOfany* stmts = compileStmt(component, fC, Statement_or_null, compileDesign, event, instance);
  if (stmts) {
    any* stmt = (*stmts)[0];
    event->Stmt(stmt);
    stmt->VpiParent(event);
  }
  return event;
}

UHDM::atomic_stmt* CompileHelper::compileCaseStmt(
  DesignComponent* component, const FileContent* fC, NodeId nodeId,
  CompileDesign* compileDesign, UHDM::any* pstmt, ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::atomic_stmt* result = nullptr;
  NodeId Case_keyword = fC->Child(nodeId);
  NodeId Unique = 0;
  if (fC->Type(Case_keyword) == VObjectType::slUnique_priority) {
    Unique = fC->Child(Case_keyword);
    Case_keyword = fC->Sibling(Case_keyword);
  }
  NodeId Case_type = fC->Child(Case_keyword);
  NodeId Condition  = fC->Sibling(Case_keyword);
  UHDM::any* cond_exp = compileExpression(component, fC, Condition, compileDesign, pstmt, instance);
  NodeId Case_item = fC->Sibling(Condition);
  UHDM::case_stmt* case_stmt = s.MakeCase_stmt();
  UHDM::VectorOfcase_item* case_items = s.MakeCase_itemVec();
  case_stmt->Case_items(case_items);
  result = case_stmt;
  case_stmt->VpiCondition((UHDM::expr*) cond_exp);
  setParentNoOverride(cond_exp, case_stmt);
  VObjectType CaseType = fC->Type(Case_type);
  switch (CaseType) {
    case VObjectType::slCase_inside_item:
    case VObjectType::slCase:
      case_stmt->VpiCaseType(vpiCaseExact);
      break;
    case VObjectType::slCaseX:
      case_stmt->VpiCaseType(vpiCaseX);
      break;
    case VObjectType::slCaseZ:
      case_stmt->VpiCaseType(vpiCaseZ);
      break;
    default:
      break;
  }
  if (Unique) {
    VObjectType UniqueType = fC->Type(Unique);
    switch (UniqueType) {
    case VObjectType::slUnique:
      case_stmt->VpiQualifier(vpiUniqueQualifier);
      break;
    case VObjectType::slUnique0:
      case_stmt->VpiQualifier(vpiNoQualifier);
      break;
    case VObjectType::slPriority:
      case_stmt->VpiQualifier(vpiPriorityQualifier);
      break;
    default:
      break;
    }
  }
  while (Case_item) {
    UHDM::case_item* case_item = nullptr;
    if (fC->Type(Case_item) == VObjectType::slCase_item ||
        fC->Type(Case_item) == VObjectType::slCase_inside_item) {
      case_item = s.MakeCase_item();
      case_items->push_back(case_item);
      case_item->VpiFile(fC->getFileName());
      case_item->VpiLineNo(fC->Line(Case_item));
      case_item->VpiColumnNo(fC->Column(Case_item));
      case_item->VpiParent(case_stmt);
    }
    bool isDefault = false;
    NodeId Expression = 0;
    if (fC->Type(Case_item) == VObjectType::slCase_item) {
      Expression = fC->Child(Case_item);
      if (fC->Type(Expression) == VObjectType::slExpression) {
        VectorOfany* exprs = s.MakeAnyVec();
        case_item->VpiExprs(exprs);
        while (Expression) {
          if (fC->Type(Expression) == VObjectType::slExpression) {
            // Expr
            UHDM::any* item_exp = compileExpression(component, fC, Expression, compileDesign, pstmt, instance);
            setParentNoOverride(item_exp, case_item);
            if (item_exp) {
              exprs->push_back(item_exp);
            } else {
             // std::cout << "HERE\n";
            }
          } else {
            // Stmt
            VectorOfany* stmts = compileStmt(component, fC, Expression, compileDesign, case_item, instance);
            if (stmts) {
              any* stmt = (*stmts)[0];
              stmt->VpiParent(case_item);
              case_item->Stmt(stmt);
            }
          }
          Expression = fC->Sibling(Expression);
        }
      } else {
        isDefault = true;
      }
    } else if (fC->Type(Case_item) == VObjectType::slCase_inside_item) {
      NodeId Open_range_list = fC->Child(Case_item);
      if (fC->Type(Open_range_list) == VObjectType::slStatement_or_null) {
         isDefault = true;
      } else {
        NodeId Value_range = fC->Child(Open_range_list);
        VectorOfany* exprs = s.MakeAnyVec();
        case_item->VpiExprs(exprs);
        while (Value_range) {
          UHDM::expr* item_exp = (expr*)compileExpression(
              component, fC, Value_range, compileDesign);
          setParentNoOverride(item_exp, case_item);
          if (item_exp) {
            exprs->push_back(item_exp);
          }
          Value_range = fC->Sibling(Value_range);
        }
        NodeId Statement_or_null = fC->Sibling(Open_range_list);
        // Stmt
        VectorOfany* stmts = compileStmt(component, fC, Statement_or_null, compileDesign,
                                case_item, instance);
        if (stmts) {
          any* stmt = (*stmts)[0];
          stmt->VpiParent(case_item);
          case_item->Stmt(stmt);
        }
      }
    }

    if (isDefault) {
      // Default
      if (Expression) {
        VectorOfany* stmts = compileStmt(component, fC, Expression, compileDesign, case_item, instance);
        if (stmts) {
          any* stmt = (*stmts)[0];
          if (stmt)
            stmt->VpiParent(case_item);
          case_item->Stmt(stmt);
        }
      }
    }

    Case_item = fC->Sibling(Case_item);
  }

  return result;
}


std::pair<std::vector<UHDM::io_decl*>*, std::vector<UHDM::variables*>*> CompileHelper::compileTfPortDecl(
  DesignComponent* component, UHDM::task_func* parent,
  const FileContent* fC, NodeId tf_item_decl,
  CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<io_decl*>* ios = s.MakeIo_declVec();
  std::vector<variables*>* vars = s.MakeVariablesVec();
  std::pair<std::vector<UHDM::io_decl*>*, std::vector<UHDM::variables*>*> results = std::make_pair(ios, vars);
  /*
n<> u<137> t<TfPortDir_Inp> p<141> s<138> l<28>
n<> u<138> t<Data_type_or_implicit> p<141> s<140> l<28>
n<req_1> u<139> t<StringConst> p<140> l<28>
n<> u<140> t<List_of_tf_variable_identifiers> p<141> c<139> l<28>
n<> u<141> t<Tf_port_declaration> p<142> c<137> l<28>
n<> u<142> t<Tf_item_declaration> p<386> c<141> s<384> l<28>
  */
  std::map<std::string, io_decl*> ioMap;

  while  (tf_item_decl) {
    if (fC->Type(tf_item_decl) == VObjectType::slTf_item_declaration) {
      NodeId Tf_port_declaration = fC->Child(tf_item_decl);
      if (fC->Type(Tf_port_declaration) == slTf_port_declaration) {
        NodeId TfPortDir = fC->Child(Tf_port_declaration);
        VObjectType tf_port_direction_type = fC->Type(TfPortDir);
        NodeId Data_type_or_implicit = fC->Sibling(TfPortDir);
        NodeId Packed_dimension = fC->Child(Data_type_or_implicit);
        int size;
        VectorOfrange* ranges =
            compileRanges(component, fC, Packed_dimension, compileDesign,
                          nullptr, nullptr, true, size, false);

        NodeId List_of_tf_variable_identifiers =
            fC->Sibling(Data_type_or_implicit);
        while (List_of_tf_variable_identifiers) {
          NodeId nameId = fC->Child(List_of_tf_variable_identifiers);
          const std::string& name = fC->SymName(nameId);
          io_decl* decl = s.MakeIo_decl();
          ios->push_back(decl);
          decl->VpiParent(parent);
          decl->VpiDirection(
              UhdmWriter::getVpiDirection(tf_port_direction_type));
          decl->VpiName(name);
          ioMap.insert(std::make_pair(name, decl));
          decl->VpiFile(fC->getFileName());
          decl->VpiLineNo(fC->Line(nameId));
          decl->VpiColumnNo(fC->Column(nameId));
          decl->Ranges(ranges);
          List_of_tf_variable_identifiers =
              fC->Sibling(List_of_tf_variable_identifiers);
        }
      } else if (fC->Type(Tf_port_declaration) == slBlock_item_declaration) {
        NodeId Data_declaration = fC->Child(Tf_port_declaration);
        if (fC->Type(Data_declaration) == slData_declaration) {
          NodeId Variable_declaration = fC->Child(Data_declaration);
          NodeId Data_type = fC->Child(Variable_declaration);
          UHDM::typespec* ts = compileTypespec(
              component, fC, Data_type, compileDesign, parent, nullptr, true);
          NodeId List_of_variable_decl_assignments = fC->Sibling(Data_type);
          NodeId Variable_decl_assignment =
              fC->Child(List_of_variable_decl_assignments);
          while (Variable_decl_assignment) {
            NodeId nameId = fC->Child(Variable_decl_assignment);
            const std::string& name = fC->SymName(nameId);
            std::map<std::string, io_decl*>::iterator itr = ioMap.find(name);
            if (itr == ioMap.end()) {
              variables* var = (variables*)compileVariable(
                  component, fC, Data_type, compileDesign,
                  nullptr, nullptr, true, false);
              if (var) {    
                var->VpiName(name);
                vars->push_back(var);
                var->Typespec(ts);
              }
            } else {
              (*itr).second->Typespec(ts);
            }
            Variable_decl_assignment = fC->Sibling(Variable_decl_assignment);
          }
        }
      }
    }
    tf_item_decl = fC->Sibling(tf_item_decl);
  }
  return results;
}

std::vector<io_decl*>* CompileHelper::compileTfPortList(
  DesignComponent* component, UHDM::task_func* parent,
  const FileContent* fC, NodeId tf_port_list,
  CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<io_decl*>* ios = s.MakeIo_declVec();
  /*
   n<c1> u<7> t<StringConst> p<29> s<27> l<10>
   n<> u<8> t<IntegerAtomType_Int> p<9> l<12>
   n<> u<9> t<Data_type> p<10> c<8> l<12>
   n<> u<10> t<Function_data_type> p<11> c<9> l<12>
   n<> u<11> t<Function_data_type_or_implicit> p<24> c<10> s<12> l<12>
   n<try_get> u<12> t<StringConst> p<24> s<22> l<12>
   n<> u<13> t<IntegerAtomType_Int> p<14> l<12>
   n<> u<14> t<Data_type> p<15> c<13> l<12>
   n<> u<15> t<Data_type_or_implicit> p<21> c<14> s<16> l<12>
   n<keyCount> u<16> t<StringConst> p<21> s<20> l<12>
   n<1> u<17> t<IntConst> p<18> l<12>
   n<> u<18> t<Primary_literal> p<19> c<17> l<12>
   n<> u<19> t<Primary> p<20> c<18> l<12>
   n<> u<20> t<Expression> p<21> c<19> l<12>
   n<> u<21> t<Tf_port_item> p<22> c<15> l<12>
   n<> u<22> t<Tf_port_list> p<24> c<21> s<23> l<12>
   n<> u<23> t<Endfunction> p<24> l<13>
   n<> u<24> t<Function_body_declaration> p<25> c<11> l<12>
   n<> u<25> t<Function_declaration> p<26> c<24> l<12>
   n<> u<26> t<Class_method> p<27> c<25> l<12>
  */
  /*
   Or
   n<get> u<47> t<StringConst> p<55> s<53> l<18>
   n<> u<48> t<PortDir_Ref> p<49> l<18>
   n<> u<49> t<Tf_port_direction> p<52> c<48> s<50> l<18>
   n<> u<50> t<Data_type_or_implicit> p<52> s<51> l<18>
   n<message> u<51> t<StringConst> p<52> l<18>
   n<> u<52> t<Tf_port_item> p<53> c<49> l<18>
  */
  // Compile arguments
  if (tf_port_list && (fC->Type(tf_port_list) == VObjectType::slTf_port_list)) {
    NodeId tf_port_item = fC->Child(tf_port_list);
    int previousDirection = vpiInput;
    UHDM::typespec* ts = nullptr;
    while (tf_port_item) {
      io_decl* decl = s.MakeIo_decl();
      ios->push_back(decl);
      NodeId tf_data_type_or_implicit = fC->Child(tf_port_item);
      NodeId tf_data_type = fC->Child(tf_data_type_or_implicit);
      VObjectType tf_port_direction_type = fC->Type(tf_data_type_or_implicit);
      if (tf_port_direction_type != slData_type_or_implicit)
        previousDirection = UhdmWriter::getVpiDirection(tf_port_direction_type);
      decl->VpiDirection(previousDirection);
      NodeId tf_param_name = fC->Sibling(tf_data_type_or_implicit);
      if (tf_port_direction_type == VObjectType::slTfPortDir_Ref ||
          tf_port_direction_type == VObjectType::slTfPortDir_ConstRef ||
          tf_port_direction_type == VObjectType::slTfPortDir_Inp ||
          tf_port_direction_type == VObjectType::slTfPortDir_Out ||
          tf_port_direction_type == VObjectType::slTfPortDir_Inout) {
        tf_data_type = fC->Sibling(tf_data_type_or_implicit);
        tf_param_name = fC->Sibling(tf_data_type);
      }
      NodeId type = fC->Child(tf_data_type);

      std::vector<UHDM::range*>* unpackedDimensions = nullptr;
      NodeId varDimension = fC->Sibling(fC->Sibling(fC->Child(tf_port_item)));
      int size;
      unpackedDimensions =
          compileRanges(component, fC, varDimension, compileDesign, nullptr,
                        nullptr, false, size, false);
      if (UHDM::typespec* tempts =
        compileTypespec(component, fC, type,
                        compileDesign, nullptr, nullptr, false)) {
        ts = tempts;
      }
      decl->Typespec(ts);
      decl->Ranges(unpackedDimensions);
      const std::string& name = fC->SymName(tf_param_name);
      decl->VpiName(name);

      NodeId expression = fC->Sibling(tf_param_name);
      if (expression &&
          (fC->Type(expression) != VObjectType::slVariable_dimension) &&
          (fC->Type(type) != VObjectType::slStringConst)) {
        any* defvalue = compileExpression(component, fC, expression, compileDesign, parent, nullptr, false);
        decl->Expr(defvalue);
      }

      tf_port_item = fC->Sibling(tf_port_item);
    }
  }

  return ios;
}

NodeId setFuncTaskQualifiers(const FileContent* fC, NodeId nodeId, task_func* func) {
  NodeId func_decl = nodeId;
  VObjectType func_type = fC->Type(nodeId);

  if (func_type == slFunction_declaration) {
    func_decl = fC->Child(nodeId);
    func_type = fC->Type(func_decl);
  } 
  if (func_type == slTask_declaration) {
    func_decl = fC->Child(nodeId);
    func_type = fC->Type(func_decl);
  }

  bool is_local = false;
  bool is_protected = false;
  while ((func_type == VObjectType::slMethodQualifier_Virtual) ||
         (func_type == VObjectType::slMethodQualifier_ClassItem) ||
         (func_type == VObjectType::slPure_virtual_qualifier) ||
         (func_type == VObjectType::slExtern_qualifier) ||
         (func_type == VObjectType::slClassItemQualifier_Protected) ||
         (func_type == VObjectType::slLifetime_Automatic) ||
         (func_type == VObjectType::slDpi_import_export) ||
         (func_type == VObjectType::slPure_keyword) ||
         (func_type == VObjectType::slImport) ||
         (func_type == VObjectType::slExport) ||
         (func_type == VObjectType::slContext_keyword) ||
         (func_type == VObjectType::slStringConst)
         ) {
    if (func_type == VObjectType::slDpi_import_export) {
      func_decl = fC->Child(func_decl);
      func_type = fC->Type(func_decl);
    }
    if (func_type == VObjectType::slPure_keyword) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiDPIPure(true);
    }
    if (func_type == VObjectType::slExport) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiAccessType(vpiDPIExportAcc);
    }
    if (func_type == VObjectType::slImport) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiAccessType(vpiDPIImportAcc);
    }
    if (func_type == VObjectType::slStringLiteral) {
      std::string ctype = fC->SymName(func_decl);
      if (ctype.front() == '"' && ctype.back() == '"')
          ctype = ctype.substr(1, ctype.length() - 2);
      if (ctype == "DPI-C") {
        if (func) func->VpiDPICStr(vpiDPIC);
      } else if (ctype == "DPI") {
        if (func) func->VpiDPICStr(vpiDPI);
      }        
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }
    if (func_type == VObjectType::slContext_keyword) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiDPIContext(true);
    }
    if (func_type == VObjectType::slMethodQualifier_Virtual) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiVirtual(true);
    }
    if (func_type == VObjectType::slLifetime_Automatic) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiAutomatic(true);
    }
    if (func_type == VObjectType::slClassItemQualifier_Protected) {
      is_protected = true;
      if (func) func->VpiVisibility(vpiProtectedVis);
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }
    if (func_type == VObjectType::slPure_virtual_qualifier) {
      if (func) func->VpiDPIPure(true);
      if (func) func->VpiVirtual(true);
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }
    if (func_type == VObjectType::slExtern_qualifier) {
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
      if (func) func->VpiAccessType(vpiExternAcc);
    }
    if (func_type == VObjectType::slMethodQualifier_ClassItem) {
      NodeId qualifier = fC->Child(func_decl);
      VObjectType type = fC->Type(qualifier);
      if (type == VObjectType::slClassItemQualifier_Static) {
        // TODO: No VPI attribute for static!
      }
      if (type == VObjectType::slClassItemQualifier_Local) {
        if (func) func->VpiVisibility(vpiLocalVis);
        is_local = true;
      }
      if (type == VObjectType::slClassItemQualifier_Protected) {
        is_protected = true;
        if (func) func->VpiVisibility(vpiProtectedVis);
      }
      func_decl = fC->Sibling(func_decl);
      func_type = fC->Type(func_decl);
    }

  }
  if ((!is_local) && (!is_protected)) {
    if (func) func->VpiVisibility(vpiPublicVis);
  }
  return func_decl;
}

bool CompileHelper::compileTask(
  DesignComponent* component, const FileContent* fC, NodeId nodeId,
  CompileDesign* compileDesign, bool isMethod) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::task_func*>* task_funcs = component->getTask_funcs();
  if (task_funcs == nullptr) {
    component->setTask_funcs(s.MakeTask_funcVec());
    task_funcs = component->getTask_funcs();
  }
  std::string name;
  NodeId task_decl = setFuncTaskQualifiers(fC, nodeId, nullptr);
  NodeId Task_body_declaration = 0;
  if (fC->Type(task_decl) == slTask_body_declaration)
    Task_body_declaration = task_decl;
  else 
    Task_body_declaration = fC->Child(task_decl);
  NodeId task_name = fC->Child(Task_body_declaration);
  if (fC->Type(task_name) == VObjectType::slStringConst)
    name = fC->SymName(task_name);
  else if (fC->Type(task_name) == VObjectType::slClass_scope) {
    NodeId Class_type = fC->Child(task_name);
    name = fC->SymName(fC->Child(Class_type));
    name += "::" + fC->SymName(fC->Sibling(task_name));
    task_name = fC->Sibling(task_name);
  }

  UHDM::task* task = nullptr;
  for (auto f : *component->getTask_funcs()) {
    if (f->VpiName() == name) {
      task = reinterpret_cast<UHDM::task*> (f);
      break;
    }
  }
  if (task == nullptr) {
    // make placeholder first
    task = s.MakeTask();
    task->VpiName(name);
    task_funcs->push_back(task);
    return true;
  }
  setFuncTaskQualifiers(fC, nodeId, task);
  task->VpiMethod(isMethod);
  task->VpiFile(fC->getFileName());
  task->VpiLineNo(fC->Line(nodeId));
  task->VpiColumnNo(fC->Column(nodeId));
  NodeId Tf_port_list = fC->Sibling(task_name);
  NodeId Statement_or_null = 0;
  if (fC->Type(Tf_port_list) == slTf_port_list) {
    Statement_or_null = fC->Sibling(Tf_port_list);
    task->Io_decls(compileTfPortList(component, task, fC, Tf_port_list, compileDesign));
  } else if (fC->Type(Tf_port_list) == VObjectType::slTf_item_declaration) {
    NodeId Block_item_declaration = fC->Child(Tf_port_list);
    if (fC->Type(Block_item_declaration) != slBlock_item_declaration) {
      auto results = compileTfPortDecl(component, task, fC, Tf_port_list, compileDesign);
      task->Io_decls(results.first);
      task->Variables(results.second);
      while (fC->Type(Tf_port_list) == VObjectType::slTf_item_declaration) {
        NodeId Tf_port_declaration = fC->Child(Tf_port_list);
        if (fC->Type(Tf_port_declaration) == slTf_port_declaration) { 
        } else if (fC->Type(Tf_port_declaration) == slBlock_item_declaration) { 
          NodeId ItemNode = fC->Child(Tf_port_declaration);
          if (fC->Type(ItemNode) != slData_declaration)
            break;
        } else {
          break;
        }
        Tf_port_list = fC->Sibling(Tf_port_list);
      }
    }
    Statement_or_null = Tf_port_list;
  } else {
    if (fC->Type(Tf_port_list) == slStatement_or_null)
      Statement_or_null = Tf_port_list;
  }

  NodeId MoreStatement_or_null = fC->Sibling(Statement_or_null);
  if (fC->Type(MoreStatement_or_null) == VObjectType::slEndtask) {
    MoreStatement_or_null = 0;
  }
  if (MoreStatement_or_null) {
    // Page 983, 2017 Standard: More than 1 Stmts
    begin* begin = s.MakeBegin();
    task->Stmt(begin);
    begin->VpiParent(task);
    VectorOfany* stmts = s.MakeAnyVec();
    begin->Stmts(stmts);
    while (Statement_or_null) {
      if (Statement_or_null && (fC->Type(Statement_or_null) == slEndtask))
        break;
      if (VectorOfany* sts = compileStmt(component, fC, Statement_or_null, compileDesign, begin)) {
        for (any* st : *sts) {
          UHDM_OBJECT_TYPE stmt_type = st->UhdmType();
          if (stmt_type == uhdmparam_assign) {
            UHDM::VectorOfparam_assign* param_assigns= task->Param_assigns();
            if (param_assigns == nullptr) {
              task->Param_assigns(s.MakeParam_assignVec());
              param_assigns= task->Param_assigns();
            }
            if (param_assign* pst = dynamic_cast<param_assign*> (st))
              param_assigns->push_back(pst);
          } else if (stmt_type == uhdmassign_stmt) {
            assign_stmt* stmt = (assign_stmt*)st;
            if (stmt->Rhs() == nullptr) {
              // Declaration
              VectorOfvariables* vars = task->Variables();
              if (vars == nullptr) {
                task->Variables(s.MakeVariablesVec());
                vars = task->Variables();
              }
              vars->push_back((variables*)stmt->Lhs());
            } else {
              stmts->push_back(st);
            }
          } else {
            stmts->push_back(st);
          }
          st->VpiParent(begin);
        }
      }
      Statement_or_null = fC->Sibling(Statement_or_null);
    }
  } else {
    // Page 983, 2017 Standard: 0 or 1 Stmt
    if (Statement_or_null && (fC->Type(Statement_or_null) != slEndtask)) {
      VectorOfany* stmts = compileStmt(component, fC, Statement_or_null, compileDesign, task);
      if (stmts) {
        for (any* st : *stmts) {
          UHDM_OBJECT_TYPE stmt_type = st->UhdmType();
          if (stmt_type == uhdmparam_assign) {
            UHDM::VectorOfparam_assign* param_assigns= task->Param_assigns();
            if (param_assigns == nullptr) {
              task->Param_assigns(s.MakeParam_assignVec());
              param_assigns= task->Param_assigns();
            }
            if (param_assign* pst = dynamic_cast<param_assign*> (st))
              param_assigns->push_back(pst);
          } else if (stmt_type == uhdmassign_stmt) {
            assign_stmt* stmt = (assign_stmt*)st;
            if (stmt->Rhs() == nullptr) {
              // Declaration
              VectorOfvariables* vars = task->Variables();
              if (vars == nullptr) {
                task->Variables(s.MakeVariablesVec());
                vars = task->Variables();
              }
              vars->push_back((variables*)stmt->Lhs());
            } else {
              task->Stmt(st);
            }  
          } else {
            task->Stmt(st);
          }
          st->VpiParent(task);
        }
      }
    }
  }
  return true;
}

bool CompileHelper::compileClassConstructorDeclaration(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::task_func*>* task_funcs = component->getTask_funcs();
  if (task_funcs == nullptr) {
    component->setTask_funcs(s.MakeTask_funcVec());
    task_funcs = component->getTask_funcs();
  }
  UHDM::function* func = s.MakeFunction();
  func->VpiMethod(true);
  task_funcs->push_back(func);
  func->VpiFile(fC->getFileName());
  func->VpiLineNo(fC->Line(nodeId));
  func->VpiColumnNo(fC->Column(nodeId));
  std::string name = "new";
  std::string className;
  NodeId Tf_port_list = 0;
  Tf_port_list = fC->Child(nodeId);
  if (fC->Type(Tf_port_list) == slClass_scope) {
    NodeId Class_scope = Tf_port_list;
    NodeId Class_type = fC->Child(Class_scope);
    NodeId Class_name = fC->Child(Class_type);
    name = fC->SymName(Class_name);
    className = name;
    name += "::new";
    Tf_port_list = fC->Sibling(Tf_port_list);
  }
  UHDM::class_var* var = s.MakeClass_var();
  func->Return(var);
  UHDM::class_typespec* tps = s.MakeClass_typespec();
  var->Typespec(tps);
  ClassDefinition* cdef = dynamic_cast<ClassDefinition*>(component);
  if (cdef) {
    tps->Class_defn(cdef->getUhdmDefinition());
    const std::string& name = cdef->getUhdmDefinition()->VpiName();
    tps->VpiName(name);
  } else {
    Package* p = dynamic_cast<Package*>(component);
    if (p) {
      ClassDefinition* cdef = p->getClassDefinition(className);
      if (cdef) {
        const std::string& name = cdef->getUhdmDefinition()->VpiName();
        tps->Class_defn(cdef->getUhdmDefinition());
        tps->VpiName(name);
      }
    }
  }  

  func->VpiName(name);
  func->Io_decls(compileTfPortList(component, func, fC, Tf_port_list, compileDesign));

  NodeId Stmt = fC->Sibling(Tf_port_list);
  int nbStmts = 0;
  while (Stmt) {
    if (fC->Type(Stmt) == slBlock_item_declaration) {
      nbStmts++;
    } else if (fC->Type(Stmt) == slSuper_dot_new) {
      nbStmts++;
      NodeId lookAhead = fC->Sibling(Stmt);
      if (fC->Type(lookAhead) == slList_of_arguments) {
        Stmt = fC->Sibling(Stmt);
      }
    } else if (fC->Type(Stmt) == slFunction_statement_or_null) {
      nbStmts++;
    }
    Stmt = fC->Sibling(Stmt);
  }

  if (nbStmts == 1) {
    Stmt = fC->Sibling(Tf_port_list);
    if (fC->Type(Stmt) == slSuper_dot_new) {
      UHDM::method_func_call* mcall = s.MakeMethod_func_call();
      mcall->VpiParent(func);
      mcall->VpiName("super.new");
      NodeId Args = fC->Sibling(Stmt);
      if (fC->Type(Args) == slList_of_arguments) {
        VectorOfany* arguments = compileTfCallArguments(
          component, fC, Args, compileDesign, mcall, nullptr, false, false);
        mcall->Tf_call_args(arguments);
        Stmt = fC->Sibling(Stmt);
      }
      func->Stmt(mcall);
    } else {
      NodeId Statement = fC->Child(Stmt);
      if (Statement) {
        VectorOfany* sts =
            compileStmt(component, fC, Statement, compileDesign, func);
        if (sts) {
          any* st = (*sts)[0];
          st->VpiParent(func);
          func->Stmt(st);
        }
      }
    }
  } else if (nbStmts > 1) {
    begin* begin = s.MakeBegin();
    func->Stmt(begin);
    begin->VpiParent(func);
    VectorOfany* stmts = s.MakeAnyVec();
    begin->Stmts(stmts);
    Stmt = fC->Sibling(Tf_port_list);
    while (Stmt) {
      if (fC->Type(Stmt) == slSuper_dot_new) {
        UHDM::method_func_call* mcall = s.MakeMethod_func_call();
        mcall->VpiParent(func);
        mcall->VpiName("super.new");
        NodeId Args = fC->Sibling(Stmt);
        if (fC->Type(Args) == slList_of_arguments) {
          VectorOfany* arguments =
              compileTfCallArguments(component, fC, Args, compileDesign, mcall, nullptr, false, false);
          mcall->Tf_call_args(arguments);
          Stmt = fC->Sibling(Stmt);
        }
        stmts->push_back(mcall);
        mcall->VpiParent(begin);
      } else {
        NodeId Statement = fC->Child(Stmt);
        if (Statement) {
          if (VectorOfany* sts =
                  compileStmt(component, fC, Statement, compileDesign, begin)) {
            for (any* st : *sts) {
              stmts->push_back(st);
              st->VpiParent(begin);
            }
          }
        }
      }
      Stmt = fC->Sibling(Stmt);
    }
  }

  return true;
}

bool CompileHelper::compileFunction(
  DesignComponent* component, const FileContent* fC,
  NodeId nodeId,
  CompileDesign* compileDesign, bool isMethod) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::task_func*>* task_funcs = component->getTask_funcs();
  if (task_funcs == nullptr) {
    component->setTask_funcs(s.MakeTask_funcVec());
    task_funcs = component->getTask_funcs();
  }
  std::string name;
  NodeId func_decl = setFuncTaskQualifiers(fC, nodeId, nullptr);
  VObjectType func_decl_type = fC->Type(func_decl);
  bool constructor = false;
  if (func_decl_type == slClass_constructor_declaration ||
      func_decl_type == slClass_constructor_prototype) {
    constructor = true;
  }
  NodeId Tf_port_list = 0;
  if (constructor) {
    Tf_port_list = fC->Child(func_decl);
    name = "new";
  } else {
    NodeId Function_body_declaration = 0;
    if (fC->Type(func_decl) == slFunction_body_declaration) 
      Function_body_declaration = func_decl;
    else 
      Function_body_declaration = fC->Child(func_decl);
    NodeId Function_data_type_or_implicit = fC->Child(Function_body_declaration);
    NodeId Function_name = fC->Sibling(Function_data_type_or_implicit);
    if (fC->Type(Function_name) == VObjectType::slStringConst) {
      name = fC->SymName(Function_name);
      Tf_port_list = fC->Sibling(Function_name);
    } else if (fC->Type(Function_name) == VObjectType::slClass_scope) {
      NodeId Class_type = fC->Child(Function_name);
      name = fC->SymName(fC->Child(Class_type));
      NodeId suffixname = fC->Sibling(Function_name);
      name += "::" + fC->SymName(suffixname);
      Tf_port_list = fC->Sibling(suffixname);
    }
  }
  UHDM::function* func = nullptr;
  for (auto f : *component->getTask_funcs()) {
    if (f->VpiName() == name) {
      func = dynamic_cast<UHDM::function*>(f);
      break;
    }
  }
  if (func == nullptr) {
    // make placeholder first
    func = s.MakeFunction();
    func->VpiName(name);
    task_funcs->push_back(func);
    return true;
  }
  setFuncTaskQualifiers(fC, nodeId, func);
  func->VpiMethod(isMethod);
  func->VpiFile(fC->getFileName());
  func->VpiLineNo(fC->Line(nodeId));
  func->VpiColumnNo(fC->Column(nodeId));
  if (constructor) {
    UHDM::class_var* var = s.MakeClass_var();
    func->Return(var);
    UHDM::class_typespec* tps = s.MakeClass_typespec();
    var->Typespec(tps);
    ClassDefinition* cdef = dynamic_cast<ClassDefinition*> (component);
    tps->Class_defn(cdef->getUhdmDefinition());
    tps->VpiName(cdef->getUhdmDefinition()->VpiFullName());
  } else {
    NodeId Function_body_declaration = 0;
    if (fC->Type(func_decl) == slFunction_body_declaration) 
      Function_body_declaration = func_decl;
    else 
      Function_body_declaration = fC->Child(func_decl);
    NodeId Function_data_type_or_implicit = fC->Child(Function_body_declaration);
    NodeId Function_data_type = fC->Child(Function_data_type_or_implicit);
    NodeId Return_data_type = fC->Child(Function_data_type);
    variables* var = dynamic_cast<variables*>(
        compileVariable(component, fC, Return_data_type, compileDesign, nullptr,
                        nullptr, true, false));
    if (var) {
      var->VpiName("");
    }                    
    func->Return(var);
  }
  
  NodeId Function_statement_or_null = Tf_port_list;
  if (fC->Type(Tf_port_list) == VObjectType::slTf_port_list) {
    func->Io_decls(compileTfPortList(component, func, fC, Tf_port_list, compileDesign));
    Function_statement_or_null = fC->Sibling(Tf_port_list);
  } else if (fC->Type(Tf_port_list) == VObjectType::slTf_item_declaration) {
    auto results = compileTfPortDecl(component, func, fC, Tf_port_list, compileDesign);
    func->Io_decls(results.first);
    func->Variables(results.second);
    while (fC->Type(Tf_port_list) == VObjectType::slTf_item_declaration) {
      Tf_port_list = fC->Sibling(Tf_port_list);
    }
    Function_statement_or_null = Tf_port_list;
  }

  NodeId MoreFunction_statement_or_null = fC->Sibling(Function_statement_or_null);
  if (fC->Type(MoreFunction_statement_or_null) == VObjectType::slEndfunction) {
    MoreFunction_statement_or_null = 0;
  }
  if (MoreFunction_statement_or_null) {
    // Page 983, 2017 Standard: More than 1 Stmts
    begin* begin = s.MakeBegin();
    func->Stmt(begin);
    begin->VpiParent(func);
    VectorOfany* stmts = s.MakeAnyVec();
    begin->Stmts(stmts);
    while (Function_statement_or_null) {
      NodeId Statement = fC->Child(Function_statement_or_null);
      if (Statement) {
        if (VectorOfany* sts = compileStmt(component, fC, Statement, compileDesign, begin)) {
          for (any* st : *sts) {
            UHDM_OBJECT_TYPE stmt_type = st->UhdmType();
            if (stmt_type == uhdmparam_assign) {
              UHDM::VectorOfparam_assign* param_assigns = func->Param_assigns();
              if (param_assigns == nullptr) {
                func->Param_assigns(s.MakeParam_assignVec());
                param_assigns = func->Param_assigns();
              }
              if (param_assign* pst = dynamic_cast<param_assign*> (st))
                param_assigns->push_back(pst);
            } else if (stmt_type == uhdmassign_stmt) {
              assign_stmt* stmt = (assign_stmt*) st;
              if (stmt->Rhs() == nullptr) {
                // Declaration
                VectorOfvariables* vars = func->Variables();
                if (vars == nullptr) {
                  func->Variables(s.MakeVariablesVec());
                  vars = func->Variables(); 
                }
                vars->push_back((variables*) stmt->Lhs());
              } else {
               stmts->push_back(st);
              }
            } else {
              stmts->push_back(st);
            }
            st->VpiParent(begin);
          }
        }
      }
      Function_statement_or_null = fC->Sibling(Function_statement_or_null);
    }
  } else {
    // Page 983, 2017 Standard: 0 or 1 Stmt
    NodeId Statement = fC->Child(Function_statement_or_null);
    if (Statement) {
      VectorOfany* sts = compileStmt(component, fC, Statement, compileDesign, func);
      if (sts) {
        any* st = (*sts)[0];
        UHDM_OBJECT_TYPE stmt_type = st->UhdmType();
        if (stmt_type == uhdmparam_assign) {
          UHDM::VectorOfparam_assign* param_assigns = func->Param_assigns();
          if (param_assigns == nullptr) {
            func->Param_assigns(s.MakeParam_assignVec());
            param_assigns = func->Param_assigns();
          }
          if (param_assign* pst = dynamic_cast<param_assign*> (st))
            param_assigns->push_back(pst);
        } else if (stmt_type == uhdmassign_stmt) {
          assign_stmt* stmt = (assign_stmt*)st;
          if (stmt->Rhs() == nullptr) {
            // Declaration
            VectorOfvariables* vars = func->Variables();
            if (vars == nullptr) {
              func->Variables(s.MakeVariablesVec());
              vars = func->Variables();
            }
            vars->push_back((variables*)stmt->Lhs());
          } else {
            func->Stmt(st);
          }
        } else {
          func->Stmt(st);
        }
        st->VpiParent(func);
       
      }
    }
  }
  return true;
}

Function* CompileHelper::compileFunctionPrototype(
    DesignComponent* scope, const FileContent* fC,
    NodeId id, CompileDesign* compileDesign) {   
  std::string funcName;
  NodeId function_name = 0;
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::task_func*>* task_funcs = scope->getTask_funcs();
  if (task_funcs == nullptr) {
    scope->setTask_funcs(s.MakeTask_funcVec());
    task_funcs = scope->getTask_funcs();
  }
  UHDM::function* func = s.MakeFunction();
  task_funcs->push_back(func);
  /*
  n<"DPI-C"> u<2> t<StringLiteral> p<15> s<3> l<3>
  n<> u<3> t<Context_keyword> p<15> s<14> l<3>
  n<> u<4> t<IntVec_TypeBit> p<5> l<3>
  n<> u<5> t<Data_type> p<6> c<4> l<3>
  n<> u<6> t<Function_data_type> p<14> c<5> s<7> l<3>
  n<SV2C_peek> u<7> t<StringConst> p<14> s<13> l<3>
  n<> u<8> t<IntegerAtomType_Int> p<9> l<3>
  n<> u<9> t<Data_type> p<10> c<8> l<3>
  n<> u<10> t<Data_type_or_implicit> p<12> c<9> s<11> l<3>
  n<x_id> u<11> t<StringConst> p<12> l<3>
  n<> u<12> t<Tf_port_item> p<13> c<10> l<3>
  n<> u<13> t<Tf_port_list> p<14> c<12> l<3>
  n<> u<14> t<Function_prototype> p<15> c<6> l<3>
  n<> u<15> t<Dpi_import_export> p<16> c<2> l<3>
   */
  NodeId prop = setFuncTaskQualifiers(fC, id, func);
  NodeId func_prototype = prop;
  NodeId function_data_type = fC->Child(func_prototype);
  NodeId data_type = fC->Child(function_data_type);
  NodeId type = fC->Child(data_type);
  VObjectType the_type = fC->Type(type);
  std::string typeName;
  if (the_type == VObjectType::slStringConst) {
    typeName = fC->SymName(type);
  } else if (the_type == VObjectType::slClass_scope) {
    NodeId class_type = fC->Child(type);
    NodeId class_name = fC->Child(class_type);
    typeName = fC->SymName(class_name);
    typeName += "::";
    NodeId symb_id = fC->Sibling(type);
    typeName += fC->SymName(symb_id);
  } else {
    typeName = VObject::getTypeName(the_type);
  }

  if (fC->Type(fC->Child(id)) == VObjectType::slExport) {
    function_name = fC->Child(func_prototype);
    funcName = fC->SymName(function_name);
  } else if (fC->Type(fC->Child(id)) == VObjectType::slImport) {
    function_name = fC->Sibling(function_data_type);
    funcName = fC->SymName(function_name);
  }

  func->VpiFile(fC->getFileName());
  func->VpiLineNo(fC->Line(id));
  func->VpiColumnNo(fC->Column(id));
  func->Return(dynamic_cast<variables*>(
        compileVariable(scope, fC, type, compileDesign, nullptr,
                        nullptr, true, false)));
  NodeId Tf_port_list = 0;
  if (fC->Type(function_name) == VObjectType::slStringConst) {
    Tf_port_list = fC->Sibling(function_name);
  } else if (fC->Type(function_name) == VObjectType::slClass_scope) {
    NodeId Class_type = fC->Child(function_name);
    funcName = fC->SymName(fC->Child(Class_type));
    NodeId suffixname = fC->Sibling(function_name);
    funcName += "::" + fC->SymName(suffixname);
    Tf_port_list = fC->Sibling(suffixname);
  }

  func->VpiName(funcName);

  if (fC->Type(Tf_port_list) == VObjectType::slTf_port_list) {
    func->Io_decls(compileTfPortList(scope, func, fC, Tf_port_list, compileDesign));
  } else if (fC->Type(Tf_port_list) == VObjectType::slTf_item_declaration) {
    auto results = compileTfPortDecl(scope, func, fC, Tf_port_list, compileDesign);
    func->Io_decls(results.first);
  }

  DataType* returnType = new DataType(); 
  returnType->init(fC, type, typeName, fC->Type(type));
  Function* result = new Function(scope, fC, id, funcName, returnType);
  Variable* variable = new Variable(returnType, fC, id, 0, funcName);
  result->addVariable(variable);
  result->compile(*this);
  return result;
}

UHDM::any* CompileHelper::compileProceduralContinuousAssign(
  DesignComponent* component, const FileContent* fC, NodeId nodeId,
  CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId assigntypeid = fC->Child(nodeId);
  VObjectType assigntype = fC->Type(assigntypeid);
  UHDM::atomic_stmt* the_stmt = nullptr;
  switch (assigntype) {
    case VObjectType::slAssign: {
      assign_stmt* assign = s.MakeAssign_stmt();
      NodeId Variable_assignment = fC->Sibling(assigntypeid);
      NodeId Variable_lvalue = fC->Child(Variable_assignment);
      NodeId Expression = fC->Sibling(Variable_lvalue);
      expr* lhs = (expr*) compileExpression(component, fC, fC->Child(Variable_lvalue), compileDesign);
      if (lhs)
        lhs->VpiParent(assign);
      expr* rhs = (expr*) compileExpression(component, fC, Expression, compileDesign);
      if (rhs)
        rhs->VpiParent(assign);
      assign->Lhs(lhs);
      assign->Rhs(rhs);
      the_stmt = assign;
      break;
    }
    case VObjectType::slForce: {
      force* assign = s.MakeForce();
      NodeId Variable_assignment = fC->Sibling(assigntypeid);
      NodeId Variable_lvalue = fC->Child(Variable_assignment);
      NodeId Expression = fC->Sibling(Variable_lvalue);
      expr* lhs = (expr*) compileExpression(component, fC, Variable_lvalue, compileDesign);
      if (lhs)
        lhs->VpiParent(assign);
      expr* rhs = (expr*) compileExpression(component, fC, Expression, compileDesign);
      if (rhs)
        rhs->VpiParent(assign);
      assign->Lhs(lhs);
      assign->Rhs(rhs);
      the_stmt = assign;
      break;
    }
    case VObjectType::slDeassign: {
      deassign* assign = s.MakeDeassign();
      NodeId Variable_assignment = fC->Sibling(assigntypeid);
      NodeId Variable_lvalue = fC->Child(Variable_assignment);
      expr* lhs = (expr*) compileExpression(component, fC, Variable_lvalue, compileDesign);
      if (lhs)
        lhs->VpiParent(assign);
      assign->Lhs(lhs);
      the_stmt = assign;
      break;
    }
    case VObjectType::slRelease: {
      release* assign = s.MakeRelease();
      NodeId Variable_assignment = fC->Sibling(assigntypeid);
      NodeId Variable_lvalue = fC->Child(Variable_assignment);
      expr* lhs = (expr*) compileExpression(component, fC, Variable_lvalue, compileDesign);
      if (lhs)
        lhs->VpiParent(assign);
      assign->Lhs(lhs);
      the_stmt = assign;
      break;
    }
    default:
      break;
  }
  return the_stmt;
}


UHDM::any* CompileHelper::compileForLoop(
  DesignComponent* component, const FileContent* fC, NodeId nodeId,
  CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  for_stmt* for_stmt = s.MakeFor_stmt();
  NodeId For_initialization = 0;
  NodeId Condition = 0;
  NodeId For_step = 0;
  NodeId Statement_or_null = 0;
  NodeId tmp = fC->Sibling(nodeId);
  while (tmp) {
    if (fC->Type(tmp) == slFor_initialization) {
      For_initialization = tmp;
    } else if (fC->Type(tmp) == slExpression) {
      Condition = tmp;
    } else if (fC->Type(tmp) == slFor_step) {
      For_step = tmp;
    } else if (fC->Type(tmp) == slStatement_or_null) {
      Statement_or_null = tmp;
    }
    tmp = fC->Sibling(tmp);
  }

  // Init
  if (For_initialization) {
    NodeId For_variable_declaration = fC->Child(For_initialization);
    if (fC->Type(For_variable_declaration) == slFor_variable_declaration) {
      while (For_variable_declaration) {
        VectorOfany* stmts = for_stmt->VpiForInitStmts();
        if (stmts == nullptr) {
          for_stmt->VpiForInitStmts(s.MakeAnyVec());
          stmts = for_stmt->VpiForInitStmts();
        }

        NodeId Data_type = fC->Child(For_variable_declaration);
        NodeId Var = fC->Sibling(Data_type);
        NodeId Expression = fC->Sibling(Var);
        assign_stmt* assign_stmt = s.MakeAssign_stmt();
        assign_stmt->VpiParent(for_stmt);

        variables* var =
            (variables*)compileVariable(component, fC, Data_type, compileDesign,
                                        assign_stmt, nullptr, true, false);
        assign_stmt->Lhs(var);
        if (var) {
          var->VpiParent(assign_stmt);
          var->VpiName(fC->SymName(Var));
        }

        expr* rhs =
            (expr*)compileExpression(component, fC, Expression, compileDesign);
        if (rhs) rhs->VpiParent(assign_stmt);
        assign_stmt->Rhs(rhs);
        stmts->push_back(assign_stmt);

        For_variable_declaration = fC->Sibling(For_variable_declaration);
      }
    } else if (fC->Type(For_variable_declaration) ==
               slList_of_variable_assignments) {
      NodeId List_of_variable_assignments = For_variable_declaration;
      NodeId Variable_assignment = fC->Child(List_of_variable_assignments);
      while (Variable_assignment) {
        NodeId Variable_lvalue = fC->Child(Variable_assignment);
        NodeId Expression = fC->Sibling(Variable_lvalue);
        VectorOfany* stmts = for_stmt->VpiForInitStmts();
        if (stmts == nullptr) {
          for_stmt->VpiForInitStmts(s.MakeAnyVec());
          stmts = for_stmt->VpiForInitStmts();
        }

        assign_stmt* assign_stmt = s.MakeAssign_stmt();
        assign_stmt->VpiParent(for_stmt);

        variables* var = (variables*)compileVariable(
            component, fC, Variable_lvalue, compileDesign, assign_stmt, nullptr,
            true, false);
        assign_stmt->Lhs(var);
        if (var) {
          var->VpiParent(assign_stmt);
        }

        expr* rhs =
            (expr*)compileExpression(component, fC, Expression, compileDesign);
        if (rhs) rhs->VpiParent(assign_stmt);
        assign_stmt->Rhs(rhs);
        stmts->push_back(assign_stmt);

        Variable_assignment = fC->Sibling(Variable_assignment);
      }
    }
  }

  // Condition
  if (Condition) {
    expr* cond = (expr*) compileExpression(component, fC, Condition, compileDesign);
    if (cond)
      cond->VpiParent(for_stmt);
    for_stmt->VpiCondition(cond);
  }

  // Increment
  if (For_step) {
    NodeId For_step_assignment = fC->Child(For_step);
    while (For_step_assignment) {
      VectorOfany* stmts = for_stmt->VpiForIncStmts();
      if (stmts == nullptr) {
        for_stmt->VpiForIncStmts(s.MakeAnyVec());
        stmts = for_stmt->VpiForIncStmts();
      }

      NodeId Expression = fC->Child(For_step_assignment);
      if (fC->Type(Expression) == slOperator_assignment) {
        std::vector<UHDM::any*>* incstmts =
            compileStmt(component, fC, Expression, compileDesign, for_stmt);
        if (incstmts) {
          for (auto stmt : *incstmts) {
            stmts->push_back(stmt);
          }
        }
      } else {
        expr* exp =
            (expr*)compileExpression(component, fC, Expression, compileDesign);
        if (exp) {
          exp->VpiParent(for_stmt);
          stmts->push_back(exp);
        }
      }
      For_step_assignment = fC->Sibling(For_step_assignment);
    }
  }

  // Stmt
  if (Statement_or_null) {
    VectorOfany* stmts = compileStmt(component, fC, Statement_or_null, compileDesign, for_stmt);
    if (stmts)
      for_stmt->VpiStmt((*stmts)[0]);
  }

/*
n<> u<36> t<IntegerAtomType_Int> p<37> l<5>
n<> u<37> t<Data_type> p<43> c<36> s<38> l<5>
n<i> u<38> t<StringConst> p<43> s<42> l<5>
n<PTR_WIDTH> u<39> t<StringConst> p<40> l<5>
n<> u<40> t<Primary_literal> p<41> c<39> l<5>
n<> u<41> t<Primary> p<42> c<40> l<5>
n<> u<42> t<Expression> p<43> c<41> l<5>
n<> u<43> t<For_variable_declaration> p<44> c<37> l<5>
n<> u<44> t<For_initialization> p<84> c<43> s<54> l<5>
n<i> u<45> t<StringConst> p<46> l<5>
n<> u<46> t<Primary_literal> p<47> c<45> l<5>
n<> u<47> t<Primary> p<48> c<46> l<5>
n<> u<48> t<Expression> p<54> c<47> s<49> l<5>
n<> u<49> t<BinOp_GreatEqual> p<54> s<53> l<5>
n<0> u<50> t<IntConst> p<51> l<5>
n<> u<51> t<Primary_literal> p<52> c<50> l<5>
n<> u<52> t<Primary> p<53> c<51> l<5>
n<> u<53> t<Expression> p<54> c<52> l<5>
n<> u<54> t<Expression> p<84> c<48> s<63> l<5>
n<i> u<55> t<StringConst> p<56> l<5>
n<> u<56> t<Hierarchical_identifier> p<59> c<55> s<58> l<5>
n<> u<57> t<Bit_select> p<58> l<5>
n<> u<58> t<Select> p<59> c<57> l<5>
n<> u<59> t<Variable_lvalue> p<61> c<56> s<60> l<5>
n<> u<60> t<IncDec_MinusMinus> p<61> l<5>
n<> u<61> t<Inc_or_dec_expression> p<62> c<59> l<5>
n<> u<62> t<For_step_assignment> p<63> c<61> l<5>
n<> u<63> t<For_step> p<84> c<62> s<82> l<5>
n<dec_tmp> u<64> t<StringConst> p<65> l<6>
n<> u<65> t<Hierarchical_identifier> p<72> c<64> s<71> l<6>
n<i> u<66> t<StringConst> p<67> l<6>
n<> u<67> t<Primary_literal> p<68> c<66> l<6>
n<> u<68> t<Primary> p<69> c<67> l<6>
n<> u<69> t<Expression> p<70> c<68> l<6>
n<> u<70> t<Bit_select> p<71> c<69> l<6>
n<> u<71> t<Select> p<72> c<70> l<6>
n<> u<72> t<Variable_lvalue> p<78> c<65> s<73> l<6>
n<> u<73> t<AssignOp_Assign> p<78> s<77> l<6>
n<0> u<74> t<IntConst> p<75> l<6>
n<> u<75> t<Primary_literal> p<76> c<74> l<6>
n<> u<76> t<Primary> p<77> c<75> l<6>
n<> u<77> t<Expression> p<78> c<76> l<6>
n<> u<78> t<Operator_assignment> p<79> c<72> l<6>
n<> u<79> t<Blocking_assignment> p<80> c<78> l<6>
n<> u<80> t<Statement_item> p<81> c<79> l<6>
n<> u<81> t<Statement> p<82> c<80> l<6>
n<> u<82> t<Statement_or_null> p<84> c<81> l<6>
n<> u<83> t<For> p<84> s<44> l<5>
*/

  return for_stmt;
}


UHDM::any* CompileHelper::bindVariable(DesignComponent* component, ValuedComponentI* instance, const std::string& name, CompileDesign* compileDesign) {
  UHDM::any* result = nullptr;
  /*
  if (ModuleInstance* instance = dynamic_cast<ModuleInstance*> (instance)) {

  }
  */
  return result;
}

UHDM::any* CompileHelper::bindVariable(DesignComponent* component, const UHDM::any* scope, const std::string& name, CompileDesign* compileDesign) {
  UHDM_OBJECT_TYPE scope_type = scope->UhdmType();
  switch (scope_type) {
    case uhdmfunction: {
      function* lscope = (function*) scope;
      if (lscope->Variables()) {
        for (auto var: *lscope->Variables()) {
          if (var->VpiName() == name)
            return var;
        }
      }
      if (lscope->Io_decls()) {
        for (auto var: *lscope->Io_decls()) {
          if (var->VpiName() == name)
            return var;
        }
      }
      break;
    }
    case uhdmtask: {
      task* lscope = (task*) scope;
      if (lscope->Variables()) {
        for (auto var: *lscope->Variables()) {
          if (var->VpiName() == name)
            return var;
        }
      }
      if (lscope->Io_decls()) {
        for (auto var: *lscope->Io_decls()) {
          if (var->VpiName() == name)
            return var;
        }
      }
      break;
    }
    case uhdmbegin: {
      begin* lscope = (begin*) scope;
      if (lscope->Variables()) {
        for (auto var: *lscope->Variables()) {
          if (var->VpiName() == name)
            return var;
        }
      }
      break;
    }
    case uhdmmodule: {
      // We never get here, as modules are built as DesignComponent, not as UHDM::module.
      // Need late binding.
      break;
    }
    default:
      break;
  }
  if (scope->VpiParent()) {
    return bindVariable(component, scope->VpiParent(), name, compileDesign);
  }
  return nullptr;
}


UHDM::method_func_call* CompileHelper::compileRandomizeCall(DesignComponent* component,
                                  const FileContent* fC, NodeId Identifier_list,
                                  CompileDesign* compileDesign, UHDM::any* pexpr) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  method_func_call* func_call = s.MakeMethod_func_call();  
  method_func_call* result = func_call;
  func_call->VpiName("randomize");
  NodeId With = 0;
  if (fC->Type(Identifier_list) == slIdentifier_list) {
    With = fC->Sibling(Identifier_list);
  } else if (fC->Type(Identifier_list) == slWith) {
    With = Identifier_list;
  }
  NodeId Constraint_block = fC->Sibling(With);
  if (fC->Type(Identifier_list) == slIdentifier_list) {
    VectorOfany* arguments = compileTfCallArguments(component, fC, Identifier_list, compileDesign, func_call, nullptr, false, false);
    func_call->Tf_call_args(arguments);
  }

  if (Constraint_block) {
    UHDM::any* cblock = compileConstraintBlock(component, fC, Constraint_block, compileDesign);
    func_call->With(cblock);
  }
  return result;
}

UHDM::any* CompileHelper::compileConstraintBlock(DesignComponent* component,
                                  const FileContent* fC, NodeId nodeId,
                                  CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  UHDM::constraint* cons = s.MakeConstraint();
  result = cons;
  return result;
}
