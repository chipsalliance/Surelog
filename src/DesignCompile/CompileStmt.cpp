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
#include "DesignCompile/CompileHelper.h"
#include "CompileDesign.h"
#include "uhdm.h"
#include "expr.h"
#include "UhdmWriter.h"

using namespace SURELOG;

VectorOfany* CompileHelper::compileStmt(
  DesignComponent* component,
  const FileContent* fC, NodeId the_stmt,
  CompileDesign* compileDesign, UHDM::any* pstmt) {
  VectorOfany* results = nullptr;
  UHDM::Serializer& s = compileDesign->getSerializer();
  VObjectType type = fC->Type(the_stmt);
  UHDM::any* stmt = nullptr;
  switch (type) {
  case VObjectType::slStatement_or_null: {
    NodeId child =  fC->Child(the_stmt);
    if (child == 0) {
      // That is the null statement (no statement)
      return nullptr;
    }
    return compileStmt(component, fC, child, compileDesign, pstmt);
  }
  case VObjectType::slBlock_item_declaration:
  case VObjectType::slStatement:
  case VObjectType::slJump_statement:
  case VObjectType::slStatement_item:
  case VObjectType::slImmediate_assertion_statement:
  case VObjectType::slProcedural_assertion_statement:
  case VObjectType::slLoop_statement: {
	  return compileStmt(component, fC, fC->Child(the_stmt), compileDesign, pstmt);
  }
  case VObjectType::slProcedural_timing_control_statement:{
    UHDM::atomic_stmt* dc = compileProceduralTimingControlStmt(component, fC, the_stmt, compileDesign);
    stmt = dc;
    break;
  }
  case VObjectType::slNonblocking_assignment: {
    NodeId Operator_assignment  = the_stmt;
    UHDM::assignment* assign = compileBlockingAssignment(component, fC,
                Operator_assignment, false, compileDesign);
    stmt = assign;
    break;
  }
  case VObjectType::slBlocking_assignment: {
    NodeId Operator_assignment = fC->Child(the_stmt);
    UHDM::assignment* assign = compileBlockingAssignment(component, fC,
                Operator_assignment, true, compileDesign);
    stmt = assign;
    break;
  }
  case VObjectType::slSubroutine_call_statement: {
	  NodeId Subroutine_call = fC->Child(the_stmt);
    UHDM::tf_call* call = compileTfCall(component, fC, Subroutine_call ,compileDesign);
	  stmt = call;
  	break;
  }
  case VObjectType::slSystem_task: {
    UHDM::tf_call* call = compileTfCall(component, fC, the_stmt, compileDesign);
    stmt = call;
    break;
  }
  case VObjectType::slConditional_statement: {
	  NodeId Conditional_statement = the_stmt;
    NodeId Cond_predicate = fC->Child(Conditional_statement);
	  UHDM::atomic_stmt* cstmt = compileConditionalStmt(component, fC,
                                   Cond_predicate, compileDesign);
  	stmt = cstmt;
  	break;
  }
  case VObjectType::slCond_predicate: {
    NodeId Cond_predicate = the_stmt;
	  UHDM::atomic_stmt* cstmt = compileConditionalStmt(component, fC,
                                   Cond_predicate, compileDesign);
  	stmt = cstmt;
  	break;
  }
  case VObjectType::slCase_statement: {
    NodeId Case_statement = the_stmt;
	  UHDM::atomic_stmt* cstmt = compileCaseStmt(component, fC,
                                   Case_statement, compileDesign);
  	stmt = cstmt;
    break;
  }
  case VObjectType::slSeq_block: {
	  NodeId item = fC->Child(the_stmt);
	  VectorOfany* stmts = s.MakeAnyVec();
    if (fC->Type(item) == VObjectType::slStringConst) {
      UHDM::named_begin* begin = s.MakeNamed_begin();
      begin->Stmts(stmts);
      stmt = begin;
      begin->VpiName(fC->SymName(item));
      item = fC->Sibling(item);
    } else {
      UHDM::begin* begin = s.MakeBegin();
      begin->Stmts(stmts);
      stmt = begin;
    }
	  while (item) {
	    VectorOfany* cstmts = compileStmt(component, fC, item, compileDesign, stmt);
	    if (cstmts) {
        for (any* cstmt : *cstmts) {
	        stmts->push_back(cstmt);
          cstmt->VpiParent(stmt);
        }
      }
	    item = fC->Sibling(item);
      if (item && (fC->Type(item) == VObjectType::slEnd)) {
        break;
      }
  	}
	  break;
  }
  case VObjectType::slPar_block: {
	  NodeId item = fC->Child(the_stmt);
	  VectorOfany* stmts = s.MakeAnyVec();
    if (fC->Type(item) == VObjectType::slStringConst) {
      UHDM::named_fork* fork = s.MakeNamed_fork();
      fork->Stmts(stmts);
      stmt = fork;
      fork->VpiName(fC->SymName(item));
      item = fC->Sibling(item);
    } else {
      UHDM::fork_stmt* fork = s.MakeFork_stmt();
      fork->Stmts(stmts);
      stmt = fork;
    }
	  while (item) {
      VectorOfany* cstmts = compileStmt(component, fC, item, compileDesign, stmt);
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
        } else if (jointype == VObjectType::slJoin_any_keyword) {
          vpijointype = vpiJoinAny;
        } else if (jointype == VObjectType::slJoin_none_keyword) {
          vpijointype = vpiJoinNone;
        }
        if (stmt->UhdmType() == uhdmnamed_fork) {
          ((UHDM::named_fork*)stmt)->VpiJoinType(vpijointype);
        } else {
          ((UHDM::fork_stmt*)stmt)->VpiJoinType(vpijointype);
        }
      }
  	}
	  break;
  }
  case VObjectType::slForever: {
    UHDM::forever_stmt* forever = s.MakeForever_stmt();
    NodeId item = fC->Sibling(the_stmt);
    VectorOfany* forev = compileStmt(component, fC, item, compileDesign, forever);
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
    UHDM::any* var = compileVariable(component, fC, fC->Child(Ps_or_hierarchical_array_identifier), compileDesign, foreach, nullptr, true);
    NodeId Loop_variables = fC->Sibling(Ps_or_hierarchical_array_identifier);
    UHDM::any* loop_var = compileVariable(component, fC, fC->Child(Loop_variables), compileDesign, foreach, nullptr, true);
    NodeId Statement = fC->Sibling(Loop_variables);
    VectorOfany* forev = compileStmt(component, fC, Statement, compileDesign, foreach);
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
    foreach->VpiLoopVars(loop_var);
    stmt = foreach;
    break;
  }
  case VObjectType::slProcedural_continuous_assignment: {
    any* conta = compileProceduralContinuousAssign(component, fC, the_stmt, compileDesign);
    stmt = conta;
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
    VectorOfany* repeat_stmts = compileStmt(component, fC, rstmt, compileDesign, repeat);
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
    VectorOfany* while_stmts = compileStmt(component, fC, rstmt, compileDesign, while_st);
    if (while_stmts) {
      any* stmt = (*while_stmts)[0];
      while_st->VpiStmt(stmt);
      stmt->VpiParent(while_st);
    }
    stmt = while_st;
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
  case VObjectType::slContinueStmt: {
    UHDM::continue_stmt* cstmt = s.MakeContinue_stmt();
    stmt = cstmt;
    break;
  }
  case VObjectType::slSimple_immediate_assertion_statement: {
    stmt = compileImmediateAssertion(component, fC, fC->Child(the_stmt), compileDesign, pstmt, nullptr);
    break;
  }
  case VObjectType::slData_declaration: {
    results = compileDataDeclaration(component, fC, fC->Child(the_stmt), compileDesign);
    break;
  }
  case VObjectType::slStringConst: {
    const std::string& label = fC->SymName(the_stmt);
    VectorOfany* stmts = compileStmt(component, fC, fC->Sibling(the_stmt), compileDesign, pstmt);
    if (stmts) {
      for(any* st : *stmts) {
        if (UHDM::atomic_stmt* stm = dynamic_cast<atomic_stmt*> (st))
          stm->VpiName(label);
        else if (UHDM::assertion* stm = dynamic_cast<assertion*> (st))
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
    stmt->VpiFile(fC->getFileName(the_stmt));
    stmt->VpiLineNo(fC->Line(the_stmt));
    stmt->VpiParent(pstmt);
    results = s.MakeAnyVec();
    results->push_back(stmt);
  } else if (results) {
  } else {
    VObjectType stmttype = fC->Type(the_stmt);
    if ((stmttype != VObjectType::slEnd) && (stmttype != VObjectType::slJoin_keyword) && (stmttype != VObjectType::slJoin_any_keyword)
     && (stmttype != VObjectType::slJoin_none_keyword)) {
      unsupported_stmt* ustmt = s.MakeUnsupported_stmt();
      std::string fileContent = FileUtils::getFileContent(fC->getFileName());
      std::string lineText = StringUtils::getLineInString(fileContent, fC->Line(the_stmt));
      ustmt->VpiValue("STRING:" + lineText);
      ustmt->VpiFile(fC->getFileName(the_stmt));
      ustmt->VpiLineNo(fC->Line(the_stmt));
      ustmt->VpiParent(pstmt);
      stmt = ustmt;
      //std::cout << "UNSUPPORTED STATEMENT: " << fC->getFileName(the_stmt) << ":" << fC->Line(the_stmt) << ":" << std::endl;
      //std::cout << " -> " << fC->printObject(the_stmt) << std::endl;
    }

  }
  return results;
}

VectorOfany* CompileHelper::compileDataDeclaration(DesignComponent* component,
                                                   const FileContent* fC,
                                                   NodeId nodeId,
                                                   CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  VectorOfany* results = nullptr;
  VObjectType type = fC->Type(nodeId);
  bool automatic_status = false;
  bool static_status = false;
  if (type == slLifetime_Automatic) {
    nodeId = fC->Sibling(nodeId);
    automatic_status = true;
    type = fC->Type(nodeId);
  }
  if (type == slLifetime_Static) {
    nodeId = fC->Sibling(nodeId);
    static_status = true;
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
        NodeId Expression = fC->Sibling(Var);

        assign_stmt* assign_stmt = s.MakeAssign_stmt();

        variables* var = (variables*)compileVariable(
            component, fC, Data_type, compileDesign, assign_stmt, nullptr, true);
        if (var) {
          var->VpiConstantVariable(static_status);
          var->VpiAutomatic(automatic_status);
        }
        assign_stmt->Lhs(var);
        if (var) {
          var->VpiParent(assign_stmt);
          var->VpiName(fC->SymName(Var));
        }
        if (Expression) {
          expr* rhs =
            (expr*)compileExpression(component, fC, Expression, compileDesign);
          if (rhs) rhs->VpiParent(assign_stmt);
          assign_stmt->Rhs(rhs);
        }
        if (results == nullptr) {
          results = s.MakeAnyVec();
        }
        results->push_back(assign_stmt);
        Variable_decl_assignment = fC->Sibling(Variable_decl_assignment);
      }
      break;
    }
    default:
      break;
  }
  return results;
}

UHDM::any* CompileHelper::compileImmediateAssertion(
  DesignComponent* component, const FileContent* fC, NodeId the_stmt,
  CompileDesign* compileDesign, UHDM::any* pstmt,
  SURELOG::ValuedComponentI *instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId Expression = fC->Child(the_stmt);
  NodeId Action_block = fC->Sibling(Expression);
  NodeId if_stmt_id = fC->Child(Action_block);
  NodeId else_stmt_id = fC->Sibling(if_stmt_id);
  UHDM::any* expr = compileExpression(component, fC, Expression, compileDesign, pstmt, instance, true);
  VectorOfany* if_stmts = compileStmt(component, fC, if_stmt_id, compileDesign, pstmt);
  UHDM::any* if_stmt  = nullptr;
  if (if_stmts)
    if_stmt = (*if_stmts)[0];
  VectorOfany* else_stmts = nullptr;
  if (else_stmt_id)
    else_stmts = compileStmt(component, fC, else_stmt_id, compileDesign, pstmt);
  UHDM::any* else_stmt = nullptr;
  if (else_stmts)
    else_stmt = (*else_stmts)[0];
  UHDM::any* stmt = nullptr;
  switch (fC->Type(the_stmt)) {
  case VObjectType::slSimple_immediate_assert_statement: {
    UHDM::immediate_assert* astmt = s.MakeImmediate_assert();
    astmt->VpiParent(pstmt);
    astmt->Expr((UHDM::expr*) expr);
    if (expr)
      expr->VpiParent(astmt);
    astmt->Stmt(if_stmt);
    if (if_stmt)
      if_stmt->VpiParent(astmt);
    astmt->Else_stmt(else_stmt);
    if (else_stmt)
      else_stmt->VpiParent(astmt);
    stmt = astmt;
    break;
  }
  case VObjectType::slSimple_immediate_assume_statement: {
    UHDM::immediate_assume* astmt = s.MakeImmediate_assume();
    astmt->VpiParent(pstmt);
    astmt->Expr((UHDM::expr*) expr);
    if (expr)
      expr->VpiParent(astmt);
    astmt->Stmt(if_stmt);
    if (if_stmt)
      if_stmt->VpiParent(astmt);
    astmt->Else_stmt(else_stmt);
    if (else_stmt)
      else_stmt->VpiParent(astmt);
    stmt = astmt;
    break;
  }
  case VObjectType::slSimple_immediate_cover_statement: {
    UHDM::immediate_cover* astmt = s.MakeImmediate_cover();
    astmt->VpiParent(pstmt);
    astmt->Expr((UHDM::expr*) expr);
    if (expr)
      expr->VpiParent(astmt);
    astmt->Stmt(if_stmt);
    if (if_stmt)
      if_stmt->VpiParent(astmt);
    stmt = astmt;
    break;
  }
  default:
    break;
  }

  /*
n<o> u<277> t<StringConst> p<278> l<25>
n<> u<278> t<Primary_literal> p<279> c<277> l<25>
n<> u<279> t<Primary> p<280> c<278> l<25>
n<> u<280> t<Expression> p<286> c<279> s<281> l<25>
n<> u<281> t<BinOp_Equiv> p<286> s<285> l<25>
n<0> u<282> t<IntConst> p<283> l<25>
n<> u<283> t<Primary_literal> p<284> c<282> l<25>
n<> u<284> t<Primary> p<285> c<283> l<25>
n<> u<285> t<Expression> p<286> c<284> l<25>
n<> u<286> t<Expression> p<289> c<280> s<288> l<25>
n<> u<287> t<Statement_or_null> p<288> l<25>
n<> u<288> t<Action_block> p<289> c<287> l<25>
n<> u<289> t<Simple_immediate_assert_statement> p<290> c<286> l<25>
*/
  return stmt;
}

UHDM::atomic_stmt* CompileHelper::compileConditionalStmt(
  DesignComponent* component, const FileContent* fC,
  NodeId Cond_predicate,
  CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* cond_exp = compileExpression(component, fC, Cond_predicate, compileDesign);
  NodeId If_branch_stmt = fC->Sibling(Cond_predicate);
  NodeId Else_branch_stmt = fC->Sibling(If_branch_stmt);
  UHDM::atomic_stmt* result_stmt = nullptr;
  if (Else_branch_stmt != 0) {
    UHDM::if_else* cond_stmt = s.MakeIf_else();
    cond_stmt->VpiCondition((UHDM::expr*) cond_exp);
    if (cond_exp)
      cond_exp->VpiParent(cond_stmt);
    VectorOfany* if_stmts = compileStmt(component, fC, If_branch_stmt, compileDesign, cond_stmt);
    UHDM::any* if_stmt  = nullptr;
    if (if_stmts)
      if_stmt = (*if_stmts)[0];
    cond_stmt->VpiStmt(if_stmt);
    if (if_stmt)
      if_stmt->VpiParent(cond_stmt);
    VectorOfany* else_stmts = compileStmt(component, fC, Else_branch_stmt, compileDesign, cond_stmt);
    UHDM::any* else_stmt = nullptr;
    if (else_stmts)
      else_stmt = (*else_stmts)[0];
    cond_stmt->VpiElseStmt(else_stmt);
    if (else_stmt)
      else_stmt->VpiParent(cond_stmt);
    result_stmt = cond_stmt;
  } else {
    UHDM::if_stmt* cond_stmt = s.MakeIf_stmt();
    cond_stmt->VpiCondition((UHDM::expr*) cond_exp);
    if (cond_exp)
      cond_exp->VpiParent(cond_stmt);
    VectorOfany* if_stmts = compileStmt(component, fC, If_branch_stmt, compileDesign, cond_stmt);
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
  NodeId Procedural_timing_control_statement,
  CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  /*
  n<#100> u<70> t<IntConst> p<71> l<7>
  n<> u<71> t<Delay_control> p<72> c<70> l<7>
  n<> u<72> t<Procedural_timing_control> p<88> c<71> s<87> l<7>
  */
  NodeId Procedural_timing_control = fC->Child(Procedural_timing_control_statement);
  NodeId Event_control = fC->Child(Procedural_timing_control);

  NodeId Event_expression = fC->Child(Event_control);
  UHDM::event_control* event = s.MakeEvent_control();
  UHDM::any* exp = compileExpression(component, fC, Event_expression, compileDesign);
  event->VpiCondition(exp);
  if (exp)
    exp->VpiParent(event);
  NodeId Statement_or_null = fC->Sibling(Procedural_timing_control);
  VectorOfany* stmts = compileStmt(component, fC, Statement_or_null, compileDesign, event);
  if (stmts) {
    any* stmt = (*stmts)[0];
    event->Stmt(stmt);
    stmt->VpiParent(event);
  }
  return event;
}

UHDM::atomic_stmt* CompileHelper::compileCaseStmt(
  DesignComponent* component, const FileContent* fC, NodeId nodeId,
  CompileDesign* compileDesign) {
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
  UHDM::any* cond_exp = compileExpression(component, fC, Condition, compileDesign);
  NodeId Case_item = fC->Sibling(Condition);
  UHDM::case_stmt* case_stmt = s.MakeCase_stmt();
  UHDM::VectorOfcase_item* case_items = s.MakeCase_itemVec();
  case_stmt->Case_items(case_items);
  result = case_stmt;
  case_stmt->VpiCondition((UHDM::expr*) cond_exp);
  if (cond_exp && !cond_exp->VpiParent())
    cond_exp->VpiParent(case_stmt);
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
            UHDM::any* item_exp = compileExpression(component, fC, Expression, compileDesign);
            if (item_exp && !item_exp->VpiParent()) {
              item_exp->VpiParent(case_item);
              exprs->push_back(item_exp);
            } else {
             // std::cout << "HERE\n";
            }
          } else {
            // Stmt
            VectorOfany* stmts = compileStmt(component, fC, Expression, compileDesign, case_item);
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
          if (item_exp && !item_exp->VpiParent()) {
            item_exp->VpiParent(case_item);
            exprs->push_back(item_exp);
          }
          Value_range = fC->Sibling(Value_range);
        }
        NodeId Statement_or_null = fC->Sibling(Open_range_list);
        // Stmt
        VectorOfany* stmts = compileStmt(component, fC, Statement_or_null, compileDesign,
                                case_item);
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
        VectorOfany* stmts = compileStmt(component, fC, Expression, compileDesign, case_item);
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


std::vector<io_decl*>* CompileHelper::compileTfPortDecl(
  DesignComponent* component, UHDM::task_func* parent,
  const FileContent* fC, NodeId tf_item_decl,
  CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<io_decl*>* ios = s.MakeIo_declVec();
  /*
n<> u<137> t<TfPortDir_Inp> p<141> s<138> l<28>
n<> u<138> t<Data_type_or_implicit> p<141> s<140> l<28>
n<req_1> u<139> t<StringConst> p<140> l<28>
n<> u<140> t<List_of_tf_variable_identifiers> p<141> c<139> l<28>
n<> u<141> t<Tf_port_declaration> p<142> c<137> l<28>
n<> u<142> t<Tf_item_declaration> p<386> c<141> s<384> l<28>
  */
  while  (tf_item_decl) {
    if (fC->Type(tf_item_decl) == VObjectType::slTf_item_declaration) {
      NodeId Tf_port_declaration = fC->Child(tf_item_decl);
      NodeId TfPortDir = fC->Child(Tf_port_declaration);
      VObjectType tf_port_direction_type = fC->Type(TfPortDir);
      NodeId Data_type_or_implicit = fC->Sibling(TfPortDir);
      NodeId Packed_dimension = fC->Child(Data_type_or_implicit);
      int size;
      VectorOfrange* ranges = compileRanges(component, fC, Packed_dimension,
                                       compileDesign,
                                       nullptr, nullptr, true, size);

      NodeId List_of_tf_variable_identifiers =
          fC->Sibling(Data_type_or_implicit);
      while (List_of_tf_variable_identifiers) {
        io_decl* decl = s.MakeIo_decl();
        ios->push_back(decl);
        decl->VpiParent(parent);
        decl->VpiDirection(UhdmWriter::getVpiDirection(tf_port_direction_type));
        NodeId nameId = fC->Child(List_of_tf_variable_identifiers);
        decl->VpiName(fC->SymName(nameId));
        decl->VpiFile(fC->getFileName());
        decl->VpiLineNo(fC->Line(nameId));
        decl->Ranges(ranges);
        List_of_tf_variable_identifiers =
            fC->Sibling(List_of_tf_variable_identifiers);
      }
    }
    tf_item_decl = fC->Sibling(tf_item_decl);
  }
  return ios;
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
    while (tf_port_item) {
      io_decl* decl = s.MakeIo_decl();
      ios->push_back(decl);
      NodeId tf_data_type_or_implicit = fC->Child(tf_port_item);
      NodeId tf_data_type = fC->Child(tf_data_type_or_implicit);
      VObjectType tf_port_direction_type = fC->Type(tf_data_type_or_implicit);
      decl->VpiDirection(UhdmWriter::getVpiDirection(tf_port_direction_type));
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
      any* var = compileVariable(component, fC, type, compileDesign, nullptr, nullptr, true);
      decl->Expr(var);
      if (var)
        var->VpiParent(decl);
      std::string name = fC->SymName(tf_param_name);
      decl->VpiName(name);
      NodeId expression = fC->Sibling(tf_param_name);

      if (expression &&
          (fC->Type(expression) != VObjectType::slVariable_dimension) &&
          (fC->Type(type) != VObjectType::slStringConst)) {
        //value = m_exprBuilder.evalExpr(fC, expression, parent->getParent());
      }

      tf_port_item = fC->Sibling(tf_port_item);
    }
  }

  return ios;
}

bool CompileHelper::compileTask(
  DesignComponent* component, const FileContent* fC, NodeId nodeId,
  CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::task_func*>* task_funcs = component->getTask_funcs();
  if (task_funcs == nullptr) {
    component->setTask_funcs(s.MakeTask_funcVec());
    task_funcs = component->getTask_funcs();
  }
  UHDM::task* task = s.MakeTask();
  task->VpiFile(fC->getFileName());
  task->VpiLineNo(fC->Line(nodeId));
  task_funcs->push_back(task);
  NodeId Task_body_declaration = fC->Child(nodeId);
  NodeId task_name = fC->Child(Task_body_declaration);
  std::string name;
  if (fC->Type(task_name) == VObjectType::slStringConst)
    name = fC->SymName(task_name);
  else if (fC->Type(task_name) == VObjectType::slClass_scope) {
    NodeId Class_type = fC->Child(task_name);
    name = fC->SymName(fC->Child(Class_type));
    name += "::" + fC->SymName(fC->Sibling(task_name));
    task_name = fC->Sibling(task_name);
  }
  task->VpiName(name);
  NodeId Statement_or_null = fC->Sibling(task_name);
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
      if (VectorOfany* sts = compileStmt(component, fC, Statement_or_null, compileDesign, begin)) {
        for (any* st : *sts) {
          stmts->push_back(st);
          st->VpiParent(begin);
        }
      }
      Statement_or_null = fC->Sibling(Statement_or_null);
    }
  } else {
    // Page 983, 2017 Standard: 0 or 1 Stmt
    VectorOfany* stmts = compileStmt(component, fC, Statement_or_null, compileDesign, task);
    if (stmts) {
      for (any* stmt : *stmts) {
        task->Stmt(stmt);
        stmt->VpiParent(task);
      }
    }
  }
  return true;
}

bool CompileHelper::compileFunction(
  DesignComponent* component, const FileContent* fC,
  NodeId nodeId,
  CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::task_func*>* task_funcs = component->getTask_funcs();
  if (task_funcs == nullptr) {
    component->setTask_funcs(s.MakeTask_funcVec());
    task_funcs = component->getTask_funcs();
  }
  UHDM::function* func = s.MakeFunction();
  task_funcs->push_back(func);
  func->VpiFile(fC->getFileName());
  func->VpiLineNo(fC->Line(nodeId));
  NodeId Function_body_declaration = fC->Child(nodeId);
  if (fC->Type(Function_body_declaration) == VObjectType::slLifetime_Automatic) {
    Function_body_declaration = fC->Sibling(Function_body_declaration);
    func->VpiAutomatic(true);
  } else if (fC->Type(Function_body_declaration) == VObjectType::slMethodQualifier_Virtual) {
    Function_body_declaration = fC->Sibling(Function_body_declaration);
    func->VpiVirtual(true);
  }
  NodeId Function_data_type_or_implicit = fC->Child(Function_body_declaration);
  NodeId Function_data_type = fC->Child(Function_data_type_or_implicit);
  NodeId Return_data_type = fC->Child(Function_data_type);
  func->Return(dynamic_cast<variables*>(
      compileVariable(component, fC, Return_data_type, compileDesign, nullptr, nullptr, true)));
  NodeId Function_name = fC->Sibling(Function_data_type_or_implicit);
  std::string name;
   NodeId Tf_port_list = 0;
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
  func->VpiName(name);

  NodeId Function_statement_or_null = Tf_port_list;
  if (fC->Type(Tf_port_list) == VObjectType::slTf_port_list) {
    func->Io_decls(compileTfPortList(component, func, fC, Tf_port_list, compileDesign));
    Function_statement_or_null = fC->Sibling(Tf_port_list);
  } else if (fC->Type(Tf_port_list) == VObjectType::slTf_item_declaration) {
    func->Io_decls(compileTfPortDecl(component, func, fC, Tf_port_list, compileDesign));
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
            stmts->push_back(st);
            st->VpiParent(begin);
          }
        }
      }
      Function_statement_or_null = fC->Sibling(Function_statement_or_null);
    }
  } else {
    // Page 983, 2017 Standard: 0 or 1 Stmt
    NodeId Statement = fC->Child(Function_statement_or_null);
    VectorOfany* sts = compileStmt(component, fC, Statement, compileDesign, func);
    if (sts) {
      any* st = (*sts)[0];
      st->VpiParent(func);
      func->Stmt(st);
    }
  }
  return true;
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
  NodeId For_initialization = fC->Sibling(nodeId);
  NodeId Condition = fC->Sibling(For_initialization);
  NodeId For_step = fC->Sibling(Condition);
  NodeId Statement_or_null = fC->Sibling(For_step);

  // Init
  NodeId For_variable_declaration = fC->Child(For_initialization);
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
        (variables*)compileVariable(component, fC, Data_type, compileDesign, assign_stmt, nullptr, true);
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

  // Condition
  expr* cond = (expr*) compileExpression(component, fC, Condition, compileDesign);
  if (cond)
    cond->VpiParent(for_stmt);
  for_stmt->VpiCondition(cond);

  // Increment
  NodeId For_step_assignment = fC->Child(For_step);
  while (For_step_assignment) {
    VectorOfany* stmts = for_stmt->VpiForIncStmts();
    if (stmts == nullptr) {
      for_stmt->VpiForIncStmts(s.MakeAnyVec());
      stmts = for_stmt->VpiForIncStmts();
    }

    NodeId Expression = fC->Child(For_step_assignment);
    expr* exp = (expr*) compileExpression(component, fC, Expression, compileDesign);
    if (exp) {
      exp->VpiParent(for_stmt);
      stmts->push_back(exp);
    }
    For_step_assignment = fC->Sibling(For_step_assignment);
  }

  // Stmt
  VectorOfany* stmts = compileStmt(component, fC, Statement_or_null, compileDesign, for_stmt);
  if (stmts)
    for_stmt->VpiStmt((*stmts)[0]);

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
