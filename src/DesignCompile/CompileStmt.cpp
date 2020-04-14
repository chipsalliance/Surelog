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

UHDM::any* CompileHelper::compileStmt(FileContent* fC, NodeId the_stmt, 
        CompileDesign* compileDesign, UHDM::any* pstmt) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  VObjectType type = fC->Type(the_stmt);
  UHDM::any* stmt = nullptr;
  switch (type) {
  case VObjectType::slStatement_or_null:
  case VObjectType::slStatement:
  case VObjectType::slStatement_item:
  case VObjectType::slImmediate_assertion_statement:
  case VObjectType::slProcedural_assertion_statement: {
	  return compileStmt(fC, fC->Child(the_stmt), compileDesign);
  }
  case VObjectType::slProcedural_timing_control_statement:{
    UHDM::atomic_stmt* dc = compileProceduralTimingControlStmt(fC, the_stmt, compileDesign);
    stmt = dc;        
    break;
  }
  case VObjectType::slNonblocking_assignment: {
    NodeId Operator_assignment  = the_stmt;
    UHDM::assignment* assign = compileBlockingAssignment(fC, 
                Operator_assignment, false, compileDesign);
    stmt = assign; 
    break; 
  }
  case VObjectType::slBlocking_assignment: {
    NodeId Operator_assignment = fC->Child(the_stmt);
    UHDM::assignment* assign = compileBlockingAssignment(fC, 
                Operator_assignment, true, compileDesign);
    stmt = assign;    
    break;
  }
  case VObjectType::slSubroutine_call_statement: {
	  NodeId Subroutine_call = fC->Child(the_stmt);
    UHDM::tf_call* call = compileTfCall(fC, Subroutine_call ,compileDesign);
	  stmt = call;
  	break;
  }
  case VObjectType::slSystem_task: {
    UHDM::tf_call* call = compileTfCall(fC, the_stmt, compileDesign); 
    stmt = call;
    break;
  }
  case VObjectType::slConditional_statement: {
	  NodeId Conditional_statement = the_stmt;  
	  UHDM::atomic_stmt* cstmt = compileConditionalStmt(fC, 
                                   Conditional_statement, compileDesign);
  	stmt = cstmt;
  	break;
  }
  case VObjectType::slCase_statement: {
    NodeId Case_statement = the_stmt;  
	  UHDM::atomic_stmt* cstmt = compileCaseStmt(fC, 
                                   Case_statement, compileDesign);
  	stmt = cstmt;
    break;
  }
  case VObjectType::slSeq_block: {
	  NodeId item = fC->Child(the_stmt);
	  UHDM::begin* begin = s.MakeBegin();
	  VectorOfany* stmts = s.MakeAnyVec();
    if (fC->Type(item) == VObjectType::slStringConst) {
      begin->VpiName(fC->SymName(item));
      item = fC->Sibling(item);	
    }
	  while (item) {
	    UHDM::any* cstmt = compileStmt(fC, item, compileDesign);
	    if (cstmt)
	      stmts->push_back(cstmt);
	    item = fC->Sibling(item);	
  	}
	  begin->Stmts(stmts);
	  stmt = begin;
	  break;
  }
  case VObjectType::slSimple_immediate_assertion_statement: {
    stmt = compileImmediateAssertion(fC, fC->Child(the_stmt), compileDesign);
    break;
  }
  default:
    break;
  }
  return stmt;
}

UHDM::any* CompileHelper::compileImmediateAssertion(FileContent* fC, NodeId the_stmt, 
        CompileDesign* compileDesign, UHDM::any* pstmt) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId Expression = fC->Child(the_stmt);
  NodeId Action_block = fC->Sibling(Expression);
  NodeId if_stmt_id = fC->Child(Action_block);
  NodeId else_stmt_id = fC->Sibling(if_stmt_id);
  UHDM::any* expr = compileExpression(fC, Expression, compileDesign);
  UHDM::any* if_stmt = compileStmt(fC, if_stmt_id, compileDesign);
  UHDM::any* else_stmt = compileStmt(fC, else_stmt_id, compileDesign);
  UHDM::any* stmt = nullptr;
  switch (fC->Type(the_stmt)) {
  case VObjectType::slSimple_immediate_assert_statement: {
    UHDM::immediate_assert* astmt = s.MakeImmediate_assert();
    astmt->Expr((UHDM::expr*) expr);
    astmt->Stmt(if_stmt);
    astmt->Else_stmt(else_stmt);
    stmt = astmt;
    break;
  }
  case VObjectType::slSimple_immediate_assume_statement: {
    UHDM::immediate_assume* astmt = s.MakeImmediate_assume();
    astmt->Expr((UHDM::expr*) expr);
    astmt->Stmt(if_stmt);
    astmt->Else_stmt(else_stmt);
    stmt = astmt;
    break;
  }
  case VObjectType::slSimple_immediate_cover_statement: {
    UHDM::immediate_cover* astmt = s.MakeImmediate_cover();
    astmt->Expr((UHDM::expr*) expr);
    astmt->Stmt(if_stmt);
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

UHDM::atomic_stmt* CompileHelper::compileConditionalStmt(FileContent* fC, 
        NodeId Conditional_statement, 
        CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer(); 
  NodeId Cond_predicate = fC->Child(Conditional_statement);
  UHDM::any* cond_exp = compileExpression(fC, Cond_predicate, compileDesign);
  NodeId If_branch_stmt = fC->Sibling(Cond_predicate);
  NodeId Else_branch_stmt = fC->Sibling(If_branch_stmt);
  UHDM::atomic_stmt* result_stmt = nullptr;
  if (Else_branch_stmt != 0) {
    UHDM::if_else* cond_stmt = s.MakeIf_else();
    cond_stmt->VpiCondition((UHDM::expr*) cond_exp);
    UHDM::any* if_stmt = compileStmt(fC, If_branch_stmt, compileDesign);
    cond_stmt->VpiStmt(if_stmt);
    UHDM::any* else_stmt = compileStmt(fC, Else_branch_stmt, compileDesign);
    cond_stmt->VpiElseStmt(else_stmt);
    result_stmt = cond_stmt;
  } else {
    UHDM::if_stmt* cond_stmt = s.MakeIf_stmt();
    cond_stmt->VpiCondition((UHDM::expr*) cond_exp);
    UHDM::any* if_stmt = compileStmt(fC, If_branch_stmt, compileDesign);
    cond_stmt->VpiStmt(if_stmt);
    result_stmt = cond_stmt;
  }
  return result_stmt;
}


UHDM::atomic_stmt* CompileHelper::compileEventControlStmt(FileContent* fC, 
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
  UHDM::any* exp = compileExpression(fC, Event_expression, compileDesign);
  event->VpiCondition(exp);
  NodeId Statement_or_null = fC->Sibling(Procedural_timing_control);
  event->Stmt(compileStmt(fC, Statement_or_null, compileDesign));
  return event;
}

UHDM::atomic_stmt* CompileHelper::compileCaseStmt(FileContent* fC, NodeId nodeId, 
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
  UHDM::any* cond_exp = compileExpression(fC, Condition, compileDesign);
  NodeId Case_item = fC->Sibling(Condition);
  UHDM::case_stmt* case_stmt = s.MakeCase_stmt();
  UHDM::VectorOfcase_item* case_items = s.MakeCase_itemVec();
  case_stmt->Case_items(case_items);
  result = case_stmt;
  case_stmt->VpiCondition((UHDM::expr*) cond_exp);
  VObjectType CaseType = fC->Type(Case_type);
  switch (CaseType) {
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
    if (fC->Type(Case_item) == VObjectType::slCase_item) {
      UHDM::case_item* case_item = s.MakeCase_item();
      case_items->push_back(case_item);
      NodeId Expression = fC->Child(Case_item);
      if (fC->Type(Expression) == VObjectType::slExpression) {
        VectorOfany* exprs = s.MakeAnyVec();
        case_item->VpiExprs(exprs);
        while (Expression) {
          if (fC->Type(Expression) == VObjectType::slExpression) {
            // Expr
            UHDM::any* item_exp = compileExpression(fC, Expression, compileDesign);
            if (item_exp) {              
              exprs->push_back(item_exp);
            } else {
             // std::cout << "HERE\n";
            }  
          } else {
            // Stmt
            case_item->Stmt(compileStmt(fC, Expression, compileDesign));
          }
          Expression = fC->Sibling(Expression);
        }
      } else {
        // Default
        case_item->Stmt(compileStmt(fC, Expression, compileDesign));
      }
    }
    Case_item = fC->Sibling(Case_item);
  }

  return result;
}

bool CompileHelper::compileTask(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::task_func*>* task_funcs = component->getTask_funcs();
  if (task_funcs == nullptr) {
    component->setTask_funcs(s.MakeTask_funcVec());
    task_funcs = component->getTask_funcs();
  }
  UHDM::task* task = s.MakeTask();
  task_funcs->push_back(task);
  NodeId Task_body_declaration = fC->Child(nodeId);
  NodeId task_name = fC->Child(Task_body_declaration);
  task->VpiName(fC->SymName(task_name));
  NodeId Statement_or_null = fC->Sibling(task_name);
  task->Stmt(compileStmt(fC, Statement_or_null, compileDesign));
  return true;
}

  bool CompileHelper::compileFunction(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
        CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::task_func*>* task_funcs = component->getTask_funcs();
  if (task_funcs == nullptr) {
    component->setTask_funcs(s.MakeTask_funcVec());
    task_funcs = component->getTask_funcs();
  }
  return true;
}