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

UHDM::any* CompileHelper::compileStmt(PortNetHolder* component, FileContent* fC, NodeId the_stmt, 
        CompileDesign* compileDesign, UHDM::any* pstmt) {
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
    return compileStmt(component, fC, child, compileDesign);
  }
  case VObjectType::slStatement:
  case VObjectType::slStatement_item:
  case VObjectType::slImmediate_assertion_statement:
  case VObjectType::slProcedural_assertion_statement:
  case VObjectType::slLoop_statement: {
	  return compileStmt(component, fC, fC->Child(the_stmt), compileDesign);
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
	    UHDM::any* cstmt = compileStmt(component, fC, item, compileDesign);
	    if (cstmt)
	      stmts->push_back(cstmt);
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
      stmt = fork;
      fork->VpiName(fC->SymName(item));
      item = fC->Sibling(item);	
    } else {
      UHDM::fork_stmt* fork = s.MakeFork_stmt();
      fork->Stmts(stmts);
      stmt = fork;
    }
	  while (item) {
	    UHDM::any* cstmt = compileStmt(component, fC, item, compileDesign);
	    if (cstmt)
	      stmts->push_back(cstmt);
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
  case VObjectType::slForever_keyword: {
    UHDM::forever* forever = s.MakeForever();
    NodeId item = fC->Sibling(the_stmt);
    forever->VpiStmt(compileStmt(component, fC, item, compileDesign));
    stmt = forever;
    break;
  }
  case VObjectType::slRepeat_keyword: {
    NodeId cond = fC->Sibling(the_stmt);
    UHDM::any* cond_exp = compileExpression(component, fC, cond, compileDesign);
    NodeId rstmt = fC->Sibling(cond);
    UHDM::repeat* repeat = s.MakeRepeat();
    repeat->VpiCondition((UHDM::expr*) cond_exp);
    UHDM::any* repeat_stmt = compileStmt(component, fC, rstmt, compileDesign);
    repeat->VpiStmt(repeat_stmt);
    stmt = repeat;
    break;
  }
  case VObjectType::slWhile_keyword: {
    NodeId cond = fC->Sibling(the_stmt);
    UHDM::any* cond_exp = compileExpression(component, fC, cond, compileDesign);
    NodeId rstmt = fC->Sibling(cond);
    UHDM::while_stmt* while_st = s.MakeWhile_stmt();
    while_st->VpiCondition((UHDM::expr*) cond_exp);
    UHDM::any* while_stmt = compileStmt(component, fC, rstmt, compileDesign);
    while_st->VpiStmt(while_stmt);
    stmt = while_st;
    break;
  }
  case VObjectType::slSimple_immediate_assertion_statement: {
    stmt = compileImmediateAssertion(component, fC, fC->Child(the_stmt), compileDesign);
    break;
  }
  default:
    break;
  }
  if (stmt) {
    stmt->VpiFile(fC->getFileName(the_stmt));
    stmt->VpiLineNo(fC->Line(the_stmt));
  } else {
    /*
    VObjectType stmttype = fC->Type(the_stmt);
    if ((stmttype != VObjectType::slEnd) && (stmttype != VObjectType::slJoin_keyword) && (stmttype != VObjectType::slJoin_any_keyword)
     && (stmttype != VObjectType::slJoin_none_keyword)) {
      std::cout << "UNSUPPORTED STATEMENT: " << fC->getFileName(the_stmt) << ":" << fC->Line(the_stmt) << ":" << std::endl;
      std::cout << " -> " << fC->printObject(the_stmt) << std::endl;
    }
    */
  }
  return stmt;
}

UHDM::any* CompileHelper::compileImmediateAssertion(PortNetHolder* component, FileContent* fC, NodeId the_stmt, 
        CompileDesign* compileDesign, UHDM::any* pstmt) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId Expression = fC->Child(the_stmt);
  NodeId Action_block = fC->Sibling(Expression);
  NodeId if_stmt_id = fC->Child(Action_block);
  NodeId else_stmt_id = fC->Sibling(if_stmt_id);
  UHDM::any* expr = compileExpression(component, fC, Expression, compileDesign);
  UHDM::any* if_stmt = compileStmt(component, fC, if_stmt_id, compileDesign);
  UHDM::any* else_stmt = compileStmt(component, fC, else_stmt_id, compileDesign);
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

UHDM::atomic_stmt* CompileHelper::compileConditionalStmt(PortNetHolder* component, FileContent* fC, 
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
    UHDM::any* if_stmt = compileStmt(component, fC, If_branch_stmt, compileDesign);
    cond_stmt->VpiStmt(if_stmt);
    UHDM::any* else_stmt = compileStmt(component, fC, Else_branch_stmt, compileDesign);
    cond_stmt->VpiElseStmt(else_stmt);
    result_stmt = cond_stmt;
  } else {
    UHDM::if_stmt* cond_stmt = s.MakeIf_stmt();
    cond_stmt->VpiCondition((UHDM::expr*) cond_exp);
    UHDM::any* if_stmt = compileStmt(component, fC, If_branch_stmt, compileDesign);
    cond_stmt->VpiStmt(if_stmt);
    result_stmt = cond_stmt;
  }
  return result_stmt;
}


UHDM::atomic_stmt* CompileHelper::compileEventControlStmt(PortNetHolder* component, FileContent* fC, 
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
  NodeId Statement_or_null = fC->Sibling(Procedural_timing_control);
  event->Stmt(compileStmt(component, fC, Statement_or_null, compileDesign));
  return event;
}

UHDM::atomic_stmt* CompileHelper::compileCaseStmt(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
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
            UHDM::any* item_exp = compileExpression(component, fC, Expression, compileDesign);
            if (item_exp) {              
              exprs->push_back(item_exp);
            } else {
             // std::cout << "HERE\n";
            }  
          } else {
            // Stmt
            case_item->Stmt(compileStmt(component, fC, Expression, compileDesign));
          }
          Expression = fC->Sibling(Expression);
        }
      } else {
        // Default
        case_item->Stmt(compileStmt(component, fC, Expression, compileDesign));
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
  task->Stmt(compileStmt(component, fC, Statement_or_null, compileDesign));
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