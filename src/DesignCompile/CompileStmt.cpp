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
  case VObjectType::slJump_statement:
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
	    if (cstmt) {
	      stmts->push_back(cstmt);
        cstmt->VpiParent(stmt);
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
	    if (cstmt) {
	      stmts->push_back(cstmt);
        cstmt->VpiParent(stmt);
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
  case VObjectType::slForever_keyword: {
    UHDM::forever_stmt* forever = s.MakeForever_stmt();
    NodeId item = fC->Sibling(the_stmt);
    any* stmt = compileStmt(component, fC, item, compileDesign);
    if (stmt)
      stmt->VpiParent(forever);
    forever->VpiStmt(stmt);
    stmt = forever;
    break;
  }
  case VObjectType::slRepeat_keyword: {
    NodeId cond = fC->Sibling(the_stmt);
    UHDM::any* cond_exp = compileExpression(component, fC, cond, compileDesign);
    NodeId rstmt = fC->Sibling(cond);
    UHDM::repeat* repeat = s.MakeRepeat();
    repeat->VpiCondition((UHDM::expr*) cond_exp);
    if (cond_exp)
      cond_exp->VpiParent(repeat);
    UHDM::any* repeat_stmt = compileStmt(component, fC, rstmt, compileDesign);
    repeat->VpiStmt(repeat_stmt);
    if (repeat_stmt)
      repeat_stmt->VpiParent(repeat);
    stmt = repeat;
    break;
  }
  case VObjectType::slWhile_keyword: {
    NodeId cond = fC->Sibling(the_stmt);
    UHDM::any* cond_exp = compileExpression(component, fC, cond, compileDesign);
    NodeId rstmt = fC->Sibling(cond);
    UHDM::while_stmt* while_st = s.MakeWhile_stmt();
    while_st->VpiCondition((UHDM::expr*) cond_exp);
    if (cond_exp)
      cond_exp->VpiParent(while_st);
    UHDM::any* while_stmt = compileStmt(component, fC, rstmt, compileDesign);
    while_st->VpiStmt(while_stmt);
    if (while_stmt)
      while_stmt->VpiParent(while_st);
    stmt = while_st;
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
    stmt = compileImmediateAssertion(component, fC, fC->Child(the_stmt), compileDesign);
    break;
  }
  default:
    break;
  }
  if (stmt) {
    stmt->VpiFile(fC->getFileName(the_stmt));
    stmt->VpiLineNo(fC->Line(the_stmt));
    stmt->VpiParent(pstmt);
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
    if (cond_exp)
      cond_exp->VpiParent(cond_stmt);
    UHDM::any* if_stmt = compileStmt(component, fC, If_branch_stmt, compileDesign);
    cond_stmt->VpiStmt(if_stmt);
    if (if_stmt)
      if_stmt->VpiParent(cond_stmt);
    UHDM::any* else_stmt = compileStmt(component, fC, Else_branch_stmt, compileDesign);
    cond_stmt->VpiElseStmt(else_stmt);
    if (else_stmt)
      else_stmt->VpiParent(cond_stmt);
    result_stmt = cond_stmt;
  } else {
    UHDM::if_stmt* cond_stmt = s.MakeIf_stmt();
    cond_stmt->VpiCondition((UHDM::expr*) cond_exp);
    if (cond_exp)
      cond_exp->VpiParent(cond_stmt);
    UHDM::any* if_stmt = compileStmt(component, fC, If_branch_stmt, compileDesign);
    cond_stmt->VpiStmt(if_stmt);
    if (if_stmt)
      if_stmt->VpiParent(cond_stmt);
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
  if (exp)
    exp->VpiParent(event);
  NodeId Statement_or_null = fC->Sibling(Procedural_timing_control);
  any* stmt = compileStmt(component, fC, Statement_or_null, compileDesign);
  event->Stmt(stmt);
  if (stmt)
    stmt->VpiParent(event);
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
  if (cond_exp)
    cond_exp->VpiParent(case_stmt);
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
      case_item->VpiFile(fC->getFileName());
      case_item->VpiLineNo(fC->Line(Case_item));
      case_item->VpiParent(case_stmt);
      NodeId Expression = fC->Child(Case_item);
      if (fC->Type(Expression) == VObjectType::slExpression) {
        VectorOfany* exprs = s.MakeAnyVec();
        case_item->VpiExprs(exprs);
        while (Expression) {
          if (fC->Type(Expression) == VObjectType::slExpression) {
            // Expr
            UHDM::any* item_exp = compileExpression(component, fC, Expression, compileDesign);
            if (item_exp) {
              item_exp->VpiParent(case_item);              
              exprs->push_back(item_exp);
            } else {
             // std::cout << "HERE\n";
            }  
          } else {
            // Stmt
            any* stmt = compileStmt(component, fC, Expression, compileDesign);
            if (stmt)
              stmt->VpiParent(case_item);
            case_item->Stmt(stmt);
          }
          Expression = fC->Sibling(Expression);
        }
      } else {
        // Default
        any* stmt = compileStmt(component, fC, Expression, compileDesign);
        if (stmt)
          stmt->VpiParent(case_item);
        case_item->Stmt(stmt);
      }
    }
    Case_item = fC->Sibling(Case_item);
  }

  return result;
}


std::vector<io_decl*>* CompileHelper::compileTfPortDecl(UHDM::task_func* parent, FileContent* fC, NodeId tf_item_decl,
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
      VectorOfrange* ranges = compileRanges(nullptr, fC, Packed_dimension, 
                                       compileDesign,
                                       nullptr, nullptr);

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

std::vector<io_decl*>* CompileHelper::compileTfPortList(UHDM::task_func* parent, FileContent* fC, NodeId tf_port_list,
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
      any* var = compileVariable(fC, type, compileDesign);
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

bool CompileHelper::compileTask(PortNetHolder* component, FileContent* fC, NodeId nodeId, 
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
  task->VpiName(fC->SymName(task_name));
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
      if (any* st = compileStmt(component, fC, Statement_or_null, compileDesign)) {
        stmts->push_back(st);
        st->VpiParent(begin);
      }
      Statement_or_null = fC->Sibling(Statement_or_null); 
    }
  } else {
    // Page 983, 2017 Standard: 0 or 1 Stmt
    any* stmt = compileStmt(component, fC, Statement_or_null, compileDesign);
    task->Stmt(stmt);
    if (stmt)
      stmt->VpiParent(task);
  }
  return true;
}

bool CompileHelper::compileFunction(PortNetHolder* component, FileContent* fC,
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
      compileVariable(fC, Return_data_type, compileDesign)));
  NodeId Function_name = fC->Sibling(Function_data_type_or_implicit);
  const std::string& name = fC->SymName(Function_name);
  func->VpiName(name);

  NodeId Tf_port_list = fC->Sibling(Function_name);
  NodeId Function_statement_or_null = Tf_port_list;
  if (fC->Type(Tf_port_list) == VObjectType::slTf_port_list) {
    func->Io_decls(compileTfPortList(func, fC, Tf_port_list, compileDesign));
    Function_statement_or_null = fC->Sibling(Tf_port_list);
  } else if (fC->Type(Tf_port_list) == VObjectType::slTf_item_declaration) {
    func->Io_decls(compileTfPortDecl(func, fC, Tf_port_list, compileDesign));
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
      if (any* st = compileStmt(component, fC, Statement, compileDesign)) {
        stmts->push_back(st);
        st->VpiParent(begin);
      }
      Function_statement_or_null = fC->Sibling(Function_statement_or_null); 
    }
  } else {
    // Page 983, 2017 Standard: 0 or 1 Stmt
    NodeId Statement = fC->Child(Function_statement_or_null);
    any* st = compileStmt(component, fC, Statement, compileDesign);
    if (st) {
      st->VpiParent(func);
      func->Stmt(st);
    }
  }
  return true;
}