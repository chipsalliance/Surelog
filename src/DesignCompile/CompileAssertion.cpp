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
#include "Expression/Value.h"
#include "Expression/ExprBuilder.h"
#include "Design/Enum.h"
#include "Design/Struct.h"
#include "Design/Union.h"
#include "Design/SimpleType.h"
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
#include "Utils/FileUtils.h"
#include "Utils/StringUtils.h"
#include "uhdm.h"
#include "clone_tree.h"
#include "ElaboratorListener.h"
#include "expr.h"
#include "UhdmWriter.h"

using namespace SURELOG;
using namespace UHDM;

bool CompileHelper::compileAssertionItem(DesignComponent* component, const FileContent* fC, NodeId nodeId,
        CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();        
  NodeId item = fC->Child(nodeId);
  if (fC->Type(item) == slConcurrent_assertion_item) {
    NodeId Concurrent_assertion_statement = fC->Child(item);
    VectorOfany* stmts = compileStmt(component, fC, Concurrent_assertion_statement, compileDesign, nullptr); 
    VectorOfany* assertions = component->getAssertions();
    if (assertions == nullptr) {
      component->setAssertions(s.MakeAnyVec());
      assertions = component->getAssertions();
    }
    if (stmts) {
      for (auto stmt : *stmts) {
        assertions->push_back(stmt);
      }
    }
  } /*else if (fC->Type(item) == slDeferred_immediate_assertion_item) {
    //16.4.3 Deferred assertions outside procedural code (IEEE_Std1800-2017)
    // TODO :
    //    module m (input a, b);
    //      a1: assert #0 (a == b);
    //    endmodule
    //  This is equivalent to the following:
    //    module m (input a, b);
    //      always_comb begina1: assert #0 (a == b);
    //      end
    //    endmodule
  }*/
  return true;
}

UHDM::property_inst* createPropertyInst(any* property_expr, UHDM::Serializer& s) {
  UHDM::property_inst* inst = (UHDM::property_inst*) property_expr;
  if (property_expr->UhdmType() == uhdmfunc_call) {
    func_call* call = (func_call*)property_expr;
    UHDM::property_inst* real_property_expr = s.MakeProperty_inst();
    real_property_expr->VpiArguments(call->Tf_call_args());
    real_property_expr->VpiName(call->VpiName());
    real_property_expr->VpiFile(call->VpiFile());
    real_property_expr->VpiLineNo(call->VpiLineNo());
    real_property_expr->VpiColumnNo(call->VpiColumnNo());
    inst = real_property_expr;
  }
  return inst;
}

UHDM::any* CompileHelper::compileConcurrentAssertion(
  DesignComponent* component, const FileContent* fC, NodeId the_stmt,
  CompileDesign* compileDesign, UHDM::any* pstmt,
  SURELOG::ValuedComponentI *instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId Property_spec = fC->Child(the_stmt);

  NodeId Action_block = fC->Sibling(Property_spec);
  UHDM::any* if_stmt = nullptr;
  UHDM::any* else_stmt = nullptr;
  if (fC->Type(Action_block) == slAction_block) {
    NodeId if_stmt_id = fC->Child(Action_block);
    NodeId else_stmt_id = 0;
    if (fC->Type(if_stmt_id) == slElse) {
      else_stmt_id = fC->Sibling(if_stmt_id);
      if_stmt_id = 0;
    } else {
      NodeId else_keyword = fC->Sibling(if_stmt_id);
      if (else_keyword) else_stmt_id = fC->Sibling(else_keyword);
    }
    VectorOfany* if_stmts = nullptr;
    if (if_stmt_id)
      if_stmts = compileStmt(component, fC, if_stmt_id, compileDesign, pstmt);
    if (if_stmts) 
      if_stmt = (*if_stmts)[0];
    VectorOfany* else_stmts = nullptr;
    if (else_stmt_id)
      else_stmts =
          compileStmt(component, fC, else_stmt_id, compileDesign, pstmt);
    if (else_stmts) 
      else_stmt = (*else_stmts)[0];
  }

  UHDM::any* stmt = nullptr;
  switch (fC->Type(the_stmt)) {
  case VObjectType::slAssert_property_statement: {
    NodeId Property_expr = fC->Child(Property_spec);
    UHDM::assert_stmt* assert_stmt = s.MakeAssert_stmt();
    UHDM::property_spec* prop_spec = s.MakeProperty_spec();
    UHDM::any* property_expr = compileExpression(component, fC, Property_expr, compileDesign, pstmt, instance, false);
    property_expr = createPropertyInst(property_expr, s);
    prop_spec->VpiPropertyExpr(property_expr);
    assert_stmt->VpiProperty(prop_spec);
    assert_stmt->Stmt(if_stmt);
    assert_stmt->Else_stmt(else_stmt);
    stmt = assert_stmt;
    break;
  }
  case VObjectType::slAssume_property_statement: {
    NodeId Property_expr = fC->Child(Property_spec);
    UHDM::expr* clocking_event = nullptr;
    if (fC->Type(Property_expr) == slClocking_event) {
      clocking_event = (UHDM::expr*) compileExpression(component, fC, Property_expr, compileDesign, pstmt, instance, false);
      Property_expr = fC->Sibling(Property_expr);
    }
    UHDM::assume* assume_stmt = s.MakeAssume();
    UHDM::property_spec* prop_spec = s.MakeProperty_spec();
    UHDM::any* property_expr = compileExpression(component, fC, Property_expr, compileDesign, pstmt, instance, false);
    property_expr = createPropertyInst(property_expr, s);
    prop_spec->VpiClockingEvent(clocking_event);
    prop_spec->VpiPropertyExpr(property_expr);
    assume_stmt->VpiProperty(prop_spec);
    assume_stmt->Stmt(if_stmt);
    stmt = assume_stmt;
    break;
  }
  case VObjectType::slCover_property_statement: {
    NodeId Property_expr = fC->Child(Property_spec);
    UHDM::cover* cover_stmt = s.MakeCover();
    UHDM::property_spec* prop_spec = s.MakeProperty_spec();
    UHDM::any* property_expr = compileExpression(component, fC, Property_expr, compileDesign, pstmt, instance, false);
    property_expr = createPropertyInst(property_expr, s);
    prop_spec->VpiPropertyExpr(property_expr);
    cover_stmt->VpiProperty(prop_spec);
    cover_stmt->Stmt(if_stmt);
    stmt = cover_stmt;
    break;
  }
  case VObjectType::slCover_sequence_statement: {
    NodeId Property_expr = fC->Child(Property_spec);
    UHDM::cover* cover_stmt = s.MakeCover();
    cover_stmt->VpiIsCoverSequence();
    UHDM::property_spec* prop_spec = s.MakeProperty_spec();
    UHDM::any* property_expr = compileExpression(component, fC, Property_expr, compileDesign, pstmt, instance, false);
    property_expr = createPropertyInst(property_expr, s);
    prop_spec->VpiPropertyExpr(property_expr);
    cover_stmt->VpiProperty(prop_spec);
    cover_stmt->Stmt(if_stmt);
    stmt = cover_stmt;
    break;
  }
  case VObjectType::slRestrict_property_statement: {
    NodeId Property_expr = fC->Child(Property_spec);
    UHDM::restrict* restrict_stmt = s.MakeRestrict();
    UHDM::property_spec* prop_spec = s.MakeProperty_spec();
    UHDM::any* property_expr = compileExpression(component, fC, Property_expr, compileDesign, pstmt, instance, false);
    property_expr = createPropertyInst(property_expr, s);
    prop_spec->VpiPropertyExpr(property_expr);
    restrict_stmt->VpiProperty(prop_spec);
    restrict_stmt->Stmt(if_stmt);
    stmt = restrict_stmt;
    break;
  }
  default:
    break;
  }

  return stmt;
}


UHDM::any* CompileHelper::compileSimpleImmediateAssertion(
  DesignComponent* component, const FileContent* fC, NodeId the_stmt,
  CompileDesign* compileDesign, UHDM::any* pstmt,
  SURELOG::ValuedComponentI *instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId Expression = fC->Child(the_stmt);
  NodeId Action_block = fC->Sibling(Expression);
  NodeId if_stmt_id = fC->Child(Action_block);
  NodeId else_stmt_id = 0;
  if (fC->Type(if_stmt_id) == slElse) {
    else_stmt_id =  fC->Sibling(if_stmt_id);
    if_stmt_id = 0;
  } else {
    NodeId else_keyword = fC->Sibling(if_stmt_id);
    if (else_keyword)
      else_stmt_id = fC->Sibling(else_keyword);
  }
  UHDM::any* expr = compileExpression(component, fC, Expression, compileDesign, pstmt, instance, false);
  VectorOfany* if_stmts = nullptr;
  if (if_stmt_id)
    if_stmts = compileStmt(component, fC, if_stmt_id, compileDesign, pstmt);
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

UHDM::any* CompileHelper::compileDeferredImmediateAssertion(
  DesignComponent* component, const FileContent* fC, NodeId the_stmt,
  CompileDesign* compileDesign, UHDM::any* pstmt,
  SURELOG::ValuedComponentI *instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId the_stmt_child = fC->Child(the_stmt);
  int isFinal = fC->Type(the_stmt_child) == slPound_delay ? 0 : 1;
  NodeId Expression = isFinal ? the_stmt_child : fC->Sibling(the_stmt_child);
  NodeId Action_block = fC->Sibling(Expression);
  NodeId if_stmt_id = fC->Child(Action_block);
  NodeId else_stmt_id = 0;
  if (fC->Type(if_stmt_id) == slElse) {
    else_stmt_id =  fC->Sibling(if_stmt_id);
    if_stmt_id = 0;
  } else {
    NodeId else_keyword = fC->Sibling(if_stmt_id);
    if (else_keyword)
      else_stmt_id = fC->Sibling(else_keyword);
  }
  UHDM::any* expr = compileExpression(component, fC, Expression, compileDesign, pstmt, instance, false);
  VectorOfany* if_stmts = nullptr;
  if (if_stmt_id)
    if_stmts = compileStmt(component, fC, if_stmt_id, compileDesign, pstmt);
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
  case VObjectType::slDeferred_immediate_assert_statement: {
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
    astmt->VpiIsDeferred(1);
    astmt->VpiIsFinal(isFinal);
    stmt = astmt;
    break;
  }
  case VObjectType::slDeferred_immediate_assume_statement: {
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
    astmt->VpiIsDeferred(1);
    astmt->VpiIsFinal(isFinal);
    stmt = astmt;
    break;
  }
  case VObjectType::slDeferred_immediate_cover_statement: {
    UHDM::immediate_cover* astmt = s.MakeImmediate_cover();
    astmt->VpiParent(pstmt);
    astmt->Expr((UHDM::expr*) expr);
    if (expr)
      expr->VpiParent(astmt);
    astmt->Stmt(if_stmt);
    if (if_stmt)
      if_stmt->VpiParent(astmt);
    astmt->VpiIsDeferred(1);
    astmt->VpiIsFinal(isFinal);
    stmt = astmt;
    break;
  }
  default:
    break;
  }
  return stmt;
}
