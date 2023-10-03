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

#include <Surelog/Design/FileContent.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/CompileHelper.h>

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/clone_tree.h>
#include <uhdm/uhdm.h>

#include <iostream>

namespace SURELOG {

bool CompileHelper::compileAssertionItem(DesignComponent* component,
                                         const FileContent* fC, NodeId nodeId,
                                         CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId item = fC->Child(nodeId);
  if (fC->Type(item) == VObjectType::paConcurrent_assertion_item) {
    NodeId Concurrent_assertion_statement = fC->Child(item);
    UHDM::VectorOfany* stmts =
        compileStmt(component, fC, Concurrent_assertion_statement,
                    compileDesign, Reduce::No, nullptr);
    UHDM::VectorOfany* assertions = component->getAssertions();
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

UHDM::property_inst* createPropertyInst(DesignComponent* component,
                                        UHDM::any* property_expr,
                                        UHDM::Serializer& s) {
  UHDM::property_inst* inst = (UHDM::property_inst*)property_expr;
  if (property_expr->UhdmType() == UHDM::uhdmfunc_call) {
    UHDM::func_call* call = (UHDM::func_call*)property_expr;
    UHDM::property_inst* real_property_expr = s.MakeProperty_inst();
    if (call->Tf_call_args()) {
      UHDM::ElaboratorContext elaboratorContext(&s, false, true);
      UHDM::VectorOfany* args = s.MakeAnyVec();
      real_property_expr->VpiArguments(args);
      for (auto arg : *call->Tf_call_args()) {
        if (arg->UhdmType() == UHDM::uhdmref_obj) {
          UHDM::ref_obj* ref =
              (UHDM::ref_obj*)UHDM::clone_tree(arg, &elaboratorContext);
          args->emplace_back(ref);
          ref->VpiParent(real_property_expr);
          component->needLateBinding(ref);
        } else {
          args->emplace_back(arg);
        }
      }
    }
    real_property_expr->VpiName(call->VpiName());
    real_property_expr->VpiFile(call->VpiFile());
    real_property_expr->VpiLineNo(call->VpiLineNo());
    real_property_expr->VpiColumnNo(call->VpiColumnNo());
    real_property_expr->VpiEndLineNo(call->VpiEndLineNo());
    real_property_expr->VpiEndColumnNo(call->VpiEndColumnNo());
    inst = real_property_expr;
  }
  return inst;
}

UHDM::any* CompileHelper::compileConcurrentAssertion(
    DesignComponent* component, const FileContent* fC, NodeId the_stmt,
    CompileDesign* compileDesign, UHDM::any* pstmt,
    SURELOG::ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId Property_spec = fC->Child(the_stmt);

  NodeId Action_block = fC->Sibling(Property_spec);
  UHDM::any* if_stmt = nullptr;
  UHDM::any* else_stmt = nullptr;
  if (fC->Type(Action_block) == VObjectType::paAction_block) {
    NodeId if_stmt_id = fC->Child(Action_block);
    NodeId else_stmt_id;
    if (fC->Type(if_stmt_id) == VObjectType::paELSE) {
      else_stmt_id = fC->Sibling(if_stmt_id);
      if_stmt_id = InvalidNodeId;
    } else if (NodeId else_keyword = fC->Sibling(if_stmt_id)) {
      else_stmt_id = fC->Sibling(else_keyword);
    }
    if (if_stmt_id) {
      if (UHDM::VectorOfany* if_stmts = compileStmt(
              component, fC, if_stmt_id, compileDesign, Reduce::No, pstmt)) {
        if_stmt = (*if_stmts)[0];
      }
    }
    if (else_stmt_id) {
      if (UHDM::VectorOfany* else_stmts = compileStmt(
              component, fC, else_stmt_id, compileDesign, Reduce::No, pstmt)) {
        else_stmt = (*else_stmts)[0];
      }
    }
  }

  UHDM::any* stmt = nullptr;
  switch (fC->Type(the_stmt)) {
    case VObjectType::paAssert_property_statement: {
      NodeId Property_expr = fC->Child(Property_spec);
      UHDM::property_spec* prop_spec = s.MakeProperty_spec();
      if (UHDM::any* property_expr =
              compileExpression(component, fC, Property_expr, compileDesign,
                                Reduce::No, prop_spec, instance)) {
        property_expr = createPropertyInst(component, property_expr, s);
        prop_spec->VpiPropertyExpr(property_expr);
      }
      fC->populateCoreMembers(Property_spec, Property_spec, prop_spec);
      UHDM::assert_stmt* assert_stmt = s.MakeAssert_stmt();
      prop_spec->VpiParent(assert_stmt);
      assert_stmt->VpiProperty(prop_spec);
      if (if_stmt) {
        assert_stmt->Stmt(if_stmt);
        if_stmt->VpiParent(assert_stmt);
      } else if (else_stmt) {
        assert_stmt->Stmt(else_stmt);
        else_stmt->VpiParent(assert_stmt);
      }
      stmt = assert_stmt;
      break;
    }
    case VObjectType::paAssume_property_statement: {
      NodeId Property_expr = fC->Child(Property_spec);
      UHDM::property_spec* prop_spec = s.MakeProperty_spec();
      if (fC->Type(Property_expr) == VObjectType::paClocking_event) {
        if (UHDM::expr* clocking_event = (UHDM::expr*)compileExpression(
                component, fC, Property_expr, compileDesign, Reduce::No,
                prop_spec, instance)) {
          prop_spec->VpiClockingEvent(clocking_event);
        }
        Property_expr = fC->Sibling(Property_expr);
      }
      if (UHDM::any* property_expr =
              compileExpression(component, fC, Property_expr, compileDesign,
                                Reduce::No, prop_spec, instance)) {
        property_expr = createPropertyInst(component, property_expr, s);
        prop_spec->VpiPropertyExpr(property_expr);
      }
      fC->populateCoreMembers(Property_spec, Property_spec, prop_spec);
      UHDM::assume* assume_stmt = s.MakeAssume();
      assume_stmt->VpiProperty(prop_spec);
      prop_spec->VpiParent(assume_stmt);
      if (if_stmt) {
        assume_stmt->Stmt(if_stmt);
        if_stmt->VpiParent(assume_stmt);
      } else if (else_stmt) {
        assume_stmt->Stmt(else_stmt);
        else_stmt->VpiParent(assume_stmt);
      }
      stmt = assume_stmt;
      break;
    }
    case VObjectType::paCover_property_statement: {
      NodeId Property_expr = fC->Child(Property_spec);
      UHDM::property_spec* prop_spec = s.MakeProperty_spec();
      if (UHDM::any* property_expr =
              compileExpression(component, fC, Property_expr, compileDesign,
                                Reduce::No, prop_spec, instance)) {
        property_expr = createPropertyInst(component, property_expr, s);
        prop_spec->VpiPropertyExpr(property_expr);
      }
      fC->populateCoreMembers(Property_spec, Property_spec, prop_spec);
      UHDM::cover* cover_stmt = s.MakeCover();
      prop_spec->VpiParent(cover_stmt);
      cover_stmt->VpiProperty(prop_spec);
      if (if_stmt != nullptr) {
        cover_stmt->Stmt(if_stmt);
        if_stmt->VpiParent(cover_stmt);
      }
      stmt = cover_stmt;
      break;
    }
    case VObjectType::paCover_sequence_statement: {
      NodeId Property_expr = fC->Child(Property_spec);
      UHDM::property_spec* prop_spec = s.MakeProperty_spec();
      if (UHDM::any* property_expr =
              compileExpression(component, fC, Property_expr, compileDesign,
                                Reduce::No, prop_spec, instance)) {
        property_expr = createPropertyInst(component, property_expr, s);
        prop_spec->VpiPropertyExpr(property_expr);
      }
      fC->populateCoreMembers(Property_expr, Property_expr, prop_spec);
      UHDM::cover* cover_stmt = s.MakeCover();
      cover_stmt->VpiIsCoverSequence();
      prop_spec->VpiParent(cover_stmt);
      cover_stmt->VpiProperty(prop_spec);
      if (if_stmt != nullptr) {
        cover_stmt->Stmt(if_stmt);
        if_stmt->VpiParent(cover_stmt);
      }
      stmt = cover_stmt;
      break;
    }
    case VObjectType::paRestrict_property_statement: {
      NodeId Property_expr = fC->Child(Property_spec);
      UHDM::property_spec* prop_spec = s.MakeProperty_spec();
      if (UHDM::any* property_expr =
              compileExpression(component, fC, Property_expr, compileDesign,
                                Reduce::No, prop_spec, instance)) {
        property_expr = createPropertyInst(component, property_expr, s);
        prop_spec->VpiPropertyExpr(property_expr);
      }
      fC->populateCoreMembers(Property_spec, Property_spec, prop_spec);
      UHDM::restrict* restrict_stmt = s.MakeRestrict();
      prop_spec->VpiParent(restrict_stmt);
      restrict_stmt->VpiProperty(prop_spec);
      if (if_stmt != nullptr) {
        restrict_stmt->Stmt(if_stmt);
        if_stmt->VpiParent(restrict_stmt);
      }
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
    SURELOG::ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId Expression = fC->Child(the_stmt);
  NodeId Action_block = fC->Sibling(Expression);
  NodeId if_stmt_id = fC->Child(Action_block);
  NodeId else_stmt_id;
  if (fC->Type(if_stmt_id) == VObjectType::paELSE) {
    else_stmt_id = fC->Sibling(if_stmt_id);
    if_stmt_id = InvalidNodeId;
  } else {
    NodeId else_keyword = fC->Sibling(if_stmt_id);
    if (else_keyword) else_stmt_id = fC->Sibling(else_keyword);
  }
  UHDM::any* expr = compileExpression(component, fC, Expression, compileDesign,
                                      Reduce::No, pstmt, instance);
  UHDM::VectorOfany* if_stmts = nullptr;
  if (if_stmt_id)
    if_stmts = compileStmt(component, fC, if_stmt_id, compileDesign, Reduce::No,
                           pstmt);
  UHDM::any* if_stmt = nullptr;
  if (if_stmts) if_stmt = (*if_stmts)[0];
  UHDM::VectorOfany* else_stmts = nullptr;
  if (else_stmt_id)
    else_stmts = compileStmt(component, fC, else_stmt_id, compileDesign,
                             Reduce::No, pstmt);
  UHDM::any* else_stmt = nullptr;
  if (else_stmts) else_stmt = (*else_stmts)[0];
  UHDM::any* stmt = nullptr;
  switch (fC->Type(the_stmt)) {
    case VObjectType::paSimple_immediate_assert_statement: {
      UHDM::immediate_assert* astmt = s.MakeImmediate_assert();
      astmt->VpiParent(pstmt);
      astmt->Expr((UHDM::expr*)expr);
      if (expr) expr->VpiParent(astmt);
      astmt->Stmt(if_stmt);
      if (if_stmt) if_stmt->VpiParent(astmt);
      astmt->Else_stmt(else_stmt);
      if (else_stmt) else_stmt->VpiParent(astmt);
      stmt = astmt;
      break;
    }
    case VObjectType::paSimple_immediate_assume_statement: {
      UHDM::immediate_assume* astmt = s.MakeImmediate_assume();
      astmt->VpiParent(pstmt);
      astmt->Expr((UHDM::expr*)expr);
      if (expr) expr->VpiParent(astmt);
      astmt->Stmt(if_stmt);
      if (if_stmt) if_stmt->VpiParent(astmt);
      astmt->Else_stmt(else_stmt);
      if (else_stmt) else_stmt->VpiParent(astmt);
      stmt = astmt;
      break;
    }
    case VObjectType::paSimple_immediate_cover_statement: {
      UHDM::immediate_cover* astmt = s.MakeImmediate_cover();
      astmt->VpiParent(pstmt);
      astmt->Expr((UHDM::expr*)expr);
      if (expr) expr->VpiParent(astmt);
      astmt->Stmt(if_stmt);
      if (if_stmt) if_stmt->VpiParent(astmt);
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
    SURELOG::ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId the_stmt_child = fC->Child(the_stmt);
  int32_t isFinal =
      fC->Type(the_stmt_child) == VObjectType::paPound_delay ? 0 : 1;
  NodeId Expression = isFinal ? the_stmt_child : fC->Sibling(the_stmt_child);
  NodeId Action_block = fC->Sibling(Expression);
  NodeId if_stmt_id = fC->Child(Action_block);
  NodeId else_stmt_id;
  if (fC->Type(if_stmt_id) == VObjectType::paELSE) {
    else_stmt_id = fC->Sibling(if_stmt_id);
    if_stmt_id = InvalidNodeId;
  } else {
    NodeId else_keyword = fC->Sibling(if_stmt_id);
    if (else_keyword) else_stmt_id = fC->Sibling(else_keyword);
  }
  UHDM::any* expr = compileExpression(component, fC, Expression, compileDesign,
                                      Reduce::No, pstmt, instance);
  UHDM::VectorOfany* if_stmts = nullptr;
  if (if_stmt_id)
    if_stmts = compileStmt(component, fC, if_stmt_id, compileDesign, Reduce::No,
                           pstmt);
  UHDM::any* if_stmt = nullptr;
  if (if_stmts) if_stmt = (*if_stmts)[0];
  UHDM::VectorOfany* else_stmts = nullptr;
  if (else_stmt_id)
    else_stmts = compileStmt(component, fC, else_stmt_id, compileDesign,
                             Reduce::No, pstmt);
  UHDM::any* else_stmt = nullptr;
  if (else_stmts) else_stmt = (*else_stmts)[0];
  UHDM::any* stmt = nullptr;
  switch (fC->Type(the_stmt)) {
    case VObjectType::paDeferred_immediate_assert_statement: {
      UHDM::immediate_assert* astmt = s.MakeImmediate_assert();
      astmt->VpiParent(pstmt);
      astmt->Expr((UHDM::expr*)expr);
      if (expr) expr->VpiParent(astmt);
      astmt->Stmt(if_stmt);
      if (if_stmt) if_stmt->VpiParent(astmt);
      astmt->Else_stmt(else_stmt);
      if (else_stmt) else_stmt->VpiParent(astmt);
      astmt->VpiIsDeferred(1);
      astmt->VpiIsFinal(isFinal);
      stmt = astmt;
      break;
    }
    case VObjectType::paDeferred_immediate_assume_statement: {
      UHDM::immediate_assume* astmt = s.MakeImmediate_assume();
      astmt->VpiParent(pstmt);
      astmt->Expr((UHDM::expr*)expr);
      if (expr) expr->VpiParent(astmt);
      astmt->Stmt(if_stmt);
      if (if_stmt) if_stmt->VpiParent(astmt);
      astmt->Else_stmt(else_stmt);
      if (else_stmt) else_stmt->VpiParent(astmt);
      astmt->VpiIsDeferred(1);
      astmt->VpiIsFinal(isFinal);
      stmt = astmt;
      break;
    }
    case VObjectType::paDeferred_immediate_cover_statement: {
      UHDM::immediate_cover* astmt = s.MakeImmediate_cover();
      astmt->VpiParent(pstmt);
      astmt->Expr((UHDM::expr*)expr);
      if (expr) expr->VpiParent(astmt);
      astmt->Stmt(if_stmt);
      if (if_stmt) if_stmt->VpiParent(astmt);
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

UHDM::property_decl* CompileHelper::compilePropertyDeclaration(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, UHDM::any* pstmt,
    ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::property_decl* result = s.MakeProperty_decl();
  std::string_view propName = fC->SymName(nodeId);
  result->VpiName(propName);
  result->VpiParent(pstmt);
  NodeId Property_spec = fC->Sibling(nodeId);
  if (fC->Type(Property_spec) == VObjectType::paProperty_port_list) {
    NodeId Property_port_item = fC->Child(Property_spec);
    UHDM::VectorOfprop_formal_decl* ports = s.MakeProp_formal_declVec();
    result->Prop_formal_decls(ports);
    while (Property_port_item) {
      NodeId Property_formal_type = fC->Child(Property_port_item);
      NodeId SeqFormatType_Data = fC->Child(Property_formal_type);
      NodeId Data_type_or_implicit = fC->Child(SeqFormatType_Data);
      NodeId Data_type = fC->Child(Data_type_or_implicit);
      UHDM::typespec* tps =
          compileTypespec(component, fC, Data_type, compileDesign, Reduce::No,
                          pstmt, instance, false);

      NodeId Port_name = fC->Sibling(Property_formal_type);
      UHDM::prop_formal_decl* prop_port_decl = s.MakeProp_formal_decl();
      ports->push_back(prop_port_decl);
      prop_port_decl->VpiName(fC->SymName(Port_name));
      UHDM::ref_typespec* rtps = s.MakeRef_typespec();
      rtps->Actual_typespec(tps);
      prop_port_decl->Typespec(rtps);
      Property_port_item = fC->Sibling(Property_port_item);
    }
    Property_spec = fC->Sibling(Property_spec);
  }
  NodeId Clocking_event = fC->Child(Property_spec);
  NodeId Property_expr = fC->Sibling(Clocking_event);
  if (Property_expr == InvalidNodeId) {
    Property_expr = Clocking_event;
    Clocking_event = InvalidNodeId;
  }
  UHDM::property_spec* prop_spec = s.MakeProperty_spec();
  prop_spec->VpiParent(result);
  if (Clocking_event) {
    if (UHDM::expr* clocking_event = (UHDM::expr*)compileExpression(
            component, fC, Clocking_event, compileDesign, Reduce::No, prop_spec,
            instance)) {
      prop_spec->VpiClockingEvent(clocking_event);
      clocking_event->VpiParent(prop_spec);
    }
  }
  result->Property_spec(prop_spec);
  if (UHDM::any* property_expr =
          compileExpression(component, fC, Property_expr, compileDesign,
                            Reduce::No, prop_spec, instance)) {
    property_expr = createPropertyInst(component, property_expr, s);
    prop_spec->VpiPropertyExpr(property_expr);
  }
  fC->populateCoreMembers(Property_spec, Property_spec, prop_spec);
  return result;
}

UHDM::sequence_decl* CompileHelper::compileSequenceDeclaration(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, UHDM::any* pstmt,
    ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::sequence_decl* result = s.MakeSequence_decl();
  std::string_view propName = fC->SymName(nodeId);
  result->VpiName(propName);
  result->VpiParent(pstmt);
  NodeId Sequence_expr = fC->Sibling(nodeId);
  if (fC->Type(Sequence_expr) == VObjectType::paSequence_port_list) {
    NodeId Sequence_port_item = fC->Child(Sequence_expr);
    UHDM::VectorOfseq_formal_decl* ports = s.MakeSeq_formal_declVec();
    result->Seq_formal_decls(ports);
    while (Sequence_port_item) {
      NodeId Sequence_formal_type = fC->Child(Sequence_port_item);
      NodeId SeqFormatType_Data = fC->Child(Sequence_formal_type);
      NodeId Data_type_or_implicit = fC->Child(SeqFormatType_Data);
      NodeId Data_type = fC->Child(Data_type_or_implicit);
      UHDM::typespec* tps =
          compileTypespec(component, fC, Data_type, compileDesign, Reduce::No,
                          pstmt, instance, false);

      NodeId Port_name = fC->Sibling(Sequence_formal_type);
      UHDM::seq_formal_decl* prop_port_decl = s.MakeSeq_formal_decl();
      ports->push_back(prop_port_decl);
      prop_port_decl->VpiName(fC->SymName(Port_name));
      UHDM::ref_typespec* rtps = s.MakeRef_typespec();
      rtps->Actual_typespec(tps);
      prop_port_decl->Typespec(rtps);
      Sequence_port_item = fC->Sibling(Sequence_port_item);
    }
    Sequence_expr = fC->Sibling(Sequence_expr);
  }
  NodeId lookup = fC->Child(Sequence_expr);
  if (fC->Type(lookup) == VObjectType::paClocking_event) {
    UHDM::multiclock_sequence_expr* mexpr = s.MakeMulticlock_sequence_expr();
    result->Sequence_expr_multiclock_group(mexpr);
    mexpr->Clocked_seqs(s.MakeClocked_seqVec());
    while (fC->Type(lookup) == VObjectType::paClocking_event) {
      UHDM::expr* clock_event = any_cast<UHDM::expr*>(compileExpression(
          component, fC, lookup, compileDesign, Reduce::No, result, instance));
      UHDM::clocked_seq* seq = s.MakeClocked_seq();
      mexpr->Clocked_seqs()->push_back(seq);
      seq->VpiClockingEvent(clock_event);
      lookup = fC->Sibling(lookup);
    }
    if (UHDM::any* seq_expr =
            compileExpression(component, fC, lookup, compileDesign, Reduce::No,
                              result, instance)) {
      mexpr->Clocked_seqs()->back()->VpiSequenceExpr(seq_expr);
    }
  } else {
    if (UHDM::any* seq_expr =
            compileExpression(component, fC, Sequence_expr, compileDesign,
                              Reduce::No, result, instance)) {
      result->Sequence_expr_multiclock_group(seq_expr);
    }
  }
  return result;
}

}  // namespace SURELOG
