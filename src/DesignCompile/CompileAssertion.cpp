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

#include "Surelog/Common/NodeId.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/SourceCompile/VObjectTypes.h"

// UHDM
#include <uhdm/BaseClass.h>
#include <uhdm/ElaboratorListener.h>
#include <uhdm/clone_tree.h>
#include <uhdm/expr.h>
#include <uhdm/uhdm.h>
#include <uhdm/uhdm_types.h>

#include <cstdint>
#include <iostream>
#include <string_view>

namespace SURELOG {

bool CompileHelper::compileAssertionItem(DesignComponent* component,
                                         const FileContent* fC, NodeId nodeId,
                                         CompileDesign* compileDesign) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  NodeId item = fC->Child(nodeId);
  if (fC->Type(item) == VObjectType::paConcurrent_assertion_item) {
    NodeId Concurrent_assertion_statement = fC->Child(item);
    if (uhdm::AnyCollection* stmts =
            compileStmt(component, fC, Concurrent_assertion_statement,
                        compileDesign, Reduce::No, nullptr)) {
      uhdm::AnyCollection* assertions = component->getAssertions();
      if (assertions == nullptr) {
        component->setAssertions(s.makeCollection<uhdm::Any>());
        assertions = component->getAssertions();
      }
      for (auto stmt : *stmts) {
        assertions->emplace_back(stmt);
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

uhdm::PropertyInst* createPropertyInst(DesignComponent* component,
                                       uhdm::Any* property_expr,
                                       uhdm::Serializer& s) {
  uhdm::PropertyInst* inst = (uhdm::PropertyInst*)property_expr;
  if (property_expr->getUhdmType() == uhdm::UhdmType::FuncCall) {
    uhdm::FuncCall* call = (uhdm::FuncCall*)property_expr;
    uhdm::PropertyInst* real_property_expr = s.make<uhdm::PropertyInst>();
    real_property_expr->setParent(property_expr);
    if (call->getArguments()) {
      uhdm::ElaboratorContext elaboratorContext(&s, false, true);
      uhdm::AnyCollection* args = real_property_expr->getArguments(true);
      for (auto arg : *call->getArguments()) {
        if (arg->getUhdmType() == uhdm::UhdmType::RefObj) {
          uhdm::RefObj* ref =
              (uhdm::RefObj*)uhdm::clone_tree(arg, &elaboratorContext);
          args->emplace_back(ref);
          ref->setParent(real_property_expr);
        } else {
          args->emplace_back(arg);
        }
      }
    }
    real_property_expr->setName(call->getName());
    real_property_expr->setFile(call->getFile());
    real_property_expr->setStartLine(call->getStartLine());
    real_property_expr->setStartColumn(call->getStartColumn());
    real_property_expr->setEndLine(call->getEndLine());
    real_property_expr->setEndColumn(call->getEndColumn());
    inst = real_property_expr;
  }
  return inst;
}

uhdm::Any* CompileHelper::compileConcurrentAssertion(
    DesignComponent* component, const FileContent* fC, NodeId the_stmt,
    CompileDesign* compileDesign, uhdm::Any* pstmt,
    SURELOG::ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  NodeId Property_spec = fC->Child(the_stmt);

  NodeId Action_block = fC->Sibling(Property_spec);
  uhdm::Any* if_stmt = nullptr;
  uhdm::Any* else_stmt = nullptr;
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
      if (uhdm::AnyCollection* if_stmts = compileStmt(
              component, fC, if_stmt_id, compileDesign, Reduce::No, pstmt)) {
        if_stmt = (*if_stmts)[0];
      }
    }
    if (else_stmt_id) {
      if (uhdm::AnyCollection* else_stmts = compileStmt(
              component, fC, else_stmt_id, compileDesign, Reduce::No, pstmt)) {
        else_stmt = (*else_stmts)[0];
      }
    }
  }

  uhdm::Any* stmt = nullptr;
  switch (fC->Type(the_stmt)) {
    case VObjectType::paAssert_property_statement: {
      NodeId Property_expr = fC->Child(Property_spec);
      uhdm::PropertySpec* prop_spec = s.make<uhdm::PropertySpec>();
      if (uhdm::Any* property_expr =
              compileExpression(component, fC, Property_expr, compileDesign,
                                Reduce::No, prop_spec, instance)) {
        property_expr = createPropertyInst(component, property_expr, s);
        prop_spec->setPropertyExpr(property_expr);
      }
      fC->populateCoreMembers(Property_spec, Property_spec, prop_spec);
      uhdm::Assert* assert_stmt = s.make<uhdm::Assert>();
      prop_spec->setParent(assert_stmt);
      assert_stmt->setProperty(prop_spec);
      if (if_stmt) {
        assert_stmt->setStmt(if_stmt);
        if_stmt->setParent(assert_stmt);
      } else if (else_stmt) {
        assert_stmt->setStmt(else_stmt);
        else_stmt->setParent(assert_stmt);
      }
      stmt = assert_stmt;
      break;
    }
    case VObjectType::paAssume_property_statement: {
      NodeId Property_expr = fC->Child(Property_spec);
      uhdm::PropertySpec* prop_spec = s.make<uhdm::PropertySpec>();
      if (fC->Type(Property_expr) == VObjectType::paClocking_event) {
        if (uhdm::Expr* clocking_event = (uhdm::Expr*)compileExpression(
                component, fC, Property_expr, compileDesign, Reduce::No,
                prop_spec, instance)) {
          prop_spec->setClockingEvent(clocking_event);
        }
        Property_expr = fC->Sibling(Property_expr);
      }
      if (uhdm::Any* property_expr =
              compileExpression(component, fC, Property_expr, compileDesign,
                                Reduce::No, prop_spec, instance)) {
        property_expr = createPropertyInst(component, property_expr, s);
        prop_spec->setPropertyExpr(property_expr);
      }
      fC->populateCoreMembers(Property_spec, Property_spec, prop_spec);
      uhdm::Assume* assume_stmt = s.make<uhdm::Assume>();
      assume_stmt->setProperty(prop_spec);
      prop_spec->setParent(assume_stmt);
      if (if_stmt) {
        assume_stmt->setStmt(if_stmt);
        if_stmt->setParent(assume_stmt);
      } else if (else_stmt) {
        assume_stmt->setStmt(else_stmt);
        else_stmt->setParent(assume_stmt);
      }
      stmt = assume_stmt;
      break;
    }
    case VObjectType::paCover_property_statement: {
      NodeId Property_expr = fC->Child(Property_spec);
      uhdm::PropertySpec* prop_spec = s.make<uhdm::PropertySpec>();
      if (uhdm::Any* property_expr =
              compileExpression(component, fC, Property_expr, compileDesign,
                                Reduce::No, prop_spec, instance)) {
        property_expr = createPropertyInst(component, property_expr, s);
        prop_spec->setPropertyExpr(property_expr);
      }
      fC->populateCoreMembers(Property_spec, Property_spec, prop_spec);
      uhdm::Cover* cover_stmt = s.make<uhdm::Cover>();
      prop_spec->setParent(cover_stmt);
      cover_stmt->setProperty(prop_spec);
      if (if_stmt != nullptr) {
        cover_stmt->setStmt(if_stmt);
        if_stmt->setParent(cover_stmt);
      }
      stmt = cover_stmt;
      break;
    }
    case VObjectType::paCover_sequence_statement: {
      NodeId Property_expr = fC->Child(Property_spec);
      uhdm::PropertySpec* prop_spec = s.make<uhdm::PropertySpec>();
      if (uhdm::Any* property_expr =
              compileExpression(component, fC, Property_expr, compileDesign,
                                Reduce::No, prop_spec, instance)) {
        property_expr = createPropertyInst(component, property_expr, s);
        prop_spec->setPropertyExpr(property_expr);
      }
      fC->populateCoreMembers(Property_expr, Property_expr, prop_spec);
      uhdm::Cover* cover_stmt = s.make<uhdm::Cover>();
      cover_stmt->setIsCoverSequence(true);
      prop_spec->setParent(cover_stmt);
      cover_stmt->setProperty(prop_spec);
      if (if_stmt != nullptr) {
        cover_stmt->setStmt(if_stmt);
        if_stmt->setParent(cover_stmt);
      }
      stmt = cover_stmt;
      break;
    }
    case VObjectType::paRestrict_property_statement: {
      NodeId Property_expr = fC->Child(Property_spec);
      uhdm::PropertySpec* prop_spec = s.make<uhdm::PropertySpec>();
      if (uhdm::Any* property_expr =
              compileExpression(component, fC, Property_expr, compileDesign,
                                Reduce::No, prop_spec, instance)) {
        property_expr = createPropertyInst(component, property_expr, s);
        prop_spec->setPropertyExpr(property_expr);
      }
      fC->populateCoreMembers(Property_spec, Property_spec, prop_spec);
      uhdm::Restrict* restrict_stmt = s.make<uhdm::Restrict>();
      prop_spec->setParent(restrict_stmt);
      restrict_stmt->setProperty(prop_spec);
      if (if_stmt != nullptr) {
        restrict_stmt->setStmt(if_stmt);
        if_stmt->setParent(restrict_stmt);
      }
      stmt = restrict_stmt;
      break;
    }
    default:
      break;
  }

  return stmt;
}

uhdm::Any* CompileHelper::compileSimpleImmediateAssertion(
    DesignComponent* component, const FileContent* fC, NodeId the_stmt,
    CompileDesign* compileDesign, uhdm::Any* pstmt,
    SURELOG::ValuedComponentI* instance) {
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
  uhdm::Serializer& s = compileDesign->getSerializer();

  uhdm::Any* stmt = nullptr;
  switch (fC->Type(the_stmt)) {
    case VObjectType::paSimple_immediate_assert_statement: {
      stmt = s.make<uhdm::ImmediateAssert>();
    } break;
    case VObjectType::paSimple_immediate_assume_statement: {
      stmt = s.make<uhdm::ImmediateAssume>();
    } break;
    case VObjectType::paSimple_immediate_cover_statement: {
      stmt = s.make<uhdm::ImmediateCover>();
    } break;
    default:
      return nullptr;
  }
  fC->populateCoreMembers(the_stmt, the_stmt, stmt);
  stmt->setParent(pstmt);

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

  uhdm::Any* if_stmt = nullptr;
  if (if_stmt_id) {
    if (uhdm::AnyCollection* const if_stmts = compileStmt(
            component, fC, if_stmt_id, compileDesign, Reduce::No, stmt)) {
      if_stmt = (*if_stmts)[0];
    }
  }

  uhdm::Any* else_stmt = nullptr;
  if (else_stmt_id) {
    if (uhdm::AnyCollection* const else_stmts = compileStmt(
            component, fC, else_stmt_id, compileDesign, Reduce::No, stmt)) {
      else_stmt = (*else_stmts)[0];
    }
  }

  uhdm::Any* expr = compileExpression(component, fC, Expression, compileDesign,
                                      Reduce::No, stmt, instance);

  switch (fC->Type(the_stmt)) {
    case VObjectType::paSimple_immediate_assert_statement: {
      uhdm::ImmediateAssert* astmt = any_cast<uhdm::ImmediateAssert>(stmt);
      astmt->setExpr((uhdm::Expr*)expr);
      astmt->setStmt(if_stmt);
      astmt->setElseStmt(else_stmt);
      break;
    }
    case VObjectType::paSimple_immediate_assume_statement: {
      uhdm::ImmediateAssume* astmt = any_cast<uhdm::ImmediateAssume>(stmt);
      astmt->setExpr((uhdm::Expr*)expr);
      astmt->setStmt(if_stmt);
      astmt->setElseStmt(else_stmt);
      break;
    }
    case VObjectType::paSimple_immediate_cover_statement: {
      uhdm::ImmediateCover* astmt = any_cast<uhdm::ImmediateCover>(stmt);
      astmt->setExpr((uhdm::Expr*)expr);
      astmt->setStmt(if_stmt);
      break;
    }
    default:
      break;
  }

  return stmt;
}

uhdm::Any* CompileHelper::compileDeferredImmediateAssertion(
    DesignComponent* component, const FileContent* fC, NodeId the_stmt,
    CompileDesign* compileDesign, uhdm::Any* pstmt,
    SURELOG::ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();
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
  uhdm::Any* expr = compileExpression(component, fC, Expression, compileDesign,
                                      Reduce::No, pstmt, instance);
  uhdm::AnyCollection* if_stmts = nullptr;
  if (if_stmt_id)
    if_stmts = compileStmt(component, fC, if_stmt_id, compileDesign, Reduce::No,
                           pstmt);
  uhdm::Any* if_stmt = nullptr;
  if (if_stmts) if_stmt = (*if_stmts)[0];
  uhdm::AnyCollection* else_stmts = nullptr;
  if (else_stmt_id)
    else_stmts = compileStmt(component, fC, else_stmt_id, compileDesign,
                             Reduce::No, pstmt);
  uhdm::Any* else_stmt = nullptr;
  if (else_stmts) else_stmt = (*else_stmts)[0];
  uhdm::Any* stmt = nullptr;
  switch (fC->Type(the_stmt)) {
    case VObjectType::paDeferred_immediate_assert_statement: {
      uhdm::ImmediateAssert* astmt = s.make<uhdm::ImmediateAssert>();
      fC->populateCoreMembers(the_stmt, the_stmt, astmt);
      astmt->setParent(pstmt);
      astmt->setExpr((uhdm::Expr*)expr);
      if (expr) expr->setParent(astmt);
      astmt->setStmt(if_stmt);
      if (if_stmt) if_stmt->setParent(astmt);
      astmt->setElseStmt(else_stmt);
      if (else_stmt) else_stmt->setParent(astmt);
      astmt->setIsDeferred(1);
      astmt->setIsFinal(isFinal);
      stmt = astmt;
      break;
    }
    case VObjectType::paDeferred_immediate_assume_statement: {
      uhdm::ImmediateAssume* astmt = s.make<uhdm::ImmediateAssume>();
      fC->populateCoreMembers(the_stmt, the_stmt, astmt);
      astmt->setParent(pstmt);
      astmt->setExpr((uhdm::Expr*)expr);
      if (expr) expr->setParent(astmt);
      astmt->setStmt(if_stmt);
      if (if_stmt) if_stmt->setParent(astmt);
      astmt->setElseStmt(else_stmt);
      if (else_stmt) else_stmt->setParent(astmt);
      astmt->setIsDeferred(1);
      astmt->setIsFinal(isFinal);
      stmt = astmt;
      break;
    }
    case VObjectType::paDeferred_immediate_cover_statement: {
      uhdm::ImmediateCover* astmt = s.make<uhdm::ImmediateCover>();
      fC->populateCoreMembers(the_stmt, the_stmt, astmt);
      astmt->setParent(pstmt);
      astmt->setExpr((uhdm::Expr*)expr);
      if (expr) expr->setParent(astmt);
      astmt->setStmt(if_stmt);
      if (if_stmt) if_stmt->setParent(astmt);
      astmt->setIsDeferred(1);
      astmt->setIsFinal(isFinal);
      stmt = astmt;
      break;
    }
    default:
      break;
  }
  return stmt;
}

uhdm::PropertyDecl* CompileHelper::compilePropertyDeclaration(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, uhdm::Any* pstmt,
    ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::PropertyDecl* result = s.make<uhdm::PropertyDecl>();
  fC->populateCoreMembers(nodeId, nodeId, result);
  nodeId = fC->Child(nodeId);
  std::string_view propName = fC->SymName(nodeId);
  result->setName(propName);
  result->setParent(pstmt);
  NodeId Property_spec = fC->Sibling(nodeId);
  if (fC->Type(Property_spec) == VObjectType::paProperty_port_list) {
    NodeId Property_port_item = fC->Child(Property_spec);
    uhdm::PropFormalDeclCollection* ports = result->getPropFormalDecls(true);
    uhdm::Typespec* tps = nullptr;
    NodeId last_Data_type;
    while (Property_port_item) {
      NodeId Property_formal_type = fC->Child(Property_port_item);
      NodeId SeqFormatType_Data = fC->Child(Property_formal_type);
      NodeId Data_type_or_implicit = fC->Child(SeqFormatType_Data);
      NodeId Data_type = fC->Child(Data_type_or_implicit);
      if (Data_type) {
        tps = compileTypespec(component, fC, Data_type, compileDesign,
                              Reduce::No, pstmt, instance, false);
      } else {
        Data_type = last_Data_type;
      }

      NodeId Port_name = fC->Sibling(Property_formal_type);
      uhdm::PropFormalDecl* prop_port_decl = s.make<uhdm::PropFormalDecl>();
      prop_port_decl->setParent(result);
      fC->populateCoreMembers(Port_name, Port_name, prop_port_decl);
      ports->emplace_back(prop_port_decl);
      prop_port_decl->setName(fC->SymName(Port_name));
      if (tps != nullptr) {
        uhdm::RefTypespec* rtps = s.make<uhdm::RefTypespec>();
        rtps->setActual(tps);
        rtps->setName(fC->SymName(Port_name));
        prop_port_decl->setTypespec(rtps);
        rtps->setParent(prop_port_decl);
        fC->populateCoreMembers(Data_type, Data_type, rtps);
      }
      Property_port_item = fC->Sibling(Property_port_item);
      last_Data_type = Data_type;
    }
    Property_spec = fC->Sibling(Property_spec);
  }
  if (fC->Type(Property_spec) ==
      VObjectType::paAssertion_variable_declaration) {
    uhdm::VariablesCollection* vars = result->getVariables(true);
    while (fC->Type(Property_spec) ==
           VObjectType::paAssertion_variable_declaration) {
      NodeId Assertion_variable_declaration = Property_spec;
      uhdm::AnyCollection* varst =
          compileDataDeclaration(component, fC, Assertion_variable_declaration,
                                 compileDesign, Reduce::No, pstmt, instance);
      if (varst) {
        for (auto v : *varst) {
          if (uhdm::Assignment* vast = any_cast<uhdm::Assignment*>(v)) {
            if (uhdm::Variables* va =
                    any_cast<uhdm::Variables*>(vast->getLhs())) {
              vars->emplace_back(va);
            }
          }
        }
      }
      Property_spec = fC->Sibling(Property_spec);
    }
  }
  NodeId Clocking_event = fC->Child(Property_spec);
  NodeId Property_expr = fC->Sibling(Clocking_event);
  if (Property_expr == InvalidNodeId) {
    Property_expr = Clocking_event;
    Clocking_event = InvalidNodeId;
  }
  uhdm::PropertySpec* prop_spec = s.make<uhdm::PropertySpec>();
  prop_spec->setParent(result);
  if (Clocking_event) {
    if (uhdm::Expr* clocking_event = (uhdm::Expr*)compileExpression(
            component, fC, Clocking_event, compileDesign, Reduce::No, prop_spec,
            instance)) {
      prop_spec->setClockingEvent(clocking_event);
      clocking_event->setParent(prop_spec);
    }
  }
  result->setPropertySpec(prop_spec);
  if (uhdm::Any* property_expr =
          compileExpression(component, fC, Property_expr, compileDesign,
                            Reduce::No, prop_spec, instance)) {
    property_expr = createPropertyInst(component, property_expr, s);
    prop_spec->setPropertyExpr(property_expr);
  }
  fC->populateCoreMembers(Property_spec, Property_spec, prop_spec);
  return result;
}

uhdm::SequenceDecl* CompileHelper::compileSequenceDeclaration(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, uhdm::Any* pstmt,
    ValuedComponentI* instance) {
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::SequenceDecl* result = s.make<uhdm::SequenceDecl>();
  fC->populateCoreMembers(nodeId, nodeId, result);
  nodeId = fC->Child(nodeId);
  std::string_view propName = fC->SymName(nodeId);
  result->setName(propName);
  result->setParent(pstmt);
  NodeId Sequence_expr = fC->Sibling(nodeId);
  if (fC->Type(Sequence_expr) == VObjectType::paSequence_port_list) {
    NodeId Sequence_port_item = fC->Child(Sequence_expr);
    uhdm::SeqFormalDeclCollection* ports = result->getSeqFormalDecls(true);
    while (Sequence_port_item) {
      NodeId Sequence_formal_type = fC->Child(Sequence_port_item);
      NodeId SeqFormatType_Data = fC->Child(Sequence_formal_type);
      NodeId Data_type_or_implicit = fC->Child(SeqFormatType_Data);
      NodeId Data_type = fC->Child(Data_type_or_implicit);
      uhdm::Typespec* tps =
          compileTypespec(component, fC, Data_type, compileDesign, Reduce::No,
                          pstmt, instance, false);

      NodeId Port_name = fC->Sibling(Sequence_formal_type);
      uhdm::SeqFormalDecl* prop_port_decl = s.make<uhdm::SeqFormalDecl>();
      fC->populateCoreMembers(Sequence_expr, Sequence_expr, prop_port_decl);
      ports->emplace_back(prop_port_decl);
      prop_port_decl->setName(fC->SymName(Port_name));
      uhdm::RefTypespec* rtps = s.make<uhdm::RefTypespec>();
      rtps->setActual(tps);
      prop_port_decl->setTypespec(rtps);
      Sequence_port_item = fC->Sibling(Sequence_port_item);
    }
    Sequence_expr = fC->Sibling(Sequence_expr);
  }
  NodeId lookup = fC->Child(Sequence_expr);
  if (fC->Type(lookup) == VObjectType::paClocking_event) {
    uhdm::MulticlockSequenceExpr* mexpr =
        s.make<uhdm::MulticlockSequenceExpr>();
    fC->populateCoreMembers(Sequence_expr, Sequence_expr, mexpr);
    mexpr->setParent(result);
    result->setExpr(mexpr);
    while (fC->Type(lookup) == VObjectType::paClocking_event) {
      uhdm::Expr* clock_event = any_cast<uhdm::Expr*>(compileExpression(
          component, fC, lookup, compileDesign, Reduce::No, result, instance));
      uhdm::ClockedSeq* seq = s.make<uhdm::ClockedSeq>();
      seq->setClockingEvent(clock_event);
      seq->setParent(mexpr);
      fC->populateCoreMembers(lookup, lookup, seq);
      lookup = fC->Sibling(lookup);
    }
    if (uhdm::Any* seq_expr =
            compileExpression(component, fC, lookup, compileDesign, Reduce::No,
                              result, instance)) {
      mexpr->getClockedSeqs(true)->back()->setSequenceExpr(seq_expr);
    }
  } else {
    if (uhdm::Any* seq_expr =
            compileExpression(component, fC, Sequence_expr, compileDesign,
                              Reduce::No, result, instance)) {
      result->setExpr(seq_expr);
    }
  }
  return result;
}

}  // namespace SURELOG
