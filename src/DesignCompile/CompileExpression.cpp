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
#include "ErrorReporting/ErrorContainer.h"

using namespace SURELOG;
using namespace UHDM;

static unsigned long long get_value(bool& invalidValue,
                                    const UHDM::expr* expr) {
  const UHDM::constant* hs = dynamic_cast<const UHDM::constant*>(expr);
  if (hs) {
    s_vpi_value* sval = String2VpiValue(hs->VpiValue());
    if (sval) {
      switch (sval->format) {
        case vpiIntVal: {
          unsigned long long result = sval->value.integer;
          delete sval;
          return result;
        }
        case vpiBinStrVal: {
          std::string val = sval->value.str;
          unsigned long long result = 0;
          StringUtils::ltrim(val, '\'');
          StringUtils::ltrim(val, 'b');
          try {
            result = std::stoull(val, nullptr, 2);
          } catch (...) {
            invalidValue = true;
          }
          delete sval;
          return result;
        }
        case vpiHexStrVal: {
          std::string val = sval->value.str;
          unsigned long long result = 0;
          StringUtils::ltrim(val, '\'');
          StringUtils::ltrim(val, 'h');
          try {
            result = std::stoull(val, nullptr, 16);
          } catch (...) {
            invalidValue = true;
          }
          delete sval;
          return result;
        }
        case vpiOctStrVal: {
          std::string val = sval->value.str;
          unsigned long long result = 0;
          StringUtils::ltrim(val, '\'');
          StringUtils::ltrim(val, 'h');
          try {
            result = std::stoull(val, nullptr, 8);
          } catch (...) {
            invalidValue = true;
          }
          delete sval;
          return result;
        }
        case vpiStringVal: {
          // Don't error out, return 0
          break;
        }
        case vpiScalarVal: {
          unsigned long long result = sval->value.scalar;
          delete sval;
          return result;
        }
        default: {
          invalidValue = true;
          break;
        }
      }
    }
  }
  return 0;
}

UHDM::any* CompileHelper::compileSelectExpression(DesignComponent* component,
                                                  const FileContent* fC,
                                                  NodeId Bit_select,
                                                  const std::string& name,
                                                  CompileDesign* compileDesign,
                                                  UHDM::any* pexpr,
                                                  ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  if ((fC->Type(Bit_select) == slConstant_bit_select) && (!fC->Sibling(Bit_select))) {
    Bit_select = fC->Child(Bit_select);
  } 
  if (fC->Child(Bit_select) && fC->Sibling(Bit_select)) {
    // More than one
    UHDM::var_select* var_select = s.MakeVar_select();
    VectorOfexpr* exprs = s.MakeExprVec();
    var_select->Exprs(exprs);
    var_select->VpiName(name);
    result = var_select;
  }
  while (Bit_select) {
    if (fC->Type(Bit_select) == VObjectType::slBit_select ||
        fC->Type(Bit_select) == VObjectType::slConstant_bit_select ||
        fC->Type(Bit_select) == VObjectType::slConstant_primary ||
        fC->Type(Bit_select) == VObjectType::slConstant_expression) {
      NodeId bitexp = fC->Child(Bit_select);
      if (fC->Type(Bit_select) == VObjectType::slConstant_expression) {
         bitexp = Bit_select;
      }
      if (bitexp) {
        expr* sel = (expr*) compileExpression(component, fC, bitexp, compileDesign, pexpr, instance);

        if (result) {
          UHDM::var_select* var_select = (UHDM::var_select*) result;
          VectorOfexpr* exprs = var_select->Exprs();
          exprs->push_back(sel);
          sel->VpiParent(var_select);
        } else if (fC->Child(Bit_select) && fC->Sibling(Bit_select)) {
          UHDM::var_select* var_select = s.MakeVar_select();
          VectorOfexpr* exprs = s.MakeExprVec();
          var_select->Exprs(exprs);
          var_select->VpiName(name);
          exprs->push_back(sel);
          result = var_select;
          sel->VpiParent(var_select);
        } else {
          bit_select* bit_select = s.MakeBit_select();
          bit_select->VpiName(name);
          bit_select->VpiIndex(sel);
          result = bit_select;
          sel->VpiParent(bit_select);
        }
      }
    } else if (fC->Type(Bit_select) == VObjectType::slPart_select_range ||
               fC->Type(Bit_select) == VObjectType::slConstant_part_select_range) {
      NodeId Constant_range = fC->Child(Bit_select);
      expr* sel = (expr*) compilePartSelectRange(component, fC, Constant_range, name,
                                      compileDesign, pexpr, instance);
      if (result) {
        UHDM::var_select* var_select = (UHDM::var_select*) result;
        VectorOfexpr* exprs = var_select->Exprs();
        exprs->push_back(sel);
        sel->VpiParent(var_select);
      } else if (fC->Child(Bit_select) && fC->Sibling(Bit_select)) {
        UHDM::var_select* var_select = s.MakeVar_select();
        VectorOfexpr* exprs = s.MakeExprVec();
        var_select->Exprs(exprs);
        var_select->VpiName(name);
        exprs->push_back(sel);
        sel->VpiParent(var_select);
      } else {
        result = sel;
      }
    } else if (fC->Type(Bit_select) == VObjectType::slStringConst) {
      std::string hname = name + "." + fC->SymName(Bit_select);
      ref_obj* ref = s.MakeRef_obj();
      ref->VpiName(hname);
      ref->VpiFile(fC->getFileName());
      ref->VpiLineNo(fC->Line(Bit_select));
      result = ref;
      break;
    }
    Bit_select = fC->Sibling(Bit_select);
  }
  return result;
}

UHDM::any* CompileHelper::compileExpression(
  DesignComponent* component, const FileContent* fC, NodeId parent,
  CompileDesign* compileDesign,
  UHDM::any* pexpr,
  ValuedComponentI* instance, bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  VObjectType parentType = fC->Type(parent);
  UHDM::VectorOfattribute* attributes = nullptr;
  if (parentType == VObjectType::slAttribute_instance) {
    attributes = compileAttributes(component, fC, parent, compileDesign);
    while (fC->Type(parent) == slAttribute_instance)
      parent = fC->Sibling(parent);
  }
  parentType = fC->Type(parent);
  NodeId child = fC->Child(parent);
  VObjectType childType = slNull_rule;
  if (child) {
    childType = fC->Type(child);
  }
  if (parentType == VObjectType::slValue_range) {
    UHDM::operation* list_op = s.MakeOperation();
    list_op->VpiOpType(vpiListOp);
    UHDM::VectorOfany* operands = s.MakeAnyVec();
    list_op->Operands(operands);
    NodeId lexpr = child;
    NodeId rexpr = fC->Sibling(lexpr);
    if (expr* op = dynamic_cast<expr*>(compileExpression(component, fC, lexpr, compileDesign, pexpr, instance, reduce))) {
      operands->push_back(op);
    }
    if (rexpr) {
      if (expr* op = dynamic_cast<expr*>(compileExpression(component, fC, rexpr, compileDesign, pexpr, instance, reduce))) {
        operands->push_back(op);
      }
    }
    list_op->VpiFile(fC->getFileName());
    list_op->VpiLineNo(fC->Line(child));
    list_op->Attributes(attributes);
    result = list_op;
    result->VpiFile(fC->getFileName(parent));
    result->VpiLineNo(fC->Line(parent));
    return result;
  } else if (parentType == VObjectType::slNet_lvalue) {
    UHDM::operation* operation = s.MakeOperation();
    UHDM::VectorOfany* operands = s.MakeAnyVec();
    operation->Attributes(attributes);
    result = operation;
    operation->VpiParent(pexpr);
    operation->Operands(operands);
    operation->VpiOpType(vpiConcatOp);
    result->VpiFile(fC->getFileName(parent));
    result->VpiLineNo(fC->Line(parent));
    NodeId Expression = parent;
    while (Expression) {
      UHDM::any* exp = compileExpression(component, fC, fC->Child(Expression),
                                         compileDesign, pexpr, instance, reduce);
      if (exp) {
        operands->push_back(exp);
        exp->VpiParent(operation);
      }
      Expression = fC->Sibling(Expression);
    }
    return result;
  } else if ((parentType == VObjectType::slVariable_lvalue) && (childType == VObjectType::slVariable_lvalue)) {
    UHDM::operation* operation = s.MakeOperation();
    UHDM::VectorOfany* operands = s.MakeAnyVec();
    operation->Attributes(attributes);
    result = operation;
    operation->VpiParent(pexpr);
    operation->Operands(operands);
    operation->VpiOpType(vpiConcatOp);
    result->VpiFile(fC->getFileName(child));
    result->VpiLineNo(fC->Line(child));
    NodeId Expression = child;
    while (Expression) {
      UHDM::any* exp = compileExpression(component, fC, fC->Child(Expression),
                                         compileDesign, pexpr, instance, reduce);
      if (exp) {
        operands->push_back(exp);
        exp->VpiParent(operation);
      }
      Expression = fC->Sibling(Expression);
    }
    return result;
  } else if (childType == VObjectType::slArray_member_label) {
    UHDM::operation* operation = s.MakeOperation();
    UHDM::VectorOfany* operands = s.MakeAnyVec();
    operation->Attributes(attributes);
    result = operation;
    operation->VpiParent(pexpr);
    operation->Operands(operands);
    operation->VpiOpType(vpiConcatOp);
    result->VpiFile(fC->getFileName(child));
    result->VpiLineNo(fC->Line(child));
    NodeId Expression = child;
    bool odd = true;
    while (Expression) {
      NodeId the_exp = fC->Child(Expression);
      if (the_exp == 0) {
        ref_obj* ref = s.MakeRef_obj();
        ref->VpiName("default");
        operands->push_back(ref);
        ref->VpiParent(operation);
        ref->VpiStructMember(true);
      } else {
        UHDM::any* exp = compileExpression(
            component, fC, the_exp, compileDesign, pexpr, instance, reduce);
        if (exp) {
          operands->push_back(exp);
          exp->VpiParent(operation);
          if (odd) {
            if (exp->UhdmType() == uhdmref_obj)
              ((ref_obj*)exp)->VpiStructMember(true);
          }
        }
      }
      Expression = fC->Sibling(Expression);
      odd = !odd;
    }
    return result;
  } else if (parentType == VObjectType::slConcatenation) {
    UHDM::operation* operation = s.MakeOperation();
    UHDM::VectorOfany* operands = s.MakeAnyVec();
    operation->Attributes(attributes);
    result = operation;
    operation->VpiParent(pexpr);
    operation->Operands(operands);
    operation->VpiOpType(vpiConcatOp);
    NodeId Expression = fC->Child(parent);
    while (Expression) {
      UHDM::any* exp = compileExpression(
          component, fC, Expression, compileDesign, pexpr, instance, reduce);
      if (exp) operands->push_back(exp);
      Expression = fC->Sibling(Expression);
    }
    return result;
  } else if (parentType == VObjectType::slDelay2 ||
             parentType == VObjectType::slDelay3) {
    NodeId MinTypMax = child;
    if (fC->Sibling(MinTypMax)) {
      UHDM::operation* operation = s.MakeOperation();
      UHDM::VectorOfany* operands = s.MakeAnyVec();
      operation->Operands(operands);
      operation->VpiOpType(vpiListOp);
      result = operation;
      NodeId Expression = MinTypMax;
      while (Expression) {
        UHDM::any* exp = compileExpression(
          component, fC, Expression, compileDesign, pexpr, instance, reduce);
        if (exp) operands->push_back(exp);
        Expression = fC->Sibling(Expression);
      }
      return result;
    }
  } else if (parentType == VObjectType::slConstant_mintypmax_expression ||
             parentType == VObjectType::slMintypmax_expression) {
    NodeId Expression = child;
    operation* op = s.MakeOperation();
    op->VpiOpType(vpiMinTypMaxOp);
    op->VpiParent(pexpr);
    UHDM::VectorOfany* operands = s.MakeAnyVec();
    op->Operands(operands);
    result = op;
    while (Expression) {
      expr* sExpr = (expr*)compileExpression(
          component, fC, Expression, compileDesign, op, instance, reduce);
      if (sExpr) operands->push_back(sExpr);
      Expression = fC->Sibling(Expression);
    }
    return result;
  } else if (parentType == VObjectType::slClass_new) {
    UHDM::method_func_call* sys = s.MakeMethod_func_call();
    sys->VpiName("new");
    sys->VpiParent(pexpr);
    NodeId argListNode = child;
    VectorOfany* arguments =
        compileTfCallArguments(component, fC, argListNode, compileDesign, sys);
    sys->Tf_call_args(arguments);
    result = sys;
    return result;
  }

  if (child) {
    switch (childType) {
      case VObjectType::slNull_keyword: {
        UHDM::constant* c = s.MakeConstant();
        c->VpiValue("INT:0");
        c->VpiDecompile("0");
        c->VpiSize(32);
        c->VpiConstType(vpiNullConst);
        result = c;
        break;
      }
      case VObjectType::slDollar_keyword: {
        UHDM::constant* c = s.MakeConstant();
        c->VpiConstType(vpiUnboundedConst);
        c->VpiValue("STRING:$");
        c->VpiDecompile("$");
        result = c;
        break;
      }
      case VObjectType::slThis_keyword: {
        UHDM::constant* c = s.MakeConstant();
        c->VpiValue("STRING:this");
        c->VpiDecompile("this");
        result = c;
        break;
      }
      case VObjectType::slSuper_keyword: {
        UHDM::constant* c = s.MakeConstant();
        c->VpiValue("STRING:super");
        c->VpiDecompile("super");
        result = c;
        break;
      }
      case VObjectType::slThis_dot_super: {
        UHDM::constant* c = s.MakeConstant();
        c->VpiValue("STRING:this.super");
        c->VpiDecompile("this.super");
        result = c;
        break;
      }
      case VObjectType::slIncDec_PlusPlus:
      case VObjectType::slIncDec_MinusMinus:
      case VObjectType::slUnary_Minus:
      case VObjectType::slUnary_Plus:
      case VObjectType::slUnary_Tilda:
      case VObjectType::slUnary_Not:
      case VObjectType::slNOT:
      case VObjectType::slUnary_BitwOr:
      case VObjectType::slUnary_BitwAnd:
      case VObjectType::slUnary_BitwXor:
      case VObjectType::slUnary_ReductNand:
      case VObjectType::slUnary_ReductNor:
      case VObjectType::slUnary_ReductXnor1:
      case VObjectType::slUnary_ReductXnor2: {
        unsigned int vopType = UhdmWriter::getVpiOpType(childType);
        if (vopType) {
          UHDM::operation* op = s.MakeOperation();
          op->VpiOpType(vopType);
          op->VpiParent(pexpr);
          op->Attributes(attributes);
          UHDM::VectorOfany* operands = s.MakeAnyVec();
          if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(child),
                                                   compileDesign, op, instance, reduce)) {
            operands->push_back(operand);
          }
          op->Operands(operands);
          result = op;
        }
        break;
      }
      case VObjectType::slEdge_Posedge: {
        UHDM::operation* op = s.MakeOperation();
        op->Attributes(attributes);
        op->VpiOpType(vpiPosedgeOp);
        op->VpiParent(pexpr);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(child),
                                                   compileDesign, op, instance, reduce))
          operands->push_back(operand);
        op->Operands(operands);
        result = op;
        break;
      }
      case VObjectType::slEdge_Edge: {
        UHDM::operation* op = s.MakeOperation();
        op->Attributes(attributes);
        op->VpiOpType(vpiAnyEdge);
        op->VpiParent(pexpr);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(child),
                                                   compileDesign, op, instance, reduce))
          operands->push_back(operand);
        op->Operands(operands);
        result = op;
        break;
      }
      case VObjectType::slEdge_Negedge: {
        UHDM::operation* op = s.MakeOperation();
        op->Attributes(attributes);
        op->VpiOpType(vpiNegedgeOp);
        op->VpiParent(pexpr);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(child),
                                                   compileDesign, op, instance, reduce))
          operands->push_back(operand);
        op->Operands(operands);
        result = op;
        break;
      }
      case VObjectType::slImplicit_class_handle:
      case VObjectType::slInc_or_dec_expression:
      case VObjectType::slConstant_primary:
      case VObjectType::slPrimary_literal:
      case VObjectType::slPrimary:
      case VObjectType::slSystem_task:
      case VObjectType::slParam_expression:
      case VObjectType::slExpression_or_cond_pattern:
      case VObjectType::slConstant_param_expression:
      case VObjectType::slAssignment_pattern_expression:
      case VObjectType::slConstant_assignment_pattern_expression:
      case VObjectType::slExpression_or_dist:
        result = compileExpression(component, fC, child, compileDesign, pexpr, instance, reduce);
        break;
      case VObjectType::slComplex_func_call: {
        result = compileComplexFuncCall(component, fC, child, compileDesign, pexpr, instance, reduce);
        break;
      }
      case VObjectType::slDot: {
        NodeId Identifier = fC->Sibling(child);
        ref_obj* ref = s.MakeRef_obj();
        ref->VpiName(fC->SymName(Identifier));
        result = ref;
        break;
      }
      case VObjectType::slConstant_mintypmax_expression:
      case VObjectType::slMintypmax_expression: {
        NodeId Expression = fC->Child(child);
        NodeId Sibling = fC->Sibling(Expression);
        if (Sibling) {
          operation* op = s.MakeOperation();
          op->VpiOpType(vpiMinTypMaxOp);  
          op->VpiParent(pexpr);
          UHDM::VectorOfany* operands = s.MakeAnyVec();
          op->Operands(operands);
          result = op;
          expr* cExpr = (expr*) compileExpression(component, fC, Expression, compileDesign, op, instance, reduce);
          if (cExpr)
            operands->push_back(cExpr);
          while (Sibling) {
            expr* sExpr = (expr*) compileExpression(component, fC, Sibling, compileDesign, op, instance, reduce);
            if (sExpr)
              operands->push_back(sExpr);
            Sibling = fC->Sibling(Sibling);  
          }  
        } else {
          result = (expr*) compileExpression(component, fC, Expression, compileDesign, pexpr, instance, reduce);
        }
        break;
      }
      case VObjectType::slRandomize_call: {
        result = compileRandomizeCall(component, fC, fC->Child(child), compileDesign, pexpr);
        break;
      }
      case VObjectType::slPattern: {
        NodeId Sibling = fC->Sibling(child);
        if (Sibling) {
          operation* op = s.MakeOperation();
          op->VpiOpType(vpiListOp);  
          op->VpiParent(pexpr);
          UHDM::VectorOfany* operands = s.MakeAnyVec();
          op->Operands(operands);
          result = op;
          expr* cExpr = (expr*) compileExpression(component, fC, fC->Child(child), compileDesign, op, instance, reduce);
          if (cExpr)
            operands->push_back(cExpr);
          while (Sibling) {
            expr* sExpr = (expr*) compileExpression(component, fC, Sibling, compileDesign, op, instance, reduce);
            if (sExpr)
              operands->push_back(sExpr);
            Sibling = fC->Sibling(Sibling);  
          }  
        } else {
          result = (expr*) compileExpression(component, fC, fC->Child(child), compileDesign, pexpr, instance, reduce);
        }
        break;
      }
      case VObjectType::slTagged: {
        NodeId Identifier = fC->Sibling(child);
        NodeId Expression = fC->Sibling(Identifier);
        UHDM::tagged_pattern* pattern = s.MakeTagged_pattern();
        pattern->VpiName(fC->SymName(Identifier));
        if (Expression)
          pattern->Pattern(compileExpression(component, fC, Expression, compileDesign, pattern, instance, reduce)); 
        result = pattern;
        break;
      }
      case VObjectType::slEvent_expression: {
        NodeId subExpr = child;
        UHDM::any* opL =
            compileExpression(component, fC, subExpr, compileDesign, pexpr, instance, reduce);
        result = opL;
        NodeId op = fC->Sibling(subExpr);
        UHDM::operation* operation = nullptr;
        UHDM::VectorOfany* operands = nullptr;
        while (op) {
          if (operation == nullptr) {
            operation = s.MakeOperation();
            operation->Attributes(attributes);
            operands = s.MakeAnyVec();
            operation->Operands(operands);
            operands->push_back(opL);
            result = operation;
          }
          if (fC->Type(op) == VObjectType::slOr_operator) {
            operation->VpiOpType(vpiEventOrOp);
            NodeId subRExpr = fC->Sibling(op);
            UHDM::any* opR =
                compileExpression(component, fC, subRExpr, compileDesign, pexpr, instance, reduce);
            operands->push_back(opR);
            op = fC->Sibling(subRExpr);
          } else if (fC->Type(op) == VObjectType::slComma_operator) {
            operation->VpiOpType(vpiListOp);
            NodeId subRExpr = fC->Sibling(op);
            UHDM::any* opR =
                compileExpression(component, fC, subRExpr, compileDesign, pexpr, instance, reduce);
            operands->push_back(opR);
            op = fC->Sibling(subRExpr);
          }
        }
        break;
      }
      case VObjectType::slExpression:
      case VObjectType::slConstant_expression: {
        UHDM::any* opL =
            compileExpression(component, fC, child, compileDesign, pexpr, instance, reduce);
        NodeId op = fC->Sibling(child);
        if (!op) {
          result = opL;
          break;
        }
        UHDM::operation* operation = s.MakeOperation();
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        result = operation;
        operation->VpiParent(pexpr);
        operation->Attributes(attributes);
        if (opL) {
          setParentNoOverride(opL, operation);
          operands->push_back(opL);
        }
        VObjectType opType = fC->Type(op);
        unsigned int vopType = UhdmWriter::getVpiOpType(opType);
        if (vopType == 0) {
          result = nullptr;
        }
        operation->VpiOpType(vopType);

        operation->Operands(operands);
        NodeId rval = fC->Sibling(op);

        if (fC->Type(rval) == VObjectType::slAttribute_instance) {
          UHDM::VectorOfattribute* attributes = compileAttributes(component, fC, rval, compileDesign);
          while (fC->Type(rval) == slAttribute_instance)
          rval = fC->Sibling(rval);
          operation->Attributes(attributes);
        }

        if (opType == VObjectType::slInsideOp) {
          // Because open_range_list is stored in { }, it is being interpreted
          // as a concatenation operation. Code below constructs it manually.
          // Example tree:
          //n<> u<164> t<InsideOp> p<180> s<179> l<9>
          //n<> u<179> t<Expression> p<180> c<178> l<9>
          //    n<> u<178> t<Primary> p<179> c<177> l<9>
          //        n<> u<177> t<Concatenation> p<178> c<168> l<9>
          //            n<> u<168> t<Expression> p<177> c<167> s<172> l<9>
          //                n<> u<167> t<Primary> p<168> c<166> l<9>
          //                    n<> u<166> t<Primary_literal> p<167> c<165> l<9>
          //                        n<OP_1> u<165> t<StringConst> p<166> l<9>
          //            n<> u<172> t<Expression> p<177> c<171> s<176> l<10>
          //                n<> u<171> t<Primary> p<172> c<170> l<10>
          //                    n<> u<170> t<Primary_literal> p<171> c<169> l<10>
          //                        n<OP_2> u<169> t<StringConst> p<170> l<10>
          //            n<> u<176> t<Expression> p<177> c<175> l<11>
          //                n<> u<175> t<Primary> p<176> c<174> l<11>
          //                    n<> u<174> t<Primary_literal> p<175> c<173> l<11>
          //                        n<OP_3> u<173> t<StringConst> p<174> l<11>
          NodeId false_concat = fC->Child(fC->Child(rval));
          NodeId Expression = fC->Child(false_concat);
          // Open range list members
          while (Expression) {
            UHDM::any* exp = compileExpression(component, fC, Expression, compileDesign, pexpr, instance, reduce);
            if (exp)
              operands->push_back(exp);
            Expression = fC->Sibling(Expression);
          }
          // RHS is done, skip handling below
          break;
        } else if (opType == VObjectType::slOpen_range_list) {
          NodeId Value_range = fC->Child(op);
          NodeId Expression = fC->Child(Value_range);
          while (Expression) {
            UHDM::any* exp = compileExpression(component, fC, Expression, compileDesign, pexpr, instance, reduce);
            if (exp)
              operands->push_back(exp);
            Expression = fC->Sibling(Expression);
          }
          // RHS is done, skip handling below
          break;
        }

        UHDM::any* opR =
            compileExpression(component, fC, rval, compileDesign, operation, instance, reduce);
        if (opR) {
          setParentNoOverride(opR, operation);
          operands->push_back(opR);
        }
        if (opType == VObjectType::slQmark ||
            opType == VObjectType::slConditional_operator) { // Ternary op
          rval = fC->Sibling(rval);
          opR =
            compileExpression(component, fC, rval, compileDesign, operation, instance, reduce);
          if (opR) {
            setParentNoOverride(opR, operation);  
            operands->push_back(opR);
          }
        }
        break;
      }
      case VObjectType::slSystem_task_names: {
        // Node example:
        // n<> u<23> t<System_task_names> p<29> c<22> s<28> l<2>
        //     n<$unsigned> u<22> t<StringConst> p<23> l<2>
        // n<> u<28> t<List_of_arguments> p<29> c<27> l<2>
        //     n<> u<27> t<Expression> p<28> c<26> l<2>
        //         n<> u<26> t<Primary> p<27> c<25> l<2>
        //             n<> u<25> t<Primary_literal> p<26> c<24> l<2>
        //                 n<a> u<24> t<StringConst> p<25> l<2>

        NodeId n = fC->Child(child);
        const std::string& name = fC->SymName(n);
        if (name == "$bits") {
          NodeId List_of_arguments = fC->Sibling(child);
          result = compileBits(component, fC, List_of_arguments, compileDesign,
                               pexpr, instance, reduce);
        } else if (name == "$clog2") {
          NodeId List_of_arguments = fC->Sibling(child);
          result = compileClog2(component, fC, List_of_arguments, compileDesign, pexpr, instance, reduce);
        } else if (name == "$typename") {
          NodeId List_of_arguments = fC->Sibling(child);
          result = compileTypename(component, fC, List_of_arguments, compileDesign, pexpr, instance, reduce);
        } else {
          UHDM::sys_func_call* sys = s.MakeSys_func_call();
          sys->VpiName(name);
          sys->VpiParent(pexpr);
          NodeId argListNode = fC->Sibling(child);
          VectorOfany* arguments =
              compileTfCallArguments(component, fC, argListNode, compileDesign, sys);
          sys->Tf_call_args(arguments);
          result = sys;
        }
        break;
      }
      case VObjectType::slVariable_lvalue: {
        UHDM::any* variable =
            compileExpression(component, fC, child, compileDesign, pexpr, instance, reduce);
        NodeId op = fC->Sibling(child);
        if (op) {
          VObjectType opType = fC->Type(op);
          unsigned int vopType = UhdmWriter::getVpiOpType(opType);
          if (vopType) {
            // Post increment/decrement
            UHDM::operation* operation = s.MakeOperation();
            UHDM::VectorOfany* operands = s.MakeAnyVec();
            operation->Attributes(attributes);
            result = operation;
            operation->VpiParent(pexpr);
            operation->VpiOpType(vopType);
            operation->Operands(operands);
            operands->push_back(variable);

            NodeId rval = fC->Sibling(op);
            if (fC->Type(rval) == VObjectType::slAttribute_instance) {
              UHDM::VectorOfattribute* attributes = compileAttributes(component, fC, rval, compileDesign);
              while (fC->Type(rval) == slAttribute_instance)
              rval = fC->Sibling(rval);
              operation->Attributes(attributes);
            }

          } else if (opType == slExpression) {
            // Assignment
            UHDM::operation* operation = s.MakeOperation();
            UHDM::VectorOfany* operands = s.MakeAnyVec();
            operation->Attributes(attributes);
            result = operation;
            operation->VpiParent(pexpr);
            operation->VpiOpType(vpiAssignmentOp);
            operation->Operands(operands);
            operands->push_back(variable);

            NodeId rval = op;
            if (fC->Type(rval) == VObjectType::slAttribute_instance) {
              UHDM::VectorOfattribute* attributes = compileAttributes(component, fC, rval, compileDesign);
              while (fC->Type(rval) == slAttribute_instance)
              rval = fC->Sibling(rval);
              operation->Attributes(attributes);
            }

            UHDM::any* rexp =
            compileExpression(component, fC, rval, compileDesign, pexpr, instance, reduce);
            operands->push_back(rexp);

          }
        } else {
          result = variable;
        }
        break;
      }
      case VObjectType::slAssignment_pattern: {
        result = compileAssignmentPattern(component, fC, child, compileDesign, pexpr, instance);
        break;
      }
      case VObjectType::slSequence_expr: {
        if (fC->Sibling(parent) == 0) {
          result = compileExpression(component, fC, child, compileDesign,
                                nullptr, instance, reduce);
        } else {
          
        }
        break;
      }
      case VObjectType::slConstant_cast:
      case VObjectType::slCast: {
        NodeId Casting_type = fC->Child(child);
        NodeId Simple_type = fC->Child(Casting_type);
        UHDM::any* operand = nullptr;
        if (Casting_type) {
          NodeId Expression = fC->Sibling(Casting_type);
          operand =
              compileExpression(component, fC, Expression, compileDesign,
                                nullptr, instance, reduce);
        }
        if ((fC->Type(Simple_type) == slSigning_Unsigned) || 
            (fC->Type(Simple_type) == slSigning_Signed)) {
          UHDM::sys_func_call* sys = s.MakeSys_func_call();
          if (fC->Type(Simple_type) == slSigning_Unsigned) 
            sys->VpiName("$unsigned");
          else 
            sys->VpiName("$signed");
          sys->VpiParent(pexpr);
          VectorOfany* arguments = s.MakeAnyVec();
          sys->Tf_call_args(arguments);
          if (operand) {
            arguments->push_back(operand);
            operand->VpiParent(sys);
          }
          result = sys;
        } else {
          UHDM::operation* operation = s.MakeOperation();
          UHDM::VectorOfany* operands = s.MakeAnyVec();
          operation->Attributes(attributes);
          operation->Operands(operands);
          operation->VpiOpType(vpiCastOp);
          UHDM::typespec* tps =
              compileTypespec(component, fC, Simple_type, compileDesign,
                              operation, instance, reduce);
          if (operand) {
            setParentNoOverride(operand, operation);
            operands->push_back(operand);
          }
          operation->Typespec(tps);
          result = operation;
        }
        break;
      }
      case VObjectType::slPackage_scope:
      case VObjectType::slClass_type:
      case VObjectType::slHierarchical_identifier:
      case VObjectType::slStringConst: {
        std::string name;
        Value* sval = NULL;
        if (childType == VObjectType::slPackage_scope) {
          const std::string& packageName = fC->SymName(fC->Child(child));
          const std::string& n = fC->SymName(fC->Sibling(child));
          name = packageName + "::" + n;
          Package* pack = compileDesign->getCompiler()->getDesign()->getPackage(packageName);
          if (pack) {
            UHDM::VectorOfparam_assign* param_assigns= pack->getParam_assigns();
            if (param_assigns) {
              for (param_assign* param : *param_assigns) {
                const std::string& param_name = param->Lhs()->VpiName();
                if (param_name == n) {
                  ElaboratorListener listener(&s);
                  result = UHDM::clone_tree((any*) param->Rhs(), s, &listener);
                  break;
                }
              }
            }
            if (result == nullptr)
              sval = pack->getValue(n);
          }
        } else if (childType == VObjectType::slClass_type) {
          const std::string& packageName = fC->SymName(fC->Child(child));
          const std::string& n = fC->SymName(fC->Sibling(parent));
          name = packageName + "::" + n;
          Package* pack = compileDesign->getCompiler()->getDesign()->getPackage(packageName);
          if (pack) {
            UHDM::VectorOfparam_assign* param_assigns= pack->getParam_assigns();
            if (param_assigns) {
              for (param_assign* param : *param_assigns) {
                const std::string& param_name = param->Lhs()->VpiName();
                if (param_name == n) {
                  ElaboratorListener listener(&s);
                  result = UHDM::clone_tree((any*) param->Rhs(), s, &listener);
                  break;
                }
              }
            }
            if (result == nullptr)
              sval = pack->getValue(n);
          }
        } else {
          NodeId rhs;
          if (parentType == VObjectType::slHierarchical_identifier ||
              parentType == VObjectType::slPs_or_hierarchical_identifier) {
            rhs = parent;
          } else {
            rhs = child;
          }
          if (fC->Name(child))
            name = fC->SymName(child);
          else {
            NodeId tmp = fC->Child(child);
            if (fC->Type(tmp) == VObjectType::slDollar_root_keyword) {
              tmp = fC->Sibling(tmp);
            }
            name = fC->SymName(tmp);
          }
          while ((rhs = fC->Sibling(rhs))) {
            if (fC->Type(rhs) == VObjectType::slStringConst) {
              name += "." + fC->SymName(rhs);
            } else if (fC->Type(rhs) == VObjectType::slSelect ||
                       fC->Type(rhs) == VObjectType::slConstant_select) {
              NodeId Bit_select = fC->Child(rhs);
              result = compileSelectExpression(component, fC, Bit_select, name, compileDesign, pexpr, instance);
            }
            if (result)
              break;
          }
          if (instance)
            sval = instance->getValue(name);
        }
        if (result)
          break;

        if (sval == NULL) {
          if (component && reduce) {
            UHDM::VectorOfparam_assign* param_assigns= component->getParam_assigns();
            if (param_assigns) {
              for (param_assign* param : *param_assigns) {
                const std::string& param_name = param->Lhs()->VpiName();
                if (param_name == name) {
                  ElaboratorListener listener(&s);
                  result = UHDM::clone_tree((any*) param->Rhs(), s, &listener);
                  break;
                }
              }
            }
          }
          if (result == nullptr) {
            UHDM::ref_obj* ref = s.MakeRef_obj();
            ref->VpiName(name);
            ref->VpiParent(pexpr);
            if (pexpr) {
              UHDM::any* var = bindVariable(component, pexpr, name, compileDesign);
              if (var)
                ref->Actual_group(var);
              else if (component)
                component->needLateBinding(ref); 
            }
            result = ref;
          }
        } else {
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue(sval->uhdmValue());
          c->VpiDecompile(sval->decompiledValue());
          result = c;
        }
        break;
      }
      case VObjectType::slIntConst: {
        // Do not evaluate the constant, keep it as in the source text:
        UHDM::constant* c = s.MakeConstant();
        const std::string& value = fC->SymName(child);
        std::string v;
        c->VpiDecompile(value);
        if (strstr(value.c_str(), "'")) {
          char base = 'h';
          unsigned int i = 0;
          for (i = 0; i < value.size(); i++) {
            if (value[i] == '\'') {
              base = value[i + 1];
              break;
            }
          }
          v = value.substr(i + 2);
          v = StringUtils::replaceAll(v, "_", "");
          switch (base) {
          case 'h': {
            std::string size = value;
            StringUtils::rtrim(size, '\'');
            c->VpiSize(atoi(size.c_str()));
            v = "HEX:" + v;
            c->VpiConstType(vpiHexConst);
            break;
          }
          case 'b': {
            std::string size = value;
            StringUtils::rtrim(size, '\'');
            c->VpiSize(atoi(size.c_str()));
            v = "BIN:" + v;
            c->VpiConstType(vpiBinaryConst);
            break;
          }
          case 'o': {
            std::string size = value;
            StringUtils::rtrim(size, '\'');
            c->VpiSize(atoi(size.c_str()));
            v = "OCT:" + v;
            c->VpiConstType(vpiOctConst);
            break;
          }
          case 'd': {
            std::string size = value;
            StringUtils::rtrim(size, '\'');
            c->VpiSize(atoi(size.c_str()));
            v = "INT:" + v;
            c->VpiConstType(vpiIntConst);
            break;
          }  
          default: {
            v = "BIN:" + v;
            c->VpiConstType(vpiBinaryConst);
            break;
          }
          }

        } else {
          v = "INT:" + value;
          c->VpiSize(32);
          c->VpiConstType(vpiIntConst);
        }
        
        c->VpiValue(v);
        result = c;
        break;
      }
      case VObjectType::slRealConst: {
        UHDM::constant* c = s.MakeConstant();
        std::string value = fC->SymName(child);
        c->VpiDecompile(value);
        value = "REAL:" + value;
        c->VpiValue(value);
        c->VpiConstType(vpiRealConst);
        result = c;
        break;
      }
      case VObjectType::slNumber_1Tickb1:
      case VObjectType::slNumber_1TickB1:
      case VObjectType::slInitVal_1Tickb1:
      case VObjectType::slInitVal_1TickB1:
      case VObjectType::slScalar_1Tickb1:
      case VObjectType::slScalar_1TickB1:
      case VObjectType::slScalar_Tickb1:
      case VObjectType::slScalar_TickB1:
      case VObjectType::sl1: {
        UHDM::constant* c = s.MakeConstant();
        std::string value = "BIN:1";
        c->VpiValue(value);
        c->VpiConstType(vpiBinaryConst);
        c->VpiSize(1);
        c->VpiDecompile("'b1");
        result = c;
        break;
      }
      case VObjectType::slNumber_Tickb1:
      case VObjectType::slNumber_TickB1:
      case VObjectType::slNumber_Tick1:
      {
        UHDM::constant* c = s.MakeConstant();
        std::string value = "BIN:1";
        c->VpiValue(value);
        c->VpiConstType(vpiBinaryConst);
        c->VpiSize(0);
        c->VpiDecompile("'b1");
        result = c;
        break;
      }
      case VObjectType::slNumber_1Tickb0:
      case VObjectType::slNumber_1TickB0:
      case VObjectType::slInitVal_1Tickb0:
      case VObjectType::slInitVal_1TickB0:
      case VObjectType::slScalar_1Tickb0:
      case VObjectType::slScalar_1TickB0:
      case VObjectType::slScalar_Tickb0:
      case VObjectType::slScalar_TickB0:
      case VObjectType::sl0: {
        UHDM::constant* c = s.MakeConstant();
        std::string value = "BIN:0";
        c->VpiValue(value);
        c->VpiConstType(vpiBinaryConst);
        c->VpiSize(1);
        c->VpiDecompile("'b0");
        result = c;
        break;
      }
      case VObjectType::slNumber_Tickb0:
      case VObjectType::slNumber_TickB0:
      case VObjectType::slNumber_Tick0:
      {
        UHDM::constant* c = s.MakeConstant();
        std::string value = "BIN:0";
        c->VpiValue(value);
        c->VpiConstType(vpiBinaryConst);
        c->VpiSize(0);
        c->VpiDecompile("'b0");
        result = c;
        break;
      }
      case VObjectType::slNumber_1TickBX:
      case VObjectType::slNumber_1TickbX:
      case VObjectType::slNumber_1Tickbx:
      case VObjectType::slNumber_1TickBx:
      case VObjectType::slInitVal_1Tickbx:
      case VObjectType::slInitVal_1TickbX:
      case VObjectType::slInitVal_1TickBx:
      case VObjectType::slInitVal_1TickBX:
      case VObjectType::slX: {
        UHDM::constant* c = s.MakeConstant();
        std::string value = "BIN:X";
        c->VpiValue(value);
        c->VpiConstType(vpiBinaryConst);
        c->VpiSize(1);
        c->VpiDecompile("'bX");
        result = c;
        break;
      }
      case VObjectType::slZ: {
        UHDM::constant* c = s.MakeConstant();
        std::string value = "BIN:z";
        c->VpiValue(value);
        c->VpiConstType(vpiBinaryConst);
        c->VpiSize(1);
        c->VpiDecompile("'bz");
        result = c;
        break;
      }
      case VObjectType::slTime_literal: {
        // TODO:
        UHDM::constant* c = s.MakeConstant();
        std::string value = "BIN:0";
        c->VpiValue(value);
        c->VpiConstType(vpiBinaryConst);
        c->VpiSize(1);
        c->VpiDecompile("'b0");
        result = c;
        break;
      }
      case VObjectType::slStringLiteral: {
        UHDM::constant* c = s.MakeConstant();
        std::string value = fC->SymName(child);
        if (value.front() == '"' && value.back() == '"')
          value = value.substr(1, value.length() - 2);
        c->VpiDecompile(value);
        c->VpiSize(strlen(value.c_str()));
        value = "STRING:" + value;
        c->VpiValue(value);
        c->VpiConstType(vpiStringConst);
        result = c;
        break;
      }
      case VObjectType::slStreaming_concatenation: {
        NodeId Stream_operator = fC->Child(child);
        NodeId Stream_direction = fC->Child(Stream_operator);
        NodeId Slice_size = fC->Sibling(Stream_operator);
        UHDM::any* exp_slice = nullptr;
        NodeId Stream_concatenation = 0;
        if (fC->Type(Slice_size) == slSlice_size) {
          NodeId Constant_expression = fC->Child(Slice_size);
          if (fC->Type(Constant_expression) == slSimple_type) {
            NodeId Integer_type = fC->Child(Constant_expression);
            NodeId Type = fC->Child(Integer_type);
            exp_slice = compileBits(component, fC, Type,
                                    compileDesign, pexpr, instance, true);
          } else {
            exp_slice = compileExpression(component, fC, Constant_expression, compileDesign, pexpr, instance, reduce);
          }
          Stream_concatenation = fC->Sibling(Slice_size);
        } else {
          Stream_concatenation = Slice_size;
        }

        NodeId Stream_expression = fC->Child(Stream_concatenation);
        NodeId Expression = fC->Child(Stream_expression);
        UHDM::operation* operation = s.MakeOperation();
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        operation->Attributes(attributes);
        result = operation;
        operation->VpiParent(pexpr);
        operation->Operands(operands);
        if (fC->Type(Stream_direction) == VObjectType::slBinOp_ShiftRight)
          operation->VpiOpType(vpiStreamLROp);
        else
          operation->VpiOpType(vpiStreamRLOp);

        if (exp_slice)
          operands->push_back(exp_slice);
        UHDM::any* exp_var = compileExpression(component, fC, Expression, compileDesign, pexpr, instance, reduce);
        if (exp_var)
          operands->push_back(exp_var);
        break;
      }
      case VObjectType::slEmpty_queue: {
        UHDM::array_var* var = s.MakeArray_var();
        var->VpiArrayType(vpiQueueArray);
        result = var;
        break;
      }
      case VObjectType::slConstant_concatenation:
      case VObjectType::slConcatenation: {
        UHDM::operation* operation = s.MakeOperation();
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        operation->Attributes(attributes);
        result = operation;
        operation->VpiParent(pexpr);
        operation->Operands(operands);
        operation->VpiOpType(vpiConcatOp);
        NodeId Expression = fC->Child(child);
        while (Expression) {
          UHDM::any* exp = compileExpression(component, fC, Expression, compileDesign, pexpr, instance, reduce);
          if (exp)
            operands->push_back(exp);
          Expression = fC->Sibling(Expression);
        }
        break;
      }
      case VObjectType::slConstant_multiple_concatenation:
      case VObjectType::slMultiple_concatenation: {
        UHDM::operation* operation = s.MakeOperation();
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        operation->Attributes(attributes);
        result = operation;
        operation->VpiParent(pexpr);
        operation->Operands(operands);
        operation->VpiOpType(vpiMultiConcatOp);
        NodeId Expression = fC->Child(child);
        while (Expression) {
          UHDM::any* exp = compileExpression(component, fC, Expression, compileDesign, pexpr, instance, reduce);
          if (exp)
            operands->push_back(exp);
          Expression = fC->Sibling(Expression);
        }
        break;
      }
      case VObjectType::slSubroutine_call: {
        NodeId Dollar_keyword = fC->Child(child);
        NodeId nameId = fC->Sibling(Dollar_keyword);
        const std::string& name = fC->SymName(nameId);
        if (name == "bits") {
          NodeId List_of_arguments = fC->Sibling(nameId);
          NodeId Expression = fC->Child(List_of_arguments);
          result = compileBits(component, fC, Expression, compileDesign, pexpr, instance, reduce);
        } else if (name == "clog2") {
          NodeId List_of_arguments = fC->Sibling(nameId);
          result = compileClog2(component, fC, List_of_arguments, compileDesign, pexpr, instance, reduce);
        } else if (name == "typename") {
          NodeId List_of_arguments = fC->Sibling(nameId);
          result = compileTypename(component, fC, List_of_arguments, compileDesign, pexpr, instance, reduce);
        } else {
          NodeId List_of_arguments = fC->Sibling(nameId);
          UHDM::sys_func_call* sys = s.MakeSys_func_call();
          sys->VpiName("$" + name);
          VectorOfany *arguments = compileTfCallArguments(component, fC, List_of_arguments, compileDesign, sys);
          sys->Tf_call_args(arguments);
          result = sys;
        }
        break;
      }
      default:
        break;
    }
  } else {
    VObjectType type = fC->Type(parent);
    switch (type) {
      case VObjectType::slIncDec_PlusPlus:
      case VObjectType::slIncDec_MinusMinus:
      case VObjectType::slUnary_Minus:
      case VObjectType::slUnary_Plus:
      case VObjectType::slUnary_Tilda:
      case VObjectType::slUnary_Not:
      case VObjectType::slUnary_BitwOr:
      case VObjectType::slUnary_BitwAnd:
      case VObjectType::slUnary_BitwXor:
      case VObjectType::slUnary_ReductNand:
      case VObjectType::slUnary_ReductNor:
      case VObjectType::slUnary_ReductXnor1:
      case VObjectType::slUnary_ReductXnor2: {
        unsigned int vopType = UhdmWriter::getVpiOpType(type);
        if (vopType) {
          UHDM::operation* op = s.MakeOperation();
          op->Attributes(attributes);
          op->VpiOpType(vopType);
          op->VpiParent(pexpr);
          UHDM::VectorOfany* operands = s.MakeAnyVec();
          if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(parent),
                                                   compileDesign, op, instance, reduce)) {
            operands->push_back(operand);
          }
          op->Operands(operands);
          result = op;
        }
        break;
      }
      case VObjectType::slNull_keyword: {
        UHDM::constant* c = s.MakeConstant();
        c->VpiValue("INT:0");
        c->VpiDecompile("0");
        c->VpiSize(32);
        c->VpiConstType(vpiNullConst);
        result = c;
        break;
      }
      case VObjectType::slDollar_keyword: {
        UHDM::constant* c = s.MakeConstant();
        c->VpiConstType(vpiUnboundedConst);
        c->VpiValue("STRING:$");
        c->VpiDecompile("$");
        result = c;
        break;
      }
      case VObjectType::slThis_keyword: {
        // TODO: To be changed to class var
        UHDM::constant* c = s.MakeConstant();
        c->VpiValue("STRING:this");
        c->VpiDecompile("this");
        result = c;
        break;
      }
      case VObjectType::slSuper_keyword: {
         // TODO: To be changed to class var
        UHDM::constant* c = s.MakeConstant();
        c->VpiValue("STRING:super");
        c->VpiDecompile("super");
        result = c;
        break;
      }
      case VObjectType::slThis_dot_super: {
         // TODO: To be changed to class var
        UHDM::constant* c = s.MakeConstant();
        c->VpiValue("STRING:this.super");
        c->VpiDecompile("this.super");
        result = c;
        break;
      }
      case VObjectType::slConstraint_block: {
        // Empty constraint block
        UHDM::constraint* cons = s.MakeConstraint();
        result = cons;
        break;
      }
      case VObjectType::slStringConst: {
        std::string name = fC->SymName(parent).c_str();
        NodeId dotedName = fC->Sibling(parent);
        if (fC->Type(dotedName) == VObjectType::slStringConst) {
          name += "." + fC->SymName(dotedName);
        }
        Value* sval = NULL;
        if (instance) sval = instance->getValue(name);
        if (sval == NULL) {
          NodeId op = fC->Sibling(parent);
          if (op && (fC->Type(op) != VObjectType::slStringConst) && (fC->Type(op) != VObjectType::slExpression)) {
            VObjectType opType = fC->Type(op);
            unsigned int vopType = UhdmWriter::getVpiOpType(opType);
            if (vopType) {
              UHDM::operation* operation = s.MakeOperation();
              operation->Attributes(attributes);
              UHDM::VectorOfany* operands = s.MakeAnyVec();
              result = operation;
              operation->VpiParent(pexpr);
              operation->VpiOpType(vopType);
              operation->Operands(operands);
              UHDM::ref_obj* ref = s.MakeRef_obj();
              ref->VpiName(name);
              ref->VpiParent(operation);
              operands->push_back(ref);
            }
          } else {
            UHDM::ref_obj* ref = s.MakeRef_obj();
            ref->VpiName(name);
            ref->VpiParent(pexpr);
            result = ref;
          }
        } else {
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue(sval->uhdmValue());
          c->VpiDecompile(sval->decompiledValue());
          result = c;
        }
        break;
      }
      default:
        break;
    }
  }

  NodeId the_node = 0;
  if (child) {
    the_node = child;
  } else {
    the_node = parent;
  }
  if (result == nullptr) {
    VObjectType exprtype = fC->Type(the_node);
    if ((exprtype != VObjectType::slEnd)) {
      ErrorContainer* errors = compileDesign->getCompiler()->getErrorContainer();
      SymbolTable* symbols = compileDesign->getCompiler()->getSymbolTable();
      unsupported_expr* exp = s.MakeUnsupported_expr();
      std::string fileContent = FileUtils::getFileContent(fC->getFileName());
      std::string lineText = StringUtils::getLineInString(fileContent, fC->Line(the_node));
      Location loc (symbols->registerSymbol(fC->getFileName(the_node)), fC->Line(the_node), 0 ,
                    symbols->registerSymbol(std::string("<")+ fC->printObject(the_node) + std::string("> ") + lineText));
      Error err(ErrorDefinition::UHDM_UNSUPPORTED_EXPR, loc);
      errors->addError(err);
      exp->VpiValue("STRING:" + lineText);
      exp->VpiFile(fC->getFileName(the_node));
      exp->VpiLineNo(fC->Line(the_node));
      exp->VpiParent(pexpr);
      result = exp;
    }
  }

  if ((result != nullptr) && reduce) {

    // Reduce
    if (result->UhdmType() == uhdmoperation) {
      operation* op = (operation*) result;
      VectorOfany* operands = op->Operands();
      bool constantOperands = true;
      if (operands) {
        for (auto oper : *operands) {
          UHDM_OBJECT_TYPE optype = oper->UhdmType();
          if (optype != uhdmconstant) {
            constantOperands = false;
            break;
          }
        }
        if (constantOperands) {
          VectorOfany& operands = *op->Operands();
          bool invalidValue = false;
          switch (op->VpiOpType()) {
            case vpiArithRShiftOp:
            case vpiRShiftOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) >> get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiEqOp: {
              if (operands.size() == 2) {
                std::string s0;
                std::string s1;
                const UHDM::constant* hs0 = dynamic_cast<const UHDM::constant*> ((constant*)(operands[0]));
                if (hs0) {
                  s_vpi_value* sval = String2VpiValue(hs0->VpiValue());
                  if (sval) {
                    if (sval->format == vpiStringVal) {
                      s0 = sval->value.str;
                    }
                  }
                }
                const UHDM::constant* hs1 = dynamic_cast<const UHDM::constant*> ((constant*)(operands[1]));
                if (hs1) {
                  s_vpi_value* sval = String2VpiValue(hs1->VpiValue());
                  if (sval) {
                    if (sval->format == vpiStringVal) {
                      s1 = sval->value.str;
                    }
                  }
                }

                unsigned long long val = 0;
                if (hs0 && hs1) {
                  val = (s0 == s1);
                } else {
                  val = get_value(invalidValue, (constant*)(operands[0])) == get_value(invalidValue, (constant*)(operands[1]));
                }
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiNeqOp: {
              if (operands.size() == 2) {
                std::string s0;
                std::string s1;
                const UHDM::constant* hs0 = dynamic_cast<const UHDM::constant*> ((constant*)(operands[0]));
                if (hs0) {
                  s_vpi_value* sval = String2VpiValue(hs0->VpiValue());
                  if (sval) {
                    if (sval->format == vpiStringVal) {
                      s0 = sval->value.str;
                    }
                  }
                }
                const UHDM::constant* hs1 = dynamic_cast<const UHDM::constant*> ((constant*)(operands[1]));
                if (hs1) {
                  s_vpi_value* sval = String2VpiValue(hs1->VpiValue());
                  if (sval) {
                    if (sval->format == vpiStringVal) {
                      s1 = sval->value.str;
                    }
                  }
                }

                unsigned long long val = 0;
                if (hs0 && hs1) {
                  val = (s0 != s1);
                } else {
                  val = get_value(invalidValue, (constant*)(operands[0])) != get_value(invalidValue, (constant*)(operands[1]));
                }
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiGtOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) > get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiGeOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) >=
                          get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiLtOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) <
                          get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiLeOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) <=
                          get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiArithLShiftOp:
            case vpiLShiftOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0]))
                          << get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiAddOp:
            case vpiPlusOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) + get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiBitOrOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) | get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiBitAndOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) & get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiLogOrOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) || get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiLogAndOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) && get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiMinusOp: {
              if (operands.size() == 1) {
                unsigned long long val = - get_value(invalidValue, (constant*)(operands[0]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiSubOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) - get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiMultOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) * get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiBitNegOp: {
              if (operands.size() == 1) {
                unsigned long long val = ~ get_value(invalidValue, (constant*)(operands[0]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiNotOp: {
              if (operands.size() == 1) {
                unsigned long long val = ! get_value(invalidValue, (constant*)(operands[0]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiUnaryAndOp: {
              if (operands.size() == 1) {
                constant* cst = (constant*)(operands[0]);
                unsigned long long val = get_value(invalidValue, cst);
                int res = val & 1;
                for (int i = 1; i < cst->VpiSize(); i++) {
                  res = res & ((val & (1 << i)) >> i);
                }
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(res));
                c->VpiDecompile(std::to_string(res));
                result = c;
              }
              break;
            }
            case vpiUnaryNandOp: {
              if (operands.size() == 1) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0]));
                int res = val & 1;
                for (unsigned int i = 1; i < 32; i++) {
                  res = res & ((val & (1 << i)) >> i);
                }
                res = ~res;
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(res));
                c->VpiDecompile(std::to_string(res));
                result = c;
              }
              break;
            }
            case vpiUnaryOrOp: {
              if (operands.size() == 1) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0]));
                int res = val & 1;
                for (unsigned int i = 1; i < 32; i++) {
                  res = res | ((val & (1 << i)) >> i);
                }
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(res));
                c->VpiDecompile(std::to_string(res));
                result = c;
              }
              break;
            }
            case vpiUnaryNorOp: {
              if (operands.size() == 1) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0]));
                int res = val & 1;
                for (unsigned int i = 1; i < 32; i++) {
                  res = res | ((val & (1 << i)) >> i);
                }
                res = ~res;
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(res));
                c->VpiDecompile(std::to_string(res));
                result = c;
              }
              break;
            }
            case vpiUnaryXorOp: {
              if (operands.size() == 1) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0]));
                int res = val & 1;
                for (unsigned int i = 1; i < 32; i++) {
                  res = res ^ ((val & (1 << i)) >> i);
                }
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(res));
                c->VpiDecompile(std::to_string(res));
                result = c;
              }
              break;
            }
            case vpiUnaryXNorOp: {
              if (operands.size() == 1) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0]));
                int res = val & 1;
                for (unsigned int i = 1; i < 32; i++) {
                  res = res ^ ((val & (1 << i)) >> i);
                }
                res = ~res;
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(res));
                c->VpiDecompile(std::to_string(res));
                result = c;
              }
              break;
            }
            case vpiModOp: {
              if (operands.size() == 2) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) % get_value(invalidValue, (constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiDivOp: {
              if (operands.size() == 2) {
                unsigned long long divisor = get_value(invalidValue, (constant*)operands[1]);
                if (divisor) {
                  int val = get_value(invalidValue, (constant*)(operands[0])) / divisor;
                  UHDM::constant* c = s.MakeConstant();
                  c->VpiValue("INT:" + std::to_string(val));
                  c->VpiDecompile(std::to_string(val));
                  result = c;
                }
              }
              break;
            }
            case vpiConditionOp: {
              if (operands.size() == 3) {
                unsigned long long val = get_value(invalidValue, (constant*)(operands[0])) ? get_value(invalidValue, (constant*)(operands[1])) : get_value(invalidValue, (constant*)(operands[2]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiPowerOp: {
              if (operands.size() == 2) {
                unsigned long long val = pow(get_value(invalidValue, (constant*)(operands[0])), get_value(invalidValue, (constant*)(operands[1])));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiCastOp:
            case vpiConcatOp:
            case vpiMultiConcatOp:
            case vpiAssignmentPatternOp:  
            case vpiMultiAssignmentPatternOp: 
              // Don't reduce these ops
              break;
            default: {
              invalidValue = true;
            }
          }
          if (invalidValue) {
            // Can't reduce an expression
            ErrorContainer* errors =
                compileDesign->getCompiler()->getErrorContainer();
            SymbolTable* symbols =
                compileDesign->getCompiler()->getSymbolTable();
            std::string fileContent =
                FileUtils::getFileContent(fC->getFileName());
            std::string lineText =
                StringUtils::getLineInString(fileContent, fC->Line(the_node));
            Location loc(symbols->registerSymbol(fC->getFileName(the_node)),
                         fC->Line(the_node), 0,
                         symbols->registerSymbol(std::string("<") +
                                                 fC->printObject(the_node) +
                                                 std::string("> ") + lineText));
            Error err(ErrorDefinition::UHDM_UNSUPPORTED_EXPR, loc);
            errors->addError(err);
          }
        }
      }
    }
  }

  if (result) {
    if (child) {
      result->VpiFile(fC->getFileName(child));
      result->VpiLineNo(fC->Line(child));
    } else {
      result->VpiFile(fC->getFileName(parent));
      result->VpiLineNo(fC->Line(parent));
    }
  }

  return result;
}

UHDM::any* CompileHelper::compileAssignmentPattern(
  DesignComponent* component, const FileContent* fC, NodeId Assignment_pattern,
  CompileDesign* compileDesign,
  UHDM::any* pexpr,
  ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  UHDM::operation* operation = s.MakeOperation();
  UHDM::VectorOfany* operands = s.MakeAnyVec();
  result = operation;
  operation->VpiParent(pexpr);
  operation->VpiOpType(vpiAssignmentPatternOp);
  operation->Operands(operands);
  // Page 1035: For an operation of type vpiAssignmentPatternOp, the operand iteration shall return the expressions as if the
  // assignment pattern were written with the positional notation. Nesting of assignment patterns shall be preserved.

  // We forward the structure without reordering the bits or interpreting, 
  // we deviate from the Standard by forwarding the complete spec to the client
  // and letting them do the reordering if need be.
  NodeId Structure_pattern_key = fC->Child(Assignment_pattern);
  bool with_key = true;
  if (fC->Type(Structure_pattern_key) == VObjectType::slExpression) {
    with_key = false;
  }
  while (Structure_pattern_key) {
    NodeId Expression;
    if (!with_key) {
      Expression = Structure_pattern_key; // No key '{1,2,...}
      if (Expression) {
        if (any* exp = compileExpression(component, fC, Expression, compileDesign, operation, instance)) {
          operands->push_back(exp);
        }
      }
    } else {
      Expression = fC->Sibling(Structure_pattern_key); // With key '{a: 1, b: 2,...}

      if (Expression) {
        if (any* exp = compileExpression(component, fC, Expression, compileDesign, operation, instance)) {
          tagged_pattern* pattern = s.MakeTagged_pattern();
          pattern->Pattern(exp);
          NodeId Constant_expression = fC->Child(Structure_pattern_key);
          NodeId Constant_primary = fC->Child(Constant_expression);
          if (Constant_primary == 0) {
            UHDM::string_typespec* tps = s.MakeString_typespec();
            if (fC->Type(Constant_expression) == slStringConst) {
              tps->VpiName(fC->SymName(Constant_expression));
            } else {
              tps->VpiName("default");
            }
            tps->VpiFile(fC->getFileName());
            tps->VpiLineNo(fC->Line(Constant_expression));
            pattern->Typespec(tps);
          } else {
            NodeId Primary_literal = Constant_primary;
            if (fC->Type(Primary_literal) != slPrimary_literal)
              Primary_literal = fC->Child(Constant_primary);
            pattern->Typespec(compileTypespec(component, fC, Primary_literal, compileDesign, nullptr, instance, true, ""));
          }
          operands->push_back(pattern);
        }
      }
      Structure_pattern_key = fC->Sibling(Structure_pattern_key);
    }
 
    if (Structure_pattern_key)
      Structure_pattern_key = fC->Sibling(Structure_pattern_key);
  }
  return result;
}

std::vector<UHDM::range*>* CompileHelper::compileRanges(
  DesignComponent* component, const FileContent* fC, NodeId Packed_dimension,
  CompileDesign* compileDesign,
  UHDM::any* pexpr,
  ValuedComponentI* instance, bool reduce, int& size) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  VectorOfrange* ranges = nullptr;
  size = 0;
  if (Packed_dimension && ((fC->Type(Packed_dimension) == VObjectType::slPacked_dimension) ||
                           (fC->Type(Packed_dimension) == VObjectType::slUnpacked_dimension) ||
                           (fC->Type(Packed_dimension) == VObjectType::slVariable_dimension) ||
                           (fC->Type(Packed_dimension) == VObjectType::slConstant_range))) {
    ranges = s.MakeRangeVec();
    size = 1;
    while (Packed_dimension) {
      NodeId Constant_range = fC->Child(Packed_dimension);
      if (fC->Type(Packed_dimension) == VObjectType::slConstant_range) {
        Constant_range = Packed_dimension;
      }
      if (fC->Type(Constant_range) == VObjectType::slUnpacked_dimension ||
          fC->Type(Constant_range) == VObjectType::slPacked_dimension) {
        Constant_range = fC->Child(Constant_range);
      }
      if (fC->Type(Constant_range) == VObjectType::slConstant_range) {
        // Specified by range
        NodeId lexpr = fC->Child(Constant_range);
        NodeId rexpr = fC->Sibling(lexpr);
        range* range = s.MakeRange();
        expr* lexp = nullptr;
        expr* rexp = nullptr;
        if (reduce) {
          Value* leftV = m_exprBuilder.evalExpr(fC, lexpr, instance, true);
          Value* rightV = m_exprBuilder.evalExpr(fC, rexpr, instance, true);
          uint64_t lint = 0;
          uint64_t rint = 0;
          if (leftV->isValid()) {
            constant* lexpc = s.MakeConstant();
            lexpc->VpiSize(leftV->getSize());
            lexpc->VpiConstType(vpiIntConst);
            lexpc->VpiValue(leftV->uhdmValue());
            lexpc->VpiDecompile(leftV->decompiledValue());
            lexpc->VpiFile(fC->getFileName());
            lexpc->VpiLineNo(fC->Line(lexpr));
            lexp = lexpc;
            lint = leftV->getValueL();
          }
          if (rightV->isValid()) {
            constant* rexpc = s.MakeConstant();
            rexpc->VpiSize(rightV->getSize());
            rexpc->VpiConstType(vpiIntConst);
            rexpc->VpiValue(rightV->uhdmValue());
            rexpc->VpiDecompile(rightV->decompiledValue());
            rexpc->VpiFile(fC->getFileName());
            rexpc->VpiLineNo(fC->Line(rexpr));
            rexp = rexpc;
            rint = rightV->getValueL();
          }
          uint64_t tmp = (lint > rint) ? lint - rint + 1 : rint - lint + 1;
          size = size * tmp;
        }
        if (lexp == nullptr)
          lexp = dynamic_cast<expr*> (compileExpression(component, fC, lexpr, compileDesign, pexpr, instance, reduce));
        range->Left_expr(lexp);
        if (lexp)
          lexp->VpiParent(range);
        if (rexp == nullptr)
          rexp = dynamic_cast<expr*> (compileExpression(component, fC, rexpr, compileDesign, pexpr, instance, reduce));
        if (rexp)
          rexp->VpiParent(range);
        range->Right_expr(rexp);
        range->VpiFile(fC->getFileName());
        range->VpiLineNo(fC->Line(Constant_range));
        ranges->push_back(range);
        range->VpiParent(pexpr);
      } else if (fC->Type(Constant_range) == VObjectType::slConstant_expression) {
        // Specified by size
        NodeId rexpr = Constant_range;
        range* range = s.MakeRange();
        expr* lexp = nullptr;
        expr* rexp = nullptr;

        constant* lexpc = s.MakeConstant();
        lexpc->VpiConstType(vpiIntConst);
        lexpc->VpiSize(1);
        lexpc->VpiValue("INT:0");
        lexpc->VpiDecompile("0");
        lexpc->VpiFile(fC->getFileName());
        lexpc->VpiLineNo(fC->Line(rexpr));
        lexp = lexpc;

        if (reduce) {
          Value* rightV = m_exprBuilder.evalExpr(fC, rexpr, instance, true);
          if (rightV->isValid()) {
            constant* rexpc = s.MakeConstant();
            rexpc->VpiSize(rightV->getSize());
            rexpc->VpiConstType(vpiIntConst);
            uint64_t rint = rightV->getValueL();
            size = size * rint;
            rightV->decr(); // Decr by 1
            rexpc->VpiValue(rightV->uhdmValue());
            rexpc->VpiDecompile(rightV->decompiledValue());
            rexpc->VpiFile(fC->getFileName());
            rexpc->VpiLineNo(fC->Line(rexpr));
            rexp = rexpc;
          }
        }
        range->Left_expr(lexp);
        lexp->VpiParent(range);
        if (rexp == nullptr) {
          rexp = dynamic_cast<expr*> (compileExpression(component, fC, rexpr, compileDesign, pexpr, instance, reduce));
          bool associativeArray = false;
          if (rexp && rexp->UhdmType() == uhdmconstant) {
            constant* c = (constant*) rexp;
            if (c->VpiConstType() == vpiUnboundedConst)
              associativeArray = true;
          }
          if (!associativeArray) {
            operation* op = s.MakeOperation();  // Decr by 1
            op->VpiOpType(vpiMinusOp);
            op->Operands(s.MakeAnyVec());
            op->Operands()->push_back(rexp);
            constant* one = s.MakeConstant();
            one->VpiValue("INT:1");
            op->Operands()->push_back(one);
            rexp = op;
          }
        }
        if (rexp)
          rexp->VpiParent(range);
        range->Right_expr(rexp);
        range->VpiFile(fC->getFileName());
        range->VpiLineNo(fC->Line(Constant_range));
        ranges->push_back(range);
        range->VpiParent(pexpr);
      }
      Packed_dimension = fC->Sibling(Packed_dimension);
    }
  }
  return ranges;
}

UHDM::any* CompileHelper::compilePartSelectRange(
  DesignComponent* component, const FileContent* fC, NodeId Constant_range,
  const std::string& name,
  CompileDesign* compileDesign,
  UHDM::any* pexpr,
  ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  if (fC->Type(Constant_range) == VObjectType::slConstant_range) {
    NodeId Constant_expression = fC->Child(Constant_range);
    UHDM::expr* lexp =
        (expr*)compileExpression(component, fC, Constant_expression, compileDesign, pexpr, instance);
    UHDM::expr* rexp = (expr*)compileExpression(
        component, fC, fC->Sibling(Constant_expression), compileDesign, pexpr, instance);
    UHDM::part_select* part_select = s.MakePart_select();
    part_select->Left_range(lexp);
    part_select->Right_range(rexp);
    if (!name.empty()) {
      UHDM::ref_obj* ref = s.MakeRef_obj();
      ref->VpiName(name);
      part_select->VpiParent(ref);
    }
    part_select->VpiConstantSelect(true);
    result = part_select;
  } else {
    // constant_indexed_range
    NodeId Constant_expression = fC->Child(Constant_range);
    UHDM::expr* lexp =
        (expr*)compileExpression(component, fC, Constant_expression, compileDesign, pexpr, instance);
    NodeId op = fC->Sibling(Constant_expression);
    UHDM::expr* rexp =
        (expr*)compileExpression(component, fC, fC->Sibling(op), compileDesign, pexpr, instance);
    UHDM::indexed_part_select* part_select = s.MakeIndexed_part_select();
    part_select->Base_expr(lexp);
    part_select->Width_expr(rexp);
    if (fC->Type(op) == VObjectType::slIncPartSelectOp)
      part_select->VpiIndexedPartSelectType(vpiPosIndexed);
    else
      part_select->VpiIndexedPartSelectType(vpiNegIndexed);
    if (!name.empty()) {
      UHDM::ref_obj* ref = s.MakeRef_obj();
      ref->VpiName(name);
      part_select->VpiParent(ref);
    }
    part_select->VpiConstantSelect(true);
    result = part_select;
  }
  return result;
}

static unsigned int Bits(const UHDM::typespec* typespec) {
  unsigned int bits = 0;
  UHDM::VectorOfrange* ranges = nullptr;
  if (typespec) {
    switch (typespec->UhdmType()) {
      case UHDM::uhdmshort_real_typespec: {
        bits = 32;
        break;
      }
      case UHDM::uhdmreal_typespec: {
        bits = 32;
        break;
      }
      case UHDM::uhdmbyte_typespec: {
        bits = 8;
        break;
      }
      case UHDM::uhdmshort_int_typespec: {
        bits = 16;
        break;
      }
      case UHDM::uhdmint_typespec: {
        bits = 32;
        break;
      }
      case UHDM::uhdmlong_int_typespec: {
        bits = 64;
        break;
      }
      case UHDM::uhdminteger_typespec: {
        bits = 32;
        break;
      }
      case UHDM::uhdmbit_typespec: {
        bits = 1;
        UHDM::bit_typespec* lts = (UHDM::bit_typespec*)typespec;
        ranges = lts->Ranges();
        break;
      }
      case UHDM::uhdmlogic_typespec: {
        bits = 1;
        UHDM::logic_typespec* lts = (UHDM::logic_typespec*)typespec;
        ranges = lts->Ranges();
        break;
      }
      case UHDM::uhdmstruct_typespec: {
        UHDM::struct_typespec* sts = (UHDM::struct_typespec*) typespec;
        UHDM::VectorOftypespec_member* members = sts->Members();
        if (members) {
          for (UHDM::typespec_member* member : *members) {
            bits += Bits(member->Typespec());
          }
        }
        break;
      }
      case UHDM::uhdmenum_typespec: {
        const UHDM::enum_typespec* sts = dynamic_cast<const UHDM::enum_typespec*> (typespec);
        if (sts)
          bits = Bits(sts->Base_typespec());
        break;
      }
      case UHDM::uhdmunion_typespec: {
        UHDM::union_typespec* sts = (UHDM::union_typespec*) typespec;
        UHDM::VectorOftypespec_member* members = sts->Members();
        if (members) {
          for (UHDM::typespec_member* member : *members) {
            unsigned int max = Bits(member->Typespec());
            if (max > bits)
              bits = max;
          }
        }
        break;
      }
      default:
        break;
    }
  }
  if (ranges) {
    for (UHDM::range* ran : *ranges) {
      bool invalidValue = false;
      unsigned long long lv = get_value(invalidValue, ran->Left_expr());
      unsigned long long rv = get_value(invalidValue, ran->Right_expr());
      if (lv > rv)
        bits = bits * (lv - rv + 1);
      else
        bits = bits * (rv - lv + 1);
    }
  }
  return bits;
}

const typespec* CompileHelper::getTypespec(
  DesignComponent* component, const FileContent* fC,
  NodeId id, CompileDesign* compileDesign, ValuedComponentI* instance,
  bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  const DataType* dtype = nullptr;
  const typespec* result = nullptr;
  std::string basename;
  std::string suffixname;
  switch (fC->Type(id)) {
    case slIntegerAtomType_Byte: {
      result = s.MakeByte_typespec();
      break;
    }
    case slIntegerAtomType_Int: {
      result = s.MakeInt_typespec();
      break;
    }
    case slIntegerAtomType_LongInt: {
      result = s.MakeLong_int_typespec();
      break;
    }
    case slIntegerAtomType_Shortint: {
      result = s.MakeShort_int_typespec();
      break;
    }
    case slIntegerAtomType_Time: {
      result = s.MakeTime_typespec();
      break;
    }
    case VObjectType::slStringConst: {
      basename = fC->SymName(id);
      NodeId suffix = fC->Sibling(id);
      if (suffix) {
        suffixname = fC->SymName(suffix);
      }
      break;
    }
    case VObjectType::slClass_scope: {
      NodeId Class_type = fC->Child(id);
      NodeId Class_type_name = fC->Child(Class_type);
      NodeId Class_scope_name = fC->Sibling(id);
      basename =
          fC->SymName(Class_type_name) + "::" + fC->SymName(Class_scope_name);
      Package* p = compileDesign->getCompiler()->getDesign()->getPackage(
          fC->SymName(Class_type_name));
      if (p) {
        dtype = p->getDataType(fC->SymName(Class_scope_name));
      }
      break;
    }
    case VObjectType::slPackage_scope: {
      const std::string& packageName = fC->SymName(fC->Child(id));
      const std::string& n = fC->SymName(fC->Sibling(id));
      basename = packageName + "::" + n;
      Package* p =
          compileDesign->getCompiler()->getDesign()->getPackage(packageName);
      if (p) {
        dtype = p->getDataType(n);
      }
      break;
    }
    default:
      break;
  }

  if (dtype == nullptr) {
    if (component)
      dtype = component->getDataType(basename);
  }
  if ((dtype == nullptr) && component) {
    Signal* sig = nullptr;
    for (auto s : component->getPorts()) {
      if (s->getName() == basename) {
        sig = s;
        break;
      }
    }
    if (sig == nullptr) {
      for (auto s : component->getSignals()) {
        if (s->getName() == basename) {
          sig = s;
          break;
        }
      }
    }
    if (sig) {
      if (sig->getTypeSpecId()) {
        result = compileTypespec(component, fC, sig->getTypeSpecId(), compileDesign, nullptr, instance, true, suffixname);
      } else {
        NodeId Packed_dimension = sig->getPackedDimension();
        if (fC->Type(Packed_dimension) != VObjectType::slNull_rule) {
          NodeId DataType = fC->Parent(Packed_dimension);
          result = compileTypespec(component, fC, DataType, compileDesign, nullptr, instance, true);
        }
      }
    }
  }
  while (dtype) {
    const TypeDef* typed = dynamic_cast<const TypeDef*>(dtype);
    if (typed) {
      const DataType* dt = typed->getDataType();
      const Enum* en = dynamic_cast<const Enum*>(dt);
      if (en) {
        result = en->getTypespec();
        break;
      }
      const Struct* st = dynamic_cast<const Struct*>(dt);
      if (st) {
        result = st->getTypespec();
        if (!suffixname.empty()) {
          struct_typespec* tpss = (struct_typespec*) result;
          for (typespec_member* memb : *tpss->Members()) {
            if (memb->VpiName() == suffixname) {
              result = memb->Typespec();
              break;
            }
          }
        }
        break;
      }
      const Union* un = dynamic_cast<const Union*>(dt);
      if (un) {
        result = un->getTypespec();
        break;
      }
      const SimpleType* sit = dynamic_cast<const SimpleType*>(dt);
      if (sit) {
        result = sit->getTypespec();
        break;
      }
    }
    dtype = dtype->getDefinition();
  }

  if (result == nullptr) {
    ModuleInstance* inst = dynamic_cast<ModuleInstance*> (instance);
    if (inst) {
      Netlist* netlist = inst->getNetlist();
      if (netlist) {
        if (netlist->ports()) {
          for (port* p : *netlist->ports()) {
            if (p->VpiName() == basename) {
              const typespec* tps = p->Typespec();
              if (tps && (tps->UhdmType() == uhdmstruct_typespec)) {
                struct_typespec* tpss = (struct_typespec*) tps;
                for (typespec_member* memb : *tpss->Members()) {
                  if (memb->VpiName() == suffixname) {
                    result = memb->Typespec();
                    break;
                  }
                }
              }
            }
            if (result)
              break;
          }
        }
      }
    }
  }
  return result;
}

UHDM::any* CompileHelper::compileBits(
  DesignComponent* component, const FileContent* fC,
  NodeId List_of_arguments,
  CompileDesign* compileDesign, UHDM::any* pexpr,
  ValuedComponentI* instance, bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  NodeId Expression = List_of_arguments;
  if (fC->Type(Expression) == slList_of_arguments) {
    Expression = fC->Child(Expression);
  } else if (fC->Type(Expression) == slData_type) {
    Expression = fC->Child(Expression);
  }
  NodeId typeSpecId = 0;
  switch (fC->Type(Expression)) {
    case slIntegerAtomType_Byte:
    case slIntegerAtomType_Int:
    case slIntegerAtomType_LongInt:
    case slIntegerAtomType_Shortint:
    case slIntegerAtomType_Time:
      typeSpecId = Expression;
      break;
    default: {
      NodeId Primary = fC->Child(Expression);
      NodeId Primary_literal = fC->Child(Primary);
      NodeId StringConst = fC->Child(Primary_literal);
      typeSpecId = StringConst;
    }
  }

  unsigned int bits = 0;

  const typespec* tps = getTypespec(component, fC, typeSpecId, compileDesign, instance, reduce);
  if (tps)
    bits = Bits(tps);

  if (bits) {
    UHDM::constant* c = s.MakeConstant();
    c->VpiValue("INT:" + std::to_string(bits));
    c->VpiDecompile(std::to_string(bits));
    result = c;
  } else {
    UHDM::sys_func_call* sys = s.MakeSys_func_call();
    sys->VpiName("$bits");
    VectorOfany *arguments = compileTfCallArguments(component, fC, List_of_arguments, compileDesign, sys);
    sys->Tf_call_args(arguments);
    result = sys;
  }

  return result;
}

UHDM::any* CompileHelper::compileTypename(
  DesignComponent* component, const FileContent* fC,
  NodeId Expression,
  CompileDesign* compileDesign, UHDM::any* pexpr,
  ValuedComponentI* instance, bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  UHDM::constant* c = s.MakeConstant();
  if (fC->Type(Expression) == slData_type) 
    Expression = fC->Child(Expression);
  VObjectType type = fC->Type(Expression);
  switch (type) {
    case slIntVec_TypeLogic:
      c->VpiValue("STRING:logic");
      c->VpiDecompile("logic");
      result = c;
      break;
    case slIntVec_TypeBit:
      c->VpiValue("STRING:bit");
      c->VpiDecompile("bit");
      result = c;
      break;
    case slIntVec_TypeReg:
      c->VpiValue("STRING:reg");
      c->VpiDecompile("reg");
      result = c;
      break;
    case slIntegerAtomType_Byte:
      c->VpiValue("STRING:byte");
      c->VpiDecompile("byte");
      result = c;
      break;
    case slIntegerAtomType_Shortint:
      c->VpiValue("STRING:shortint");
      c->VpiDecompile("shortint");
      result = c;
      break;
    case slIntegerAtomType_Int:
      c->VpiValue("STRING:int");
      c->VpiDecompile("int");
      result = c;
      break;
    case slIntegerAtomType_LongInt:
      c->VpiValue("STRING:longint");
      c->VpiDecompile("longint");
      result = c;
      break;
    case slIntegerAtomType_Time:
      c->VpiValue("STRING:time");
      c->VpiDecompile("time");
      result = c;
      break;
    case slNonIntType_ShortReal:
      c->VpiValue("STRING:shortreal");
      c->VpiDecompile("shortreal");
      result = c;
      break;
    case slNonIntType_Real:
      c->VpiValue("STRING:real");
      c->VpiDecompile("real");
      result = c;
      break;
    case slNonIntType_RealTime:
      c->VpiValue("STRING:realtime");
      c->VpiDecompile("realtime");
      result = c;
      break;
    default:
      UHDM::sys_func_call* sys = s.MakeSys_func_call();
      sys->VpiName("$typename");
      result = sys;
      const std::string& arg = fC->SymName(Expression);
      c->VpiValue("STRING:" + arg);
      c->VpiDecompile(arg);
      break;
  }
  return result;
}

UHDM::any* CompileHelper::compileClog2(
  DesignComponent* component, const FileContent* fC,
  NodeId List_of_arguments,
  CompileDesign* compileDesign, UHDM::any* pexpr,
  ValuedComponentI* instance, bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  NodeId Expression = List_of_arguments;
  if (fC->Type(Expression) == slList_of_arguments) {
    Expression = fC->Child(Expression);
  }
  expr* operand = (expr*) compileExpression(component, fC, Expression, compileDesign, pexpr, instance, reduce);
  bool invalidValue = false;
  unsigned long long val = get_value(invalidValue, operand);
  if (val) {
    val = val - 1;
    int clog2 = 0;
    for (; val > 0; clog2 = clog2 + 1) {
      val = val >> 1;
    }
    UHDM::constant* c = s.MakeConstant();
    c->VpiValue("INT:" + std::to_string(clog2));
    c->VpiDecompile(std::to_string(clog2));
    result = c;
  } else {
    UHDM::sys_func_call* sys = s.MakeSys_func_call();
    sys->VpiName("$clog2");
    VectorOfany *arguments = compileTfCallArguments(component, fC, List_of_arguments, compileDesign, sys);
    sys->Tf_call_args(arguments);
    result = sys;
  }
  return result;
}


UHDM::any* CompileHelper::compileComplexFuncCall(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, UHDM::any* pexpr, ValuedComponentI* instance,
    bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  NodeId name = fC->Child(nodeId);
  NodeId dotedName = fC->Sibling(name);
  if (fC->Type(name) == VObjectType::slDollar_root_keyword) {
    NodeId Dollar_root_keyword = name;
    NodeId nameId = fC->Sibling(Dollar_root_keyword);
    std::string name = "$root." + fC->SymName(nameId);
    nameId = fC->Sibling(nameId);
    while (nameId) {
      if (fC->Type(nameId) == slStringConst) {
        name += "." + fC->SymName(nameId);
      } else if (fC->Type(nameId) == slConstant_expression) {
        NodeId Constant_expresion = fC->Child(nameId);
        if (Constant_expresion) {
          name += "[";
          expr* select = (expr*) compileExpression(component, fC, Constant_expresion, compileDesign);
          name += select->VpiDecompile();
          name += "]";
        }
      } else {
        break;
      }
      nameId = fC->Sibling(nameId);
    }
    ref_obj* ref = s.MakeRef_obj();
    ref->VpiName(name);
    result = ref;
  } else if (fC->Type(name) == VObjectType::slDollar_keyword) {
    NodeId Dollar_keyword = name;
    NodeId nameId = fC->Sibling(Dollar_keyword);
    const std::string& name = fC->SymName(nameId);
    if (name == "bits") {
      NodeId List_of_arguments = fC->Sibling(nameId);
      result = compileBits(component, fC, List_of_arguments, compileDesign, pexpr,
                           instance, reduce);
    } else if (name == "clog2") {
      NodeId List_of_arguments = fC->Sibling(nameId);
      result = compileClog2(component, fC, List_of_arguments, compileDesign,
                            pexpr, instance, reduce);
    } else {
      NodeId List_of_arguments = fC->Sibling(nameId);
      UHDM::sys_func_call* sys = s.MakeSys_func_call();
      sys->VpiName("$" + name);
      VectorOfany* arguments = compileTfCallArguments(
          component, fC, List_of_arguments, compileDesign, sys);
      sys->Tf_call_args(arguments);
      result = sys;
    }
  } else if (fC->Type(name) == VObjectType::slImplicit_class_handle) {
    NodeId Handle = fC->Child(name);
    NodeId Method = fC->Sibling(name);
    if (Method == 0) {
      return compileExpression(component, fC, Handle, compileDesign, pexpr,
                               instance, reduce);
    }
    const std::string& name = fC->SymName(Method);
    NodeId List_of_arguments = fC->Sibling(Method);
    if (fC->Type(List_of_arguments) == slList_of_arguments) {
      method_func_call* fcall = s.MakeMethod_func_call();
      expr* object = (expr*)compileExpression(
          component, fC, Handle, compileDesign, pexpr, instance, reduce);
      fcall->Prefix(object);
      fcall->VpiName(name);
      VectorOfany* arguments = compileTfCallArguments(
          component, fC, List_of_arguments, compileDesign, fcall);
      fcall->Tf_call_args(arguments);
      result = fcall;
    } else if (fC->Type(List_of_arguments) == slConstant_expression ||
               fC->Type(List_of_arguments) == slSelect ||
               fC->Type(List_of_arguments) == slConstant_select) {
      // TODO: prefix the var_select with "this" class var
      // (this.fields[idx-1].get...)
      if (fC->Type(List_of_arguments) == slSelect)
        List_of_arguments = fC->Child(List_of_arguments);
      result = compileSelectExpression(component, fC, List_of_arguments, name,
                                       compileDesign, pexpr, instance);
      if (result == nullptr) {
        // TODO: this is a mockup
        constant* cvar = s.MakeConstant();
        cvar->VpiDecompile("this");
        result = cvar;
      }
    } else if (fC->Type(List_of_arguments) == slConstant_bit_select) {
      // TODO: Fill this
      method_func_call* fcall = s.MakeMethod_func_call();
      expr* object = (expr*)compileExpression(
          component, fC, Handle, compileDesign, pexpr, instance, reduce);
      VectorOfany* arguments = compileTfCallArguments(
          component, fC, fC->Sibling(fC->Sibling(List_of_arguments)), compileDesign, fcall);
      // TODO: make name part of the prefix, get vpiName from sibling
      fcall->Prefix(object);
      fcall->VpiName(name);
      fcall->Tf_call_args(arguments);
      result = fcall;
    } else if (fC->Type(List_of_arguments) == slStringConst) {
      // TODO: this is a mockup
      constant* cvar = s.MakeConstant();
      cvar->VpiDecompile("this");
      result = cvar;
    }
  } else if (fC->Type(name) == VObjectType::slClass_scope) {
    NodeId Class_type = fC->Child(name);
    NodeId Class_type_name = fC->Child(Class_type);
    NodeId Class_scope_name = fC->Sibling(name);
    NodeId List_of_arguments = fC->Sibling(Class_scope_name);
    if (List_of_arguments) {
      if (fC->Type(List_of_arguments) == slSelect) {
        NodeId Bit_Select = fC->Child(List_of_arguments);
        if (fC->Child(Bit_Select) == 0) {
          List_of_arguments = 0;
        }
      }
    }

    std::string packagename = fC->SymName(Class_type_name);
    std::string functionname = fC->SymName(Class_scope_name);
    std::string basename = packagename + "::" + functionname;
    tf_call* call = nullptr;
    if (component && component->getTask_funcs()) {
      // Function binding
      for (UHDM::task_func* tf : *component->getTask_funcs()) {
        if (tf->VpiName() == basename) {
          if (tf->UhdmType() == uhdmfunction) {
            func_call* fcall = s.MakeFunc_call();
            fcall->Function(dynamic_cast<function*>(tf));
            call = fcall;
          } else {
            task_call* tcall = s.MakeTask_call();
            tcall->Task(dynamic_cast<task*>(tf));
            call = tcall;
          }
          break;
        }
      }
    }
    Design* design = compileDesign->getCompiler()->getDesign();
    Package* pack = design->getPackage(packagename);
    if (call == nullptr) {
      if (pack && pack->getTask_funcs()) {
        for (UHDM::task_func* tf : *pack->getTask_funcs()) {
          if (tf->VpiName() == functionname) {
            if (tf->UhdmType() == uhdmfunction) {
              func_call* fcall = s.MakeFunc_call();
              fcall->Function(dynamic_cast<function*>(tf));
              call = fcall;
            } else {
              task_call* tcall = s.MakeTask_call();
              tcall->Task(dynamic_cast<task*>(tf));
              call = tcall;
            }
            break;
          }
        }
      }
    }
    if (call == nullptr) {
      if (pack && (List_of_arguments == 0)) {
        Value* val = pack->getValue(functionname);
        if (val && val->isValid()) {
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue(val->uhdmValue());
          c->VpiDecompile(val->decompiledValue());
          result = c;
          return result;
        }
      }
    }
    if (call == nullptr) {
      if (pack && pack->getParameters()) {
        for (UHDM::any* param : *pack->getParameters()) {
          if (param->VpiName() == functionname) {
            if ((fC->Type(List_of_arguments) == slSelect) &&
                (fC->Child(List_of_arguments))) {
              result = compileSelectExpression(component, fC,
                                               fC->Child(List_of_arguments), "",
                                               compileDesign, pexpr, instance);
              if (result)
                result->VpiParent(param);
              else
                result = param;
            } else {
              result = param;
            }
            break;
          }
        }
        if (result) return result;
      }
    }
    if (call != nullptr) {
      call->VpiName(basename);
      VectorOfany* arguments = compileTfCallArguments(
          component, fC, List_of_arguments, compileDesign, call);
      call->Tf_call_args(arguments);
      result = call;
    } else {
      result = compileExpression(component, fC, name, compileDesign, pexpr,
                                 instance, reduce);
    }
  } else if (fC->Type(dotedName) == VObjectType::slStringConst) {
    result = compileExpression(component, fC, name, compileDesign, pexpr,
                               instance, reduce);
  } else if (fC->Type(dotedName) == VObjectType::slSelect ||
             fC->Type(dotedName) == VObjectType::slConstant_select ||
             fC->Type(dotedName) == VObjectType::slConstant_expression) {
    NodeId Bit_select = fC->Child(dotedName);
    const std::string& sval = fC->SymName(name);
    NodeId selectName = fC->Sibling(dotedName);
    if (fC->Type(selectName) == slMethod_call_body) {
      // Example tree
      //
      // Verilog:
      //   a.find(i) with (i<5);
      //
      // AST:
      //   n<a> u<43> t<StringConst> p<66> s<45> l<4>
      //   n<> u<44> t<Bit_select> p<45> l<4>
      //   n<> u<45> t<Select> p<66> c<44> s<65> l<4>
      //   n<find> u<46> t<StringConst> p<47> l<4>
      //   n<> u<47> t<Array_method_name> p<63> c<46> s<52> l<4>
      //   n<i> u<48> t<StringConst> p<49> l<4>
      //   n<> u<49> t<Primary_literal> p<50> c<48> l<4>
      //   n<> u<50> t<Primary> p<51> c<49> l<4>
      //   n<> u<51> t<Expression> p<52> c<50> l<4>
      //   n<> u<52> t<List_of_arguments> p<63> c<51> s<62> l<4>
      //   n<i> u<53> t<StringConst> p<54> l<4>
      //   n<> u<54> t<Primary_literal> p<55> c<53> l<4>
      //   n<> u<55> t<Primary> p<56> c<54> l<4>
      //   n<> u<56> t<Expression> p<62> c<55> s<61> l<4>
      //   n<5> u<57> t<IntConst> p<58> l<4>
      //   n<> u<58> t<Primary_literal> p<59> c<57> l<4>
      //   n<> u<59> t<Primary> p<60> c<58> l<4>
      //   n<> u<60> t<Expression> p<62> c<59> l<4>
      //   n<> u<61> t<BinOp_Less> p<62> s<60> l<4>
      //   n<> u<62> t<Expression> p<63> c<56> l<4>
      //   n<> u<63> t<Array_manipulation_call> p<64> c<47> l<4>
      //   n<> u<64> t<Built_in_method_call> p<65> c<63> l<4>
      //   n<> u<65> t<Method_call_body> p<66> c<64> l<4>
      //   n<> u<66> t<Complex_func_call> p<67> c<43> l<4>

      NodeId method_child = fC->Child(selectName);
      method_func_call* fcall = nullptr;
      if (fC->Type(method_child) == slBuilt_in_method_call) {
        // vpiName: method name (Array_method_name above)
        NodeId method_name_node = fC->Child(fC->Child(fC->Child(method_child)));
        const std::string& method_name = fC->SymName(method_name_node);
        NodeId randomize_call = fC->Child(method_child);

        // vpiPrefix: object to which the method is being applied (sval here)
        ref_obj* prefix = s.MakeRef_obj();
        prefix->VpiName(sval);

        if (fC->Type(randomize_call) == slRandomize_call) {
          fcall = compileRandomizeCall(component, fC, fC->Child(randomize_call), compileDesign, pexpr);
          fcall->Prefix(prefix);
          result = fcall;
          return result;
        } 

        fcall = s.MakeMethod_func_call();
        fcall->VpiName(method_name);
        NodeId list_of_arguments = fC->Sibling(fC->Child(fC->Child(method_child)));
        NodeId with_conditions_node;
        if (fC->Type(list_of_arguments) == slList_of_arguments) {
          VectorOfany* arguments = compileTfCallArguments(
              component, fC, list_of_arguments, compileDesign, fcall);
          fcall->Tf_call_args(arguments);
          with_conditions_node = fC->Sibling(list_of_arguments);
        } else {
          with_conditions_node = list_of_arguments;
        }
        // vpiWith: with conditions (expression in node u<62> above)
        // (not in every method, node id is 0 if missing)
        if (with_conditions_node != 0) {
          expr* with_conditions = (expr*)compileExpression(component,
                                                           fC,
                                                           with_conditions_node,
                                                           compileDesign,
                                                           pexpr,
                                                           instance);
          fcall->With(with_conditions);
        }

        fcall->Prefix(prefix);
      } else {
        // TODO: non-builtin methods
        fcall = s.MakeMethod_func_call();
        fcall->VpiName(sval);
      }
      result = fcall;
    } else if (selectName) {
      // This is deviating from the standard VPI, in the standard VPI the
      // bit_select is bit blasted, Here we keep the algebraic expression for
      // the index.
      expr* index = (expr*)compileExpression(component, fC, dotedName,
                                             compileDesign, pexpr, instance);
      const std::string& sel = fC->SymName(selectName);
      bit_select* select = s.MakeBit_select();
      select->VpiIndex(index);
      std::string fullName = sval + "." + sel;
      select->VpiName(fullName);
      select->VpiParent(pexpr);
      result = select;
    } else {
      result = compileSelectExpression(component, fC, Bit_select, sval,
                                       compileDesign, pexpr, instance);
    }
  } else {
    result = compileTfCall(component, fC, nodeId, compileDesign);
  }
  return result;
}

