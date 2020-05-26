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
#include "Utils/StringUtils.h"

using namespace SURELOG;

UHDM::any* CompileHelper::compileExpression(PortNetHolder* component, FileContent* fC, NodeId parent,
                                            CompileDesign* compileDesign,
                                            UHDM::expr* pexpr,
                                            ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  NodeId child = fC->Child(parent);
  VObjectType parentType = fC->Type(parent);
  if (child) {
    VObjectType childType = fC->Type(child);
    switch (childType) {
      case VObjectType::slIncDec_PlusPlus: {
        // Pre increment
        UHDM::operation* op = s.MakeOperation();
        op->VpiOpType(vpiPreIncOp);
        op->VpiParent(pexpr);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(child),
                                                   compileDesign, op, instance))
          operands->push_back(operand);
        op->Operands(operands);
        result = op;
        break;
      }
      case VObjectType::slIncDec_MinusMinus: {
        // Pre decrement
        UHDM::operation* op = s.MakeOperation();
        op->VpiOpType(vpiPreDecOp);
        op->VpiParent(pexpr);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(child),
                                                   compileDesign, op, instance))
          operands->push_back(operand);
        op->Operands(operands);
        result = op;
        break;
      }
      case VObjectType::slUnary_Minus: {
        UHDM::operation* op = s.MakeOperation();
        op->VpiOpType(vpiMinusOp);
        op->VpiParent(pexpr);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(child),
                                                   compileDesign, op, instance))
          operands->push_back(operand);
        op->Operands(operands);
        result = op;
        break;
      }
      case VObjectType::slUnary_Plus: {
        UHDM::operation* op = s.MakeOperation();
        op->VpiOpType(vpiPlusOp);
        op->VpiParent(pexpr);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(child),
                                                   compileDesign, op, instance))
          operands->push_back(operand);
        op->Operands(operands);
        result = op;
        break;
      }
      case VObjectType::slUnary_Tilda: {
        UHDM::operation* op = s.MakeOperation();
        op->VpiOpType(vpiBitNegOp);
        op->VpiParent(pexpr);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(child),
                                                   compileDesign, op, instance))
          operands->push_back(operand);
        op->Operands(operands);
        result = op;
        break;
      }
      case VObjectType::slUnary_Not: {
        UHDM::operation* op = s.MakeOperation();
        op->VpiOpType(vpiNotOp);
        op->VpiParent(pexpr);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(child),
                                                   compileDesign, op, instance))
          operands->push_back(operand);
        op->Operands(operands);
        result = op;
        break;
      }
      case VObjectType::slUnary_BitwOr: {
        UHDM::operation* op = s.MakeOperation();
        op->VpiOpType(vpiUnaryOrOp);
        op->VpiParent(pexpr);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(child),
                                                   compileDesign, op, instance))
          operands->push_back(operand);
        op->Operands(operands);
        result = op;
        break;
      }
      case VObjectType::slEdge_Posedge: {
        UHDM::operation* op = s.MakeOperation();
        op->VpiOpType(vpiPosedgeOp);
        op->VpiParent(pexpr);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(child),
                                                   compileDesign, op, instance))
          operands->push_back(operand);
        op->Operands(operands);
        result = op;
        break;
      }
      case VObjectType::slEdge_Negedge: {
        UHDM::operation* op = s.MakeOperation();
        op->VpiOpType(vpiNegedgeOp);
        op->VpiParent(pexpr);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        if (UHDM::any* operand = compileExpression(component, fC, fC->Sibling(child),
                                                   compileDesign, op, instance))
          operands->push_back(operand);
        op->Operands(operands);
        result = op;
        break;
      }
      case VObjectType::slConstant_primary:
      case VObjectType::slPrimary_literal:
      case VObjectType::slPrimary:
      case VObjectType::slConstant_mintypmax_expression:
      case VObjectType::slMintypmax_expression:
      case VObjectType::slSystem_task:
      case VObjectType::slParam_expression:
      case VObjectType::slInc_or_dec_expression:
      case VObjectType::slExpression_or_cond_pattern:
      case VObjectType::slConstant_param_expression:
      case VObjectType::slAssignment_pattern_expression:
      case VObjectType::slConstant_assignment_pattern_expression:
        result = compileExpression(component, fC, child, compileDesign, pexpr, instance);
        break;
      case VObjectType::slComplex_func_call: {
        NodeId name = fC->Child(child);
        NodeId dotedName = fC->Sibling(name);
        if (fC->Type(dotedName) == VObjectType::slStringConst) {
          result = compileExpression(component, fC, name, compileDesign, pexpr, instance);
          break;
        } else if (fC->Type(dotedName) ==
                       VObjectType::slSelect) {
          NodeId bit_select = fC->Child(dotedName);
          NodeId part_sel_range = fC->Sibling(bit_select);
          NodeId Constant_range = fC->Child(part_sel_range);
          auto sval = fC->SymName(name);
          result = compilePartSelectRange(component, fC, Constant_range, sval, compileDesign, pexpr, instance);
          break;
        } else {
          tf_call* call = compileTfCall(component, fC, child, compileDesign);
          result = call;
          break;
        }
      }  
      case VObjectType::slEvent_expression: {
        NodeId subExpr = child;
        UHDM::any* opL =
            compileExpression(component, fC, subExpr, compileDesign, pexpr, instance);
        result = opL;
        NodeId op = fC->Sibling(subExpr);
        UHDM::operation* operation = nullptr;
        UHDM::VectorOfany* operands = nullptr;
        while (op) {
          if (operation == nullptr) {
            operation = s.MakeOperation();
            operands = s.MakeAnyVec();
            operation->Operands(operands);
            operands->push_back(opL);
            result = operation;
          }
          if (fC->Type(op) == VObjectType::slOr_operator) {
            operation->VpiOpType(vpiEventOrOp);
            NodeId subRExpr = fC->Sibling(op);
            UHDM::any* opR =
                compileExpression(component, fC, subRExpr, compileDesign, pexpr, instance);
            operands->push_back(opR);
            op = fC->Sibling(subRExpr);
          } else if (fC->Type(op) == VObjectType::slComma_operator) {
            operation->VpiOpType(vpiListOp);
            NodeId subRExpr = fC->Sibling(op);
            UHDM::any* opR =
                compileExpression(component, fC, subRExpr, compileDesign, pexpr, instance);
            operands->push_back(opR);
            op = fC->Sibling(subRExpr);
          }
        }
        break;
      }
      case VObjectType::slExpression:
      case VObjectType::slConstant_expression: {
        UHDM::any* opL =
            compileExpression(component, fC, child, compileDesign, pexpr, instance);
        NodeId op = fC->Sibling(child);
        if (!op) {
          result = opL;
          break;
        }
        UHDM::operation* operation = s.MakeOperation();
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        result = operation;
        operation->VpiParent(pexpr);
        if (opL) {
          if (opL->VpiParent() == nullptr)
            opL->VpiParent(operation);
          operands->push_back(opL);
        }
        operation->Operands(operands);
        NodeId rval = fC->Sibling(op);
        UHDM::any* opR =
            compileExpression(component, fC, rval, compileDesign, operation, instance);
        if (opR) {
          if (opR->VpiParent() == nullptr)
            opR->VpiParent(operation);
          operands->push_back(opR);
        }
        VObjectType opType = fC->Type(op);
        unsigned int vopType = UhdmWriter::getVpiOpType(opType);
        operation->VpiOpType(vopType);
        if (opType == VObjectType::slConditional_operator) { // Ternary op
          rval = fC->Sibling(rval);
          opR =
            compileExpression(component, fC, rval, compileDesign, operation, instance);
          if (opR) {
            if (opR->VpiParent() == nullptr)
              opR->VpiParent(operation);
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
        std::string name = fC->SymName(n).c_str();
        UHDM::sys_func_call* sys = s.MakeSys_func_call();
        sys->VpiName(name);
        sys->VpiParent(pexpr);

        NodeId argListNode = fC->Sibling(child);
        VectorOfany *arguments = compileTfCallArguments(component, fC, argListNode, compileDesign);
        sys->Tf_call_args(arguments);

        result = sys;
        break;
      }
      case VObjectType::slVariable_lvalue: {
        UHDM::any* variable =
            compileExpression(component, fC, child, compileDesign, pexpr, instance);
        NodeId op = fC->Sibling(child);
        if (op) {
          // Post increment/decrement
          UHDM::operation* operation = s.MakeOperation();
          UHDM::VectorOfany* operands = s.MakeAnyVec();
          result = operation;
          operation->VpiParent(pexpr);
          VObjectType opType = fC->Type(op);
          unsigned int vopType = UhdmWriter::getVpiOpType(opType);
          operation->VpiOpType(vopType);
          operation->Operands(operands);
          operands->push_back(variable);
        } else {
          result = variable;
        }
        break;
      }
      case VObjectType::slAssignment_pattern: {
        result = compileAssignmentPattern(component, fC, child, compileDesign, pexpr, instance);
        break;
      }
      case VObjectType::slPackage_scope:
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
            sval = pack->getValue(n);
          }
        } else {
          NodeId rhs;
          if (parentType == VObjectType::slHierarchical_identifier) {
            rhs = parent;
          } else {
            rhs = child;
          }
          name = fC->SymName(child);
          while ((rhs = fC->Sibling(rhs))) {
            if (fC->Type(rhs) == VObjectType::slStringConst) {
              name += "." + fC->SymName(rhs);
            } else if (fC->Type(rhs) == VObjectType::slSelect) {
              NodeId Bit_select = fC->Child(rhs);
              while (Bit_select) {
                if (fC->Type(Bit_select) == VObjectType::slBit_select) {
                  if (NodeId bitexp = fC->Child(Bit_select)) {
                    UHDM::bit_select* bit_select = s.MakeBit_select();
                    bit_select->VpiName(name);
                    bit_select->VpiIndex((expr*)compileExpression(
                        component, fC, bitexp, compileDesign, pexpr, instance));
                    result = bit_select;
                    break;
                  }
                } else if (fC->Type(Bit_select) ==
                           VObjectType::slPart_select_range) {
                  NodeId Constant_range = fC->Child(Bit_select);
                  result = compilePartSelectRange(component, fC, Constant_range, name, compileDesign, pexpr, instance);               
                  break;
                }
                Bit_select = fC->Sibling(Bit_select);
              }
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
          UHDM::ref_obj* ref = s.MakeRef_obj();
          ref->VpiName(name);
          ref->VpiParent(pexpr);
          result = ref;
        } else {
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue(sval->uhdmValue());
          result = c;
        }
        break;
      }
      case VObjectType::slIntConst: {
        // Do not evaluate the constant, keep it as in the source text:
        UHDM::constant* c = s.MakeConstant();
        std::string value = fC->SymName(child);
        if (strstr(value.c_str(), "'h")) {
          std::string size = value;
          StringUtils::rtrim(size, '\''); 
          c->VpiSize(atoi(size.c_str()));
          value = "HEX:" + value;
          c->VpiConstType(vpiHexConst);
        } else if (strstr(value.c_str(), "'b")) {
          std::string size = value;
          StringUtils::rtrim(size, '\''); 
          c->VpiSize(atoi(size.c_str()));
          value = "BIN:" + value;
          c->VpiConstType(vpiBinaryConst);
        } else if (strstr(value.c_str(), "'o")) {
          std::string size = value;
          StringUtils::rtrim(size, '\''); 
          c->VpiSize(atoi(size.c_str()));
          value = "OCT:" + value;
          c->VpiConstType(vpiOctConst);
        } else if (strstr(value.c_str(), "'")) {
          value = "BIN:" + value;
          c->VpiConstType(vpiBinaryConst);
        } else {
          value = "INT:" + value;
          c->VpiSize(32);
          c->VpiConstType(vpiIntConst);
        }
        c->VpiValue(value);
        result = c;
        break;
      }
      case VObjectType::slRealConst: {
        UHDM::constant* c = s.MakeConstant();
        std::string value = fC->SymName(child);
        value = "REAL:" + value;
        c->VpiValue(value);
        c->VpiConstType(vpiRealConst);
        result = c;
        break;
      }
      case VObjectType::slNumber_1Tickb1:
      case VObjectType::slNumber_1TickB1:
      case VObjectType::slNumber_Tickb1:
      case VObjectType::slNumber_TickB1:
      case VObjectType::slNumber_Tick1: {
        UHDM::constant* c = s.MakeConstant();
        std::string value = "BIN:1";
        c->VpiValue(value);
        c->VpiConstType(vpiBinaryConst);
        c->VpiSize(1);
        result = c;
        break;
      }
      case VObjectType::slNumber_1Tickb0:
      case VObjectType::slNumber_1TickB0:
      case VObjectType::slNumber_Tickb0:
      case VObjectType::slNumber_TickB0:
      case VObjectType::slNumber_Tick0: {
        UHDM::constant* c = s.MakeConstant();
        std::string value = "BIN:0";
        c->VpiValue(value);
        c->VpiConstType(vpiBinaryConst);
        c->VpiSize(1);
        result = c;
        break;
      }
      case VObjectType::slStringLiteral: {
        UHDM::constant* c = s.MakeConstant();
        std::string value = fC->SymName(child);
        c->VpiSize(strlen(value.c_str()));
        value = "STRING:" + value;
        c->VpiValue(value);
        c->VpiConstType(vpiStringConst);
        result = c;
        break;
      }
      case VObjectType::slConcatenation: {
        UHDM::operation* operation = s.MakeOperation();
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        result = operation;
        operation->VpiParent(pexpr);
        operation->Operands(operands);
        operation->VpiOpType(vpiConcatOp);
        NodeId Expression = fC->Child(child);
        while (Expression) {
          UHDM::any* exp = compileExpression(component, fC, Expression, compileDesign, pexpr, instance);
          if (exp) 
            operands->push_back(exp);
          Expression = fC->Sibling(Expression);
        }
        break;
      }
      case VObjectType::slMultiple_concatenation: {
        UHDM::operation* operation = s.MakeOperation();
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        result = operation;
        operation->VpiParent(pexpr);
        operation->Operands(operands);
        operation->VpiOpType(vpiMultiConcatOp);
        NodeId Expression = fC->Child(child);
        while (Expression) {
          UHDM::any* exp = compileExpression(component, fC, Expression, compileDesign, pexpr, instance);
          if (exp) 
            operands->push_back(exp);
          Expression = fC->Sibling(Expression);
        }
        break;
      }
      case VObjectType::slSubroutine_call: {
        Value* val = m_exprBuilder.evalExpr(fC, parent, instance, true);
        constant* c = s.MakeConstant();
        c->VpiValue(val->uhdmValue());
        result = c;
        break;
      }
      default:
        break;
    }
  } else {
    VObjectType type = fC->Type(parent);
    switch (type) {
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
          if (op && (fC->Type(op) != VObjectType::slStringConst)) {
            UHDM::operation* operation = s.MakeOperation();
            UHDM::VectorOfany* operands = s.MakeAnyVec();
            result = operation;
            operation->VpiParent(pexpr);
            VObjectType opType = fC->Type(op);
            unsigned int vopType = UhdmWriter::getVpiOpType(opType);
            operation->VpiOpType(vopType);
            operation->Operands(operands);
            UHDM::ref_obj* ref = s.MakeRef_obj();
            ref->VpiName(name);
            ref->VpiParent(operation);
            operands->push_back(ref);
          } else {
            UHDM::ref_obj* ref = s.MakeRef_obj();
            ref->VpiName(name);
            ref->VpiParent(pexpr);
            result = ref;
          }
        } else {
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue(sval->uhdmValue());
          result = c;
        }
        break;
      }
      default:
        break;
    }
  }
  /*
  if (result == nullptr) {
    NodeId the_node; 
    if (child) {
      the_node = child;
    } else {
      the_node = parent;
    } 
    VObjectType exprtype = fC->Type(the_node);
    if ((exprtype != VObjectType::slEnd)) {
      std::cout << "UNSUPPORTED EXPRESSION: " << fC->getFileName(the_node) << ":" << fC->Line(the_node) << ":" << std::endl;
      std::cout << " -> " << fC->printObject(the_node) << std::endl;
    }
  }
  */
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

UHDM::any* CompileHelper::compileAssignmentPattern(PortNetHolder* component, FileContent* fC, NodeId Assignment_pattern, 
                                       CompileDesign* compileDesign,
                                       UHDM::expr* pexpr,
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

  // WARNING: In this first implementation we do not do the data type binding so we can't order the terms correctly.
  NodeId Structure_pattern_key = fC->Child(Assignment_pattern);
  while (Structure_pattern_key) {
    //NodeId member = fC->Child(Structure_pattern_key);
    NodeId Expression;
    if (fC->Type(Structure_pattern_key) == VObjectType::slExpression) {
      Expression = Structure_pattern_key; // No key '{1,2,...}
    } else {
      Expression = fC->Sibling(Structure_pattern_key); // With key '{a: 1, b: 2,...}
    }
    if (any* exp = compileExpression(component, fC, Expression, compileDesign, operation, instance)) {
      operands->push_back(exp);
    }
    //Structure_pattern_key = fC->Sibling(Structure_pattern_key);
    //if (Structure_pattern_key == 0)
    //  break;
    Structure_pattern_key = fC->Sibling(Structure_pattern_key);
  }
  return result;
}

std::vector<UHDM::range*>* CompileHelper::compileRanges(PortNetHolder* component, FileContent* fC, NodeId Packed_dimension, 
                                       CompileDesign* compileDesign,
                                       UHDM::expr* pexpr,
                                       ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  VectorOfrange* ranges = nullptr;
  if (Packed_dimension && (fC->Type(Packed_dimension) == VObjectType::slPacked_dimension)) {
    NodeId Constant_range = fC->Child(Packed_dimension);
    if (fC->Type(Constant_range) == VObjectType::slConstant_range) { 
      ranges = s.MakeRangeVec();
      while (Constant_range) {     
        NodeId lexpr = fC->Child(Constant_range);
        NodeId rexpr = fC->Sibling(lexpr);
        range* range = s.MakeRange();
        range->Left_expr(dynamic_cast<expr*> (compileExpression(nullptr, fC, lexpr, compileDesign, pexpr, instance)));
        range->Right_expr(dynamic_cast<expr*> (compileExpression(nullptr, fC, rexpr, compileDesign, pexpr, instance)));
        range->VpiFile(fC->getFileName());
        range->VpiLineNo(fC->Line(Constant_range));
        ranges->push_back(range);
        Constant_range = fC->Sibling(Constant_range);
      }
    }
  }
  return ranges;
}

UHDM::any* CompileHelper::compilePartSelectRange(PortNetHolder* component, FileContent* fC, NodeId Constant_range, 
                                       const std::string& name,
                                       CompileDesign* compileDesign,
                                       UHDM::expr* pexpr,
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
    if (name != "") {
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
    if (name != "") {  
      UHDM::ref_obj* ref = s.MakeRef_obj();
      ref->VpiName(name);
      part_select->VpiParent(ref);
    }
    part_select->VpiConstantSelect(true);
    result = part_select;
  }
  return result;
}
