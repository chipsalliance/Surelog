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

using namespace SURELOG;

static unsigned int get_value(const UHDM::expr* expr) {
  const UHDM::constant* hs = dynamic_cast<const UHDM::constant*> (expr);
  if (hs) {
    s_vpi_value* sval = String2VpiValue(hs->VpiValue());
    if (sval) {
      unsigned int result = sval->value.integer;
      delete sval;
      return result;
    }
  }
  return 0;
}

any* CompileHelper::compileSelectExpression(DesignComponent* component,
                                            FileContent* fC, NodeId Bit_select, 
                                            const std::string& name, 
                                            CompileDesign* compileDesign,
                                            UHDM::any* pexpr,
                                            ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  while (Bit_select) {
    if (fC->Type(Bit_select) == VObjectType::slBit_select ||
        fC->Type(Bit_select) == VObjectType::slConstant_bit_select ||
        fC->Type(Bit_select) == VObjectType::slConstant_primary) {
      if (NodeId bitexp = fC->Child(Bit_select)) {
        UHDM::bit_select* bit_select = s.MakeBit_select();
        bit_select->VpiName(name);
        bit_select->VpiIndex((expr*)compileExpression(
            component, fC, bitexp, compileDesign, pexpr, instance));
        result = bit_select;
        break;
      }
    } else if (fC->Type(Bit_select) == VObjectType::slPart_select_range ||
               fC->Type(Bit_select) == VObjectType::slConstant_part_select_range) {
      NodeId Constant_range = fC->Child(Bit_select);
      result = compilePartSelectRange(component, fC, Constant_range, name,
                                      compileDesign, pexpr, instance);
      break;
    } else if (fC->Type(Bit_select) == VObjectType::slStringConst) {
      std::string hname = name + "." + fC->SymName(Bit_select);
      ref_obj* ref = s.MakeRef_obj();
      ref->VpiName(hname);
      ref->VpiFile(fC->getFileName());
      ref->VpiLineNo(fC->Line(Bit_select));
      result = ref;
    }
    Bit_select = fC->Sibling(Bit_select);
  }
  return result;
}

UHDM::any* CompileHelper::compileExpression(DesignComponent* component, FileContent* fC, NodeId parent,
                                            CompileDesign* compileDesign,
                                            UHDM::any* pexpr,
                                            ValuedComponentI* instance, bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  NodeId child = fC->Child(parent);
  VObjectType parentType = fC->Type(parent);

  if (parentType == VObjectType::slValue_range) {
    UHDM::operation* list_op = s.MakeOperation();
    list_op->VpiOpType(vpiListOp);
    VectorOfany* operands = s.MakeAnyVec();
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
    result = list_op;
    result->VpiFile(fC->getFileName(parent));
    result->VpiLineNo(fC->Line(parent));
    return result;
  } else if (parentType == VObjectType::slNet_lvalue) {
    UHDM::operation* operation = s.MakeOperation();
    UHDM::VectorOfany* operands = s.MakeAnyVec();
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
      if (exp) 
        operands->push_back(exp);
      Expression = fC->Sibling(Expression);
    }
    return result;
  }

  if (child) {
    VObjectType childType = fC->Type(child);
    switch (childType) {
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
        unsigned int vopType = UhdmWriter::getVpiOpType(childType);
        if (vopType) {
          UHDM::operation* op = s.MakeOperation();
          op->VpiOpType(vopType);
          op->VpiParent(pexpr);
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
      case VObjectType::slEdge_Negedge: {
        UHDM::operation* op = s.MakeOperation();
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
        result = compileExpression(component, fC, child, compileDesign, pexpr, instance, reduce);
        break;
      case VObjectType::slComplex_func_call: {
        NodeId name = fC->Child(child);
        NodeId dotedName = fC->Sibling(name);
        if (fC->Type(name) == VObjectType::slDollar_keyword) {
          NodeId Dollar_keyword = name;
          NodeId nameId = fC->Sibling(Dollar_keyword);
          const std::string& name = fC->SymName(nameId);
          if (name == "bits") {
            NodeId List_of_arguments = fC->Sibling(nameId);
            NodeId Expression = fC->Child(List_of_arguments);
            result = compileBits(component, fC, Expression, compileDesign,
                                 pexpr, instance, reduce);
          } else if (name == "clog2") {
            NodeId List_of_arguments = fC->Sibling(nameId);
            result = compileClog2(component, fC, List_of_arguments, compileDesign, pexpr, instance, reduce);
          } else {
            NodeId List_of_arguments = fC->Sibling(nameId);
            UHDM::sys_func_call* sys = s.MakeSys_func_call();
            sys->VpiName("$" + name);
            VectorOfany* arguments = compileTfCallArguments(
                component, fC, List_of_arguments, compileDesign);
            sys->Tf_call_args(arguments);
            result = sys;
          }
        } else if (fC->Type(dotedName) == VObjectType::slStringConst) {
          result = compileExpression(component, fC, name, compileDesign, pexpr, instance, reduce);
        } else if (fC->Type(dotedName) == VObjectType::slSelect ||
                   fC->Type(dotedName) == VObjectType::slConstant_select ||
                   fC->Type(dotedName) == VObjectType::slConstant_expression) {
          NodeId Bit_select = fC->Child(dotedName);
          const std::string& sval = fC->SymName(name);
          result = compileSelectExpression(component, fC, Bit_select, sval, compileDesign, pexpr, instance);
          NodeId selectName = fC->Sibling(dotedName);
          if (selectName) {
          //  bit_setect* select = s.MakeBit_select();
          //  select->
          }
        } else {
          tf_call* call = compileTfCall(component, fC, child, compileDesign);
          result = call;
        }
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
        if (opL) {
          if (opL->VpiParent() == nullptr)
            opL->VpiParent(operation);
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
        }

        UHDM::any* opR =
            compileExpression(component, fC, rval, compileDesign, operation, instance, reduce);
        if (opR) {
          if (opR->VpiParent() == nullptr)
            opR->VpiParent(operation);
          operands->push_back(opR);
        }
        if (opType == VObjectType::slConditional_operator) { // Ternary op
          rval = fC->Sibling(rval);
          opR =
            compileExpression(component, fC, rval, compileDesign, operation, instance, reduce);
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
        const std::string& name = fC->SymName(n);
        if (name == "$bits") {
            NodeId List_of_arguments = fC->Sibling(child);
            NodeId Expression = fC->Child(List_of_arguments);
            result = compileBits(component, fC, Expression, compileDesign,
                                 pexpr, instance, reduce);
        } else {
          UHDM::sys_func_call* sys = s.MakeSys_func_call();
          sys->VpiName(name);
          sys->VpiParent(pexpr);
          NodeId argListNode = fC->Sibling(child);
          VectorOfany* arguments =
              compileTfCallArguments(component, fC, argListNode, compileDesign);
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
            result = operation;
            operation->VpiParent(pexpr);
            operation->VpiOpType(vopType);
            operation->Operands(operands);
            operands->push_back(variable);
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
      case VObjectType::slConstant_cast:
      case VObjectType::slCast: {
        UHDM::operation* operation = s.MakeOperation();
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        operation->Operands(operands);
        operation->VpiOpType(vpiCastOp);
        NodeId Casting_type = fC->Child(child);
        NodeId Simple_type = fC->Child(Casting_type);
        UHDM::typespec* tps = compileTypespec(component, fC, Simple_type, compileDesign, operation, instance, reduce);
        NodeId Expression = fC->Sibling(Casting_type);
        UHDM::any* operand =
            compileExpression(component, fC, Expression, compileDesign, operation, instance, reduce);
        if (operand)    
          operands->push_back(operand);    
        operation->Typespec(tps);  
        result = operation;
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
          else 
            name = fC->SymName(fC->Child(child));  
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
        std::string value = fC->SymName(child);
        c->VpiDecompile(value);
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
        c->VpiDecompile(value);
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
        c->VpiDecompile("'b1");
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
        c->VpiDecompile("'b0");
        result = c;
        break;
      }
      case VObjectType::slStringLiteral: {
        UHDM::constant* c = s.MakeConstant();
        std::string value = fC->SymName(child);
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
        NodeId Constant_expression = fC->Child(Slice_size);
        NodeId Stream_concatenation = fC->Sibling(Slice_size);
        NodeId Stream_expression = fC->Child(Stream_concatenation);
        NodeId Expression = fC->Child(Stream_expression);
        UHDM::operation* operation = s.MakeOperation();
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        result = operation;
        operation->VpiParent(pexpr);
        operation->Operands(operands);
        if (fC->Type(Stream_direction) == VObjectType::slBinOp_ShiftRight)
          operation->VpiOpType(vpiStreamLROp);
        else 
          operation->VpiOpType(vpiStreamRLOp);
        UHDM::any* exp_slice = compileExpression(component, fC, Constant_expression, compileDesign, pexpr, instance, reduce);
        if (exp_slice) 
          operands->push_back(exp_slice);
        UHDM::any* exp_var = compileExpression(component, fC, Expression, compileDesign, pexpr, instance, reduce);
        if (exp_var) 
          operands->push_back(exp_var);  
        break;
      }
      case VObjectType::slConstant_concatenation: 
      case VObjectType::slConcatenation: {
        UHDM::operation* operation = s.MakeOperation();
        UHDM::VectorOfany* operands = s.MakeAnyVec();
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
        } else {
          NodeId List_of_arguments = fC->Sibling(nameId);
          UHDM::sys_func_call* sys = s.MakeSys_func_call();
          sys->VpiName("$" + name);
          VectorOfany *arguments = compileTfCallArguments(component, fC, List_of_arguments, compileDesign);
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
            VObjectType opType = fC->Type(op);
            unsigned int vopType = UhdmWriter::getVpiOpType(opType);
            if (vopType) {
              UHDM::operation* operation = s.MakeOperation();
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
  
  if (result == nullptr) {
    NodeId the_node; 
    if (child) {
      the_node = child;
    } else {
      the_node = parent;
    } 
    VObjectType exprtype = fC->Type(the_node);
    if ((exprtype != VObjectType::slEnd)) {
      unsupported_expr* exp = s.MakeUnsupported_expr();
      std::string fileContent = FileUtils::getFileContent(fC->getFileName());
      std::string lineText = StringUtils::getLineInString(fileContent, fC->Line(the_node));
      exp->VpiValue("STRING:" + lineText);
      exp->VpiFile(fC->getFileName(the_node));
      exp->VpiLineNo(fC->Line(the_node));
      exp->VpiParent(pexpr);
      result = exp;
      //std::cout << "UNSUPPORTED EXPRESSION: " << fC->getFileName(the_node) << ":" << fC->Line(the_node) << ":" << std::endl;
      //std::cout << " -> " << fC->printObject(the_node) << std::endl;
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
          switch (op->VpiOpType()) {
            case vpiArithRShiftOp:
            case vpiRShiftOp: {
              if (operands.size() == 2) {
                int val = get_value((constant*)(operands[0])) >> get_value((constant*)(operands[1]));
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
                int val = get_value((constant*)(operands[0])) << get_value((constant*)(operands[1]));
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
                int val = get_value((constant*)(operands[0])) + get_value((constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiMinusOp: {
              if (operands.size() == 1) {
                int val = - get_value((constant*)(operands[0]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiSubOp: {
              if (operands.size() == 2) {
                int val = get_value((constant*)(operands[0])) - get_value((constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiMultOp: {
              if (operands.size() == 2) {
                int val = get_value((constant*)(operands[0])) * get_value((constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiModOp: {
              if (operands.size() == 2) {
                int val = get_value((constant*)(operands[0])) % get_value((constant*)(operands[1]));
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                result = c;
              }
              break;
            }
            case vpiDivOp: {
              if (operands.size() == 2) {
                int divisor = get_value((constant*)operands[1]);
                if (divisor) {
                  int val = get_value((constant*)(operands[0])) / divisor;
                  UHDM::constant* c = s.MakeConstant();
                  c->VpiValue("INT:" + std::to_string(val));
                  c->VpiDecompile(std::to_string(val));
                  result = c;
                }
              }
              break;
            }
            default:
              break;
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

UHDM::any* CompileHelper::compileAssignmentPattern(DesignComponent* component, FileContent* fC, NodeId Assignment_pattern, 
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

std::vector<UHDM::range*>* CompileHelper::compileRanges(DesignComponent* component, FileContent* fC, NodeId Packed_dimension, 
                                       CompileDesign* compileDesign,
                                       UHDM::any* pexpr,
                                       ValuedComponentI* instance, bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  VectorOfrange* ranges = nullptr;
  if (Packed_dimension && (fC->Type(Packed_dimension) == VObjectType::slPacked_dimension)) {
    ranges = s.MakeRangeVec();
    while (Packed_dimension) {
      NodeId Constant_range = fC->Child(Packed_dimension);
      if (fC->Type(Constant_range) == VObjectType::slConstant_range) { 
        NodeId lexpr = fC->Child(Constant_range);
        NodeId rexpr = fC->Sibling(lexpr);
        range* range = s.MakeRange();
        expr* lexp = nullptr;
        expr* rexp = nullptr;
        if (reduce) {
          Value* leftV = m_exprBuilder.evalExpr(fC, lexpr, instance, true);
          Value* rightV = m_exprBuilder.evalExpr(fC, rexpr, instance, true);
          if (leftV->isValid()) {
            constant* lexpc = s.MakeConstant();
            lexpc->VpiSize(32);
            lexpc->VpiConstType(vpiIntConst);
            lexpc->VpiValue(leftV->uhdmValue());
            lexpc->VpiDecompile(leftV->decompiledValue());
            lexpc->VpiFile(fC->getFileName());
            lexpc->VpiLineNo(fC->Line(lexpr));
            lexp = lexpc;
          }
          if (rightV->isValid()) {
            constant* rexpc = s.MakeConstant();
            rexpc->VpiSize(32);
            rexpc->VpiConstType(vpiIntConst);
            rexpc->VpiValue(rightV->uhdmValue());
            rexpc->VpiDecompile(rightV->decompiledValue());
            rexpc->VpiFile(fC->getFileName());
            rexpc->VpiLineNo(fC->Line(rexpr));
            rexp = rexpc;
          }
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
      }
      Packed_dimension = fC->Sibling(Packed_dimension);
    }
  }
  return ranges;
}

UHDM::any* CompileHelper::compilePartSelectRange(DesignComponent* component, FileContent* fC, NodeId Constant_range, 
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
        UHDM::enum_typespec* sts = (UHDM::enum_typespec*) typespec;
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
      unsigned int lv = get_value(ran->Left_expr());
      unsigned int rv = get_value(ran->Right_expr());
      if (lv > rv)
        bits = bits * (lv - rv + 1);
      else
        bits = bits * (rv - lv + 1);
    }
  }
  return bits;
}

const typespec* CompileHelper::getTypespec(DesignComponent* component, FileContent* fC,
                              NodeId id, CompileDesign* compileDesign, ValuedComponentI* instance, bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  DataType* dtype = nullptr;
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
    dtype = component->getDataType(basename);
  }
  if (dtype == nullptr) {
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
        NodeId range = sig->getRange();
        if (fC->Type(range) != VObjectType::slNull_rule) {
          NodeId DataType = fC->Parent(range);
          result = compileTypespec(component, fC, DataType, compileDesign, nullptr, instance, true);
        }
      }
    }
  }
  while (dtype) {
    TypeDef* typed = dynamic_cast<TypeDef*>(dtype);
    if (typed) {
      DataType* dt = typed->getDataType();
      Enum* en = dynamic_cast<Enum*>(dt);
      if (en) {
        result = en->getTypespec();
        break;
      }
      Struct* st = dynamic_cast<Struct*>(dt);
      if (st) {
        result = st->getTypespec();
        if (suffixname != "") {
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
      Union* un = dynamic_cast<Union*>(dt);
      if (un) {
        result = un->getTypespec();
        break;
      }
      SimpleType* sit = dynamic_cast<SimpleType*>(dt);
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

UHDM::any* CompileHelper::compileBits(DesignComponent* component, FileContent* fC,
                         NodeId Expression,
                         CompileDesign* compileDesign, UHDM::any* pexpr,
                         ValuedComponentI* instance, bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
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
    VectorOfany *arguments = compileTfCallArguments(component, fC, Expression, compileDesign);
    sys->Tf_call_args(arguments);
    result = sys;
  }

  return result;
}

UHDM::any* CompileHelper::compileClog2(DesignComponent* component, FileContent* fC,
                         NodeId Expression,
                         CompileDesign* compileDesign, UHDM::any* pexpr,
                         ValuedComponentI* instance, bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;

  expr* operand = (expr*) compileExpression(component, fC, Expression, compileDesign, pexpr, instance, reduce);
  int val = get_value(operand);
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
    VectorOfany *arguments = compileTfCallArguments(component, fC, Expression, compileDesign);
    sys->Tf_call_args(arguments);
    result = sys;
  }
  return result;
}
