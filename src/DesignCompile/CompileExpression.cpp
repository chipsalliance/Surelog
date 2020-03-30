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

using namespace SURELOG;

UHDM::any* CompileHelper::compileExpression(FileContent* fC, NodeId parent, 
					     CompileDesign* compileDesign,
						 UHDM::expr* pexpr,
					     ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  NodeId child = fC->Child(parent);
  if (child) {
    VObjectType childType = fC->Type(child);
    switch (childType) {
	case VObjectType::slUnary_Minus: {
      UHDM::operation* op = s.MakeOperation();
	  op->VpiOpType(vpiMinusOp);
	  op->VpiParent(pexpr);
	  UHDM::VectorOfany* operands = s.MakeAnyVec();
	  operands->push_back(compileExpression(fC, fC->Sibling(child), compileDesign, op, instance));
	  op->Operands(operands);
	  result = op;
	  break;
	}
	case VObjectType::slUnary_Plus: {
      UHDM::operation* op = s.MakeOperation();
	  op->VpiOpType(vpiPlusOp);
	  op->VpiParent(pexpr);
	  UHDM::VectorOfany* operands = s.MakeAnyVec();
	  operands->push_back(compileExpression(fC, fC->Sibling(child), compileDesign, op, instance));
	  op->Operands(operands);
	  result = op;
	  break;
	}
	case VObjectType::slUnary_Tilda: {
      UHDM::operation* op = s.MakeOperation();
	  op->VpiOpType(vpiBitNegOp);
	  op->VpiParent(pexpr);
	  UHDM::VectorOfany* operands = s.MakeAnyVec();
	  operands->push_back(compileExpression(fC, fC->Sibling(child), compileDesign, op, instance));
	  op->Operands(operands);
	  result = op;
	  break;
	}
	case VObjectType::slUnary_Not: {
      UHDM::operation* op = s.MakeOperation();
	  op->VpiOpType(vpiNotOp);
	  op->VpiParent(pexpr);
	  UHDM::VectorOfany* operands = s.MakeAnyVec();
	  operands->push_back(compileExpression(fC, fC->Sibling(child), compileDesign, op, instance));
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
      result = compileExpression(fC, child, compileDesign, pexpr, instance);
      break;
	case VObjectType::slExpression:  
	case VObjectType::slConstant_expression: {
	  UHDM::any* opL = compileExpression(fC, child, compileDesign, pexpr, instance);	  
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
	    opL->VpiParent(operation);
	    operands->push_back(opL);
	  }
	  operation->Operands(operands);
	  NodeId rval = fC->Sibling(op);
	  UHDM::any* opR = compileExpression(fC, rval, compileDesign, operation, instance);
	  if (opR) 	  
        operands->push_back(opR);  
      VObjectType opType = fC->Type(op);
	  unsigned int vopType = UhdmWriter::getVpiOpType(opType);
	  operation->VpiOpType(vopType); 
	  break;
	}
	case VObjectType::slSystem_task_names: {
	  NodeId n = fC->Child(child);
	  std::string name = fC->SymName(n).c_str();
	  UHDM::sys_func_call* sys = s.MakeSys_func_call();
	  sys->VpiName(name);
	  sys->VpiParent(pexpr);
	  result = sys;
	  break;
	}  
    case VObjectType::slStringConst: {
      std::string name = fC->SymName(child).c_str();
	  NodeId rhs = child;
	  while ((rhs = fC->Sibling(rhs))) {
        if (fC->Type(rhs) == VObjectType::slStringConst)
          name += "." + fC->SymName(rhs);
      }
      Value* sval = NULL;
      if (instance) 
        sval = instance->getValue(name);        
      if (sval == NULL) {   
		UHDM::ref_obj* ref = s.MakeRef_obj();  
		ref->VpiName(name);
		ref->VpiParent(pexpr);
		result = ref;   
      } else {
        if (sval->getType() == Value::Type::String) {
        }
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
      Value* sval = NULL;
      if (instance) 
	    sval = instance->getValue(name);
      if (sval == NULL) {      
        break;
      }
      NodeId op = fC->Sibling(parent);
      VObjectType op_type = fC->Type(op);
      switch (op_type) {
      case VObjectType::slIncDec_PlusPlus:
		break;
      case VObjectType::slIncDec_MinusMinus:
        break;
      default:
        break;
      }
      break;
	}
    default:
      break;  
	}
  }

  return result;
}
