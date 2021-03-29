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
 * File:   ExprBuilder.cpp
 * Author: alain
 *
 * Created on November 2, 2017, 9:45 PM
 */
#include <string.h>
#if defined(_MSC_VER)
  #define strcasecmp _stricmp
  #define strdup _strdup
#else
  #include <strings.h>
#endif
#include <bitset> 
#include <stdint.h>
#include <iostream>
#include <sstream>
#include <math.h>
#include <assert.h>
#include "Utils/StringUtils.h"
#include "Utils/NumUtils.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Expression/ExprBuilder.h"
#include "SourceCompile/VObjectTypes.h"
#include "Design/Design.h"
#include "Utils/StringUtils.h"

using namespace SURELOG;

Value* ExprBuilder::clone(Value* val) {
  Value* clone = NULL;
  if (StValue* v = dynamic_cast<StValue*>(val)) {
    clone = m_valueFactory.newValue(*v);
  } else if (LValue* v = dynamic_cast<LValue*>(val)) {
    clone = m_valueFactory.newValue(*v);
  } else if (SValue* v = dynamic_cast<SValue*>(val)) {
    clone = m_valueFactory.newValue(*v);
  }
  return clone;
}

Value* ExprBuilder::evalExpr(const FileContent* fC, NodeId parent,
                             ValuedComponentI* instance, bool muteErrors) {
  Value* value = m_valueFactory.newLValue();
  NodeId child = fC->Child(parent);
  if (child) {
    VObjectType childType = fC->Type(child);
    switch (childType) {
      case VObjectType::slIncDec_PlusPlus:  {
        // Pre increment
        NodeId sibling = fC->Sibling(child);
        Value* tmp = evalExpr(fC, sibling, instance, muteErrors);
        value->u_plus(tmp);
        value->incr();
        m_valueFactory.deleteValue(tmp);
        break;
      }
      case VObjectType::slIncDec_MinusMinus:  {
        // Pre decrement
        NodeId sibling = fC->Sibling(child);
        Value* tmp = evalExpr(fC, sibling, instance, muteErrors);
        value->u_plus(tmp);
        value->decr();
        m_valueFactory.deleteValue(tmp);
        break;
      }
      case VObjectType::slUnary_Minus: {
        NodeId sibling = fC->Sibling(child);
        Value* tmp = evalExpr(fC, sibling, instance, muteErrors);
        value->u_minus(tmp);
        m_valueFactory.deleteValue(tmp);
        break;
      }
      case VObjectType::slUnary_Plus: {
        NodeId sibling = fC->Sibling(child);
        Value* tmp = evalExpr(fC, sibling, instance, muteErrors);
        value->u_plus(tmp);
        m_valueFactory.deleteValue(tmp);
        break;
      }
      case VObjectType::slUnary_Not: {
        NodeId sibling = fC->Sibling(child);
        Value* tmp = evalExpr(fC, sibling, instance, muteErrors);
        value->u_not(tmp);
        m_valueFactory.deleteValue(tmp);
        break;
      }
      case VObjectType::slUnary_Tilda: {
        NodeId sibling = fC->Sibling(child);
        Value* tmp = evalExpr(fC, sibling, instance, muteErrors);
        value->u_tilda(tmp);
        m_valueFactory.deleteValue(tmp);
        break;
      }
      case VObjectType::slUnary_BitwAnd: {
        NodeId sibling = fC->Sibling(child);
        Value* tmp = evalExpr(fC, sibling, instance, muteErrors);
        value->u_bitwAnd(tmp);
        m_valueFactory.deleteValue(tmp);
        break;
      }
      case VObjectType::slUnary_BitwOr: {
        NodeId sibling = fC->Sibling(child);
        Value* tmp = evalExpr(fC, sibling, instance, muteErrors);
        value->u_bitwOr(tmp);
        m_valueFactory.deleteValue(tmp);
        break;
      }
      case VObjectType::slUnary_BitwXor: {
        NodeId sibling = fC->Sibling(child);
        Value* tmp = evalExpr(fC, sibling, instance, muteErrors);
        value->u_bitwXor(tmp);
        m_valueFactory.deleteValue(tmp);
        break;
      }
      case VObjectType::slConstant_primary:
        m_valueFactory.deleteValue(value);
        value = evalExpr(fC, child, instance, muteErrors);
        break;
      case VObjectType::slPrimary_literal:
        m_valueFactory.deleteValue(value);
        value = evalExpr(fC, child, instance, muteErrors);
        break;
      case VObjectType::slPrimary:
        m_valueFactory.deleteValue(value);
        value = evalExpr(fC, child, instance, muteErrors);
        break;
      case VObjectType::slUnpacked_dimension:
        // Only works for the case of constant_expression, not range
        m_valueFactory.deleteValue(value);
        value = evalExpr(fC, child, instance, muteErrors);
        break;
      case VObjectType::slInc_or_dec_expression:
        m_valueFactory.deleteValue(value);
        value = evalExpr(fC, child, instance, muteErrors);
        break;
      case VObjectType::slConstant_mintypmax_expression:
        m_valueFactory.deleteValue(value);
        value = evalExpr(fC, child, instance, muteErrors);
        break;
      case VObjectType::slMintypmax_expression:
        m_valueFactory.deleteValue(value);
        value = evalExpr(fC, child, instance, muteErrors);
        break;
      case VObjectType::slParam_expression:
        m_valueFactory.deleteValue(value);
        value = evalExpr(fC, child, instance, muteErrors);
        break;
      case VObjectType::slHierarchical_identifier:  {
        m_valueFactory.deleteValue(value);
        value = evalExpr(fC, child, instance, muteErrors);
        break;
      }
      case VObjectType::slExpression:
      case VObjectType::slConstant_expression: {
        Value* valueL = evalExpr(fC, child, instance, muteErrors);
        NodeId op = fC->Sibling(child);
        if (!op) {
          m_valueFactory.deleteValue(value);
          value = valueL;
          break;
        }
        VObjectType opType = fC->Type(op);
        switch (opType) {
          case VObjectType::slBinOp_Plus: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->plus(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_Minus: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->minus(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_Mult: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->mult(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_MultMult: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->power(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slQmark:
          case VObjectType::slConditional_operator: {
            long long v = valueL->getValueL();
            m_valueFactory.deleteValue(valueL);
            NodeId Expression = fC->Sibling(op);
            NodeId ConstantExpr = fC->Sibling(Expression);
            if (v) {
              value = evalExpr(fC, Expression, instance, muteErrors);
            } else {
              value = evalExpr(fC, ConstantExpr, instance, muteErrors);
            }
            break;
          }
          case VObjectType::slBinOp_Div: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->div(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_Great: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->greater(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_GreatEqual: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->greater_equal(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_Less: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->lesser(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_LessEqual: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->lesser_equal(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_Equiv: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            if ((valueL->getType() == Value::Type::String) && (valueR->getType() == Value::Type::String)) {
              m_valueFactory.deleteValue(value);
              value = m_valueFactory.newStValue();
            }
            value->equiv(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_Not: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            if ((valueL->getType() == Value::Type::String) && (valueR->getType() == Value::Type::String)) {
              m_valueFactory.deleteValue(value);
              value = m_valueFactory.newStValue();
            }
            value->notEqual(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_Percent: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->mod(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_LogicAnd: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->logAnd(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_LogicOr: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->logOr(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_BitwAnd: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->bitwAnd(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_BitwOr: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->bitwOr(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_BitwXor: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->bitwXor(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_ShiftLeft: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->shiftLeft(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          case VObjectType::slBinOp_ShiftRight: {
            NodeId rval = fC->Sibling(op);
            Value* valueR = evalExpr(fC, rval, instance, muteErrors);
            value->shiftRight(valueL, valueR);
            m_valueFactory.deleteValue(valueL);
            m_valueFactory.deleteValue(valueR);
            break;
          }
          default:
            m_valueFactory.deleteValue(value);
            value = valueL;
            break;
        }
      } break;
      case VObjectType::slIntConst: {
        std::string val = fC->SymName(child);
        std::string size = val;
        StringUtils::rtrim(size, '\'');
        int64_t intsize = 0;
        if (size != "") 
          intsize = std::strtoull(size.c_str(), 0, 10);
        if (strstr(val.c_str(), "'")) {
          uint64_t hex_value = 0;
          char base = 'h';
          unsigned int i = 0;
          for (i = 0; i < val.size(); i++) {
            if (val[i] == '\'') {
              base = val[i + 1];
              break;
            }
          }
          std::string v = val.substr(i + 2);
          v = StringUtils::replaceAll(v, "_", "");
          bool intformat = false;
          switch (base) {
            case 'h': {
              if (intsize > 64) {
                m_valueFactory.deleteValue(value);
                StValue* stval = (StValue*) m_valueFactory.newStValue();
                stval->set(v, Value::Type::Hexadecimal, intsize);
                value = stval;
              } else {
                hex_value = std::strtoull(v.c_str(), 0, 16);
                intformat = true;
              }
              break;
            }
            case 'b':
              hex_value = std::strtoull(v.c_str(), 0, 2);
              intformat = true;
              break;
            case 'o':
              hex_value = std::strtoull(v.c_str(), 0, 8);
              intformat = true;
              break;
            case 'd':
              hex_value = std::strtoull(v.c_str(), 0, 10);
              intformat = true;
              break;
            default:
              // '1
              hex_value = std::strtoull(v.c_str(), 0, 2);
              intformat = true;
              break;
          }
          if (intformat) {
            if (size == "")
              value->set(hex_value, Value::Type::Integer, 0);
            else 
              value->set(hex_value, Value::Type::Unsigned, intsize); 
          }
        } else {
          if (val.size() && (val[0] == '-')) {
            int64_t i = std::strtoll(val.c_str(), 0, 10);
            value->set(i);
          } else {
            if (uint64_t i = std::strtoull(val.c_str(), 0, 10)) {
              value->set(i);
            } else {
              uint64_t j = atoll(val.c_str());
              value->set(j);
            }
          }
        }
        break;
      }
      case VObjectType::slRealConst: {
        std::string real = fC->SymName(child).c_str();
        std::istringstream os(real);
        double d;
        os >> d;
        value->set(d);
        break;
      }
      case VObjectType::slNull_keyword: {
        value->set((uint64_t)0);
        break;
      }
      case VObjectType::slPackage_scope:
      case VObjectType::slStringConst: {
        Value* sval = NULL;
        std::string fullName;
        if (childType == VObjectType::slPackage_scope) {
          const std::string& packageName = fC->SymName(fC->Child(child));
          const std::string& name = fC->SymName(fC->Sibling(child));
          if (m_design) {
            Package* pack = m_design->getPackage(packageName);
            if (pack) {
              if (pack->getComplexValue(name)) {
                muteErrors = true;
                value->setInvalid();
                break;
              } else {
                sval = pack->getValue(name);
              }
            }
          }
          if (sval == NULL)
            fullName = packageName + "::" + name;
        } else {
          const std::string& name = fC->SymName(child);
          if (instance) {
            if (instance->getComplexValue(name)) {
              muteErrors = true;
              value->setInvalid();
              break;
            } else {
              sval = instance->getValue(name, *this);
            }
          }
          if (sval == NULL)
            fullName = name;
        }

        if (sval == NULL) {
          if (muteErrors == false) {
            Location loc(fC->getFileId(child), fC->Line(child), 0,
                         m_symbols->registerSymbol(fullName));
            Error err(ErrorDefinition::ELAB_UNDEF_VARIABLE, loc);
            m_errors->addError(err);
          }
          value->setInvalid();
          break;
        }
        if (sval->getType() == Value::Type::String ||
            sval->getType() == Value::Type::Hexadecimal) {
          m_valueFactory.deleteValue(value);
          value = clone(sval);
        } else {
          value->u_plus(sval);
        }
        break;
      }
      case VObjectType::slStringLiteral: {
        std::string name = fC->SymName(child).c_str();
        m_valueFactory.deleteValue(value);
        value = m_valueFactory.newStValue();
        if (name.front() == '"' && name.back() == '"')
          name = name.substr(1, name.length() - 2);
        value->set(name);
        break;
      }
      case VObjectType::slNumber_1Tickb0:
      case VObjectType::slNumber_1TickB0:
      case VObjectType::slInitVal_1Tickb0:
      case VObjectType::slInitVal_1TickB0:
      case VObjectType::slScalar_1Tickb0:
      case VObjectType::slScalar_1TickB0: {
        value->set(0,Value::Type::Scalar, 1);
        break;
      }
      case VObjectType::slNumber_Tickb0:
      case VObjectType::slNumber_TickB0:
      case VObjectType::slNumber_Tick0:
      case VObjectType::slScalar_Tickb0:
      case VObjectType::slScalar_TickB0:
      case VObjectType::sl0: {
        value->set(0,Value::Type::Scalar, 0);
        break;
      }
      case VObjectType::slNumber_1Tickb1:
      case VObjectType::slNumber_1TickB1:
      case VObjectType::slInitVal_1Tickb1:
      case VObjectType::slInitVal_1TickB1:
      case VObjectType::slScalar_1Tickb1:
      case VObjectType::slScalar_1TickB1: {
        value->set(1,Value::Type::Scalar, 1);
        break;
      }
      case VObjectType::slNumber_Tickb1:
      case VObjectType::slNumber_TickB1:
      case VObjectType::slNumber_Tick1:
      case VObjectType::slScalar_Tickb1:
      case VObjectType::slScalar_TickB1:
      case VObjectType::sl1: {
        value->set(1,Value::Type::Scalar, 0);
        break;
      }
      case VObjectType::slVariable_lvalue: {
        Value* variableVal = evalExpr(fC, child, instance, muteErrors);
        NodeId sibling = fC->Sibling(child);
        if (sibling) {
          VObjectType opType = fC->Type(sibling);
          if (opType == VObjectType::slIncDec_PlusPlus)
            variableVal->incr();
          else if (opType == VObjectType::slIncDec_MinusMinus)
            variableVal->decr();
        }
        m_valueFactory.deleteValue(value);
        value = variableVal;
        break;
      }
      case VObjectType::slSubroutine_call: {
        NodeId dollar = fC->Child(child);
        NodeId function = fC->Sibling(dollar);
        NodeId List_of_arguments = fC->Sibling(function);
        NodeId Expression = fC->Child(List_of_arguments);
        std::vector<Value*> args;
        while (Expression) {
           args.push_back( evalExpr(fC, Expression, instance, muteErrors));
           Expression = fC->Sibling(Expression);
        }
        std::string funcName = fC->SymName(function);
        if (funcName == "clog2") {
          int val = args[0]->getValueL();
          val = val-1;
          if (val < 0) {
            value->set((int64_t) 0);
            value->setInvalid();
            break;
          }
          int clog2=0;
          for (; val>0; clog2=clog2+1) {
            val = val>>1;
          }
          value->set((int64_t) clog2);
        } else if (funcName == "ln") {
          int val = args[0]->getValueL();
          value->set((int64_t) log(val));
        } else if (funcName == "clog") {
          int val = args[0]->getValueL();
          value->set((int64_t) log10(val));
        } else if (funcName == "exp") {
          int val = args[0]->getValueL();
          value->set((int64_t) exp2(val));
        } else if (funcName == "bits") {
          // $bits is implemented in compileExpression.cpp
          value->set((int64_t) 0);
          value->setInvalid();
        } else {
          value->set((int64_t) 0);
          value->setInvalid();
        }
        break;
      }
      case VObjectType::slConstant_concatenation: {
        NodeId Constant_expression = fC->Child(child);
        char base = 'h';
        std::string svalue;
        while (Constant_expression) {
          NodeId Constant_primary = fC->Child(Constant_expression);
          NodeId Primary_literal = fC->Child(Constant_primary);
          NodeId ConstVal = fC->Child(Primary_literal);
          std::string token;
          if (fC->Type(ConstVal) == slIntConst) {
            token = fC->SymName(ConstVal);
          } else {
            Value* constVal = evalExpr(fC, Primary_literal, instance, muteErrors);
            unsigned long long v = constVal->getValueUL();
            token = NumUtils::toBinary(constVal->getSize(), v);
          }
          if (strstr(token.c_str(), "'")) {
            unsigned int i = 0;
            for (i = 0; i < token.size(); i++) {
              if (token[i] == '\'') {
                base = token[i + 1];
                break;
              }
            }
            std::string v = token.substr(i + 2);
            v = StringUtils::replaceAll(v, "_", "");
            std::string size = token.substr(0, i);
            uint64_t isize = std::strtoull(size.c_str(), 0, 10);
            if (base == 'd') {
              long long iv = std::strtoll(v.c_str(), 0, 10);
              v = NumUtils::toBinary(isize, iv);
            } else if (base == 'h') {
              long long iv = std::strtoll(v.c_str(), 0, 16);
              v = NumUtils::toBinary(isize, iv);
            } else if (base == 'o') {
              long long iv = std::strtoll(v.c_str(), 0, 8);
              v = NumUtils::toBinary(isize, iv);
            }
            unsigned int vsize = v.size();
            if (isize) {
              for (unsigned int i = 0; i < isize - vsize; i++) 
                v = "0" + v;
            }
            svalue += v;
          } else {
            std::string v = token;
            svalue += v;
            base = 'b';
          }
          Constant_expression = fC->Sibling(Constant_expression);
        }
        base = 'b';
        if (svalue == "") {
          value->set((int64_t) 0);
        } else {
          m_valueFactory.deleteValue(value);
          value = m_valueFactory.newStValue();
          value->set(svalue, Value::Type::Binary);
        }
        value->setInvalid(); // We can't distinguish in between concatenation or array initialization in this context
        // so we mark the value as invalid for most purposes. Enum value can still use it as concatenation
        break;
      }
      default:
        value->set((int64_t) 0);
        value->setInvalid();
        break;
    }
  } else {
    VObjectType type = fC->Type(parent);
    switch (type) {
      case VObjectType::slPackage_scope:
      case VObjectType::slStringConst: {
        std::string name;
        if (type == VObjectType::slPackage_scope) {
          name = fC->SymName(fC->Child(parent));
          name += "::" + fC->SymName(fC->Sibling(parent));
        } else {
          name = fC->SymName(parent);
        }
        Value* sval = NULL;
        if (instance) {
          if (instance->getComplexValue(name)) {
            muteErrors = true;
            value->setInvalid();
            break;
          } else {
            sval = instance->getValue(name);
          }
        }
        if (sval == NULL) {
          if (muteErrors == false) {
            Location loc(fC->getFileId(child), fC->Line(child), 0,
                         m_symbols->registerSymbol(name));
            Error err(ErrorDefinition::ELAB_UNDEF_VARIABLE, loc);
            m_errors->addError(err);
          }
          value->setInvalid();
          break;
        }
        NodeId op = fC->Sibling(parent);
        VObjectType op_type = fC->Type(op);
        switch (op_type) {
          case VObjectType::slIncDec_PlusPlus:
            value->u_plus(sval);
            value->incr();
            return value;
          case VObjectType::slIncDec_MinusMinus:
            value->u_plus(sval);
            value->decr();
            return value;
          default:
            break;
        }
        break;
      }
      default:
        break;
    }

    value->setInvalid();
  }
  return value;
}

Value* ExprBuilder::fromVpiValue(const std::string& s) {
  Value* val = nullptr;
  size_t pos;
  if ((pos = s.find("UINT:")) != std::string::npos) {  
    val = m_valueFactory.newLValue();
    uint64_t v = std::strtoull(s.c_str() + pos + strlen("UINT:"), 0 , 10);
    val->set(v);
  } else if ((pos = s.find("INT:")) != std::string::npos) {
    val = m_valueFactory.newLValue();
    int64_t v = std::strtoll(s.c_str() + pos + strlen("INT:"), 0 , 10);
    val->set(v);
  } else if ((pos = s.find("DEC:")) != std::string::npos) {  
    val = m_valueFactory.newLValue();
    int64_t v = std::strtoll(s.c_str() + pos + strlen("DEC:"), 0 , 10);
    val->set(v);
  } else if ((pos = s.find("SCAL:")) != std::string::npos) {
    const char* const parse_pos = s.c_str() + pos + strlen("SCAL:");
    switch (parse_pos[0]) {
      case 'Z':
       
        break;
      case 'X':
       
        break;
      case 'H':
        
        break;
      case 'L':
       
        break;
        // Not really clear what the difference between X and DontCare is.
        // Let's parse 'W'eak don't care as this one.
      case 'W':
        
        break;
      default:
        if (strcasecmp(parse_pos, "DontCare") == 0) {
        
        } else if (strcasecmp(parse_pos, "NoChange") == 0) {
         
        } else {
          int64_t v = std::strtoull(parse_pos, 0, 10);
          val = m_valueFactory.newLValue();
          val->set(v);
        }
        break;
    }
  } else if ((pos = s.find("BIN:")) != std::string::npos) {
    val = m_valueFactory.newLValue();
    uint64_t v = std::strtoull(s.c_str() + pos + strlen("BIN:"), 0, 2);  
    val->set(v, Value::Type::Unsigned,  s.size() - 4);
  } else if ((pos = s.find("HEX:")) != std::string::npos) {
    if (s.size() > 20) { // HEX:FFFFFFFFFFFFFFFF
      StValue* sval = (StValue*) m_valueFactory.newStValue();
      sval->set(s.c_str() + pos + strlen("HEX:"), Value::Type::Hexadecimal, (s.size() - 4) * 4);
      val = sval;
    } else {
      val = m_valueFactory.newLValue();
      uint64_t v = std::strtoull(s.c_str() + pos + strlen("HEX:"), 0, 16);  
      val->set(v, Value::Type::Unsigned, (s.size() - 4) * 4);
    }
  } else if ((pos = s.find("OCT:")) != std::string::npos) {
    val = m_valueFactory.newLValue();
    uint64_t v = std::strtoull(s.c_str() + pos + strlen("OCT:"), 0, 8);  
    val->set(v, Value::Type::Unsigned, (s.size() - 4) * 4);
  } else if ((pos = s.find("STRING:")) != std::string::npos) {
    val = m_valueFactory.newStValue();
    val->set(s.c_str() + pos + strlen("STRING:"));
  } else if ((pos = s.find("REAL:")) != std::string::npos) {
    val = m_valueFactory.newLValue();
    double v = std::strtod(s.c_str() + pos + strlen("REAL:"), 0);
    val->set(v);
  }
  return val;
}

Value* ExprBuilder::fromString(const std::string& value) {
  Value* val = nullptr;
  std::string sval;
  const char *value_ptr = value.c_str();
  char *end_parse_ptr;
  if (strstr(value_ptr, "'")) {
    char base = 'b';
    unsigned int i = 0;
    for (i = 0; i < value.size(); i++) {
      if (value[i] == '\'') {
        base = value[i + 1];
        break;
      }
    }
    sval = value.substr(i + 2);
    sval = StringUtils::replaceAll(sval, "_", "");
    switch (base) {
      case 'h': {
        std::string size = value;
        StringUtils::rtrim(size, '\'');
        int s = atoi(size.c_str());
        StValue* stval = (StValue*) m_valueFactory.newStValue();
        stval->set(sval, Value::Type::Hexadecimal, s);
        val = stval;
        break;
      }
      case 'b': {
        std::string size = value;
        StringUtils::rtrim(size, '\'');
        int s = atoi(size.c_str());
        StValue* stval = (StValue*) m_valueFactory.newStValue();
        stval->set(sval, Value::Type::Binary, s);
        val = stval;
        break;
      }
      case 'o': {
        std::string size = value;
        StringUtils::rtrim(size, '\'');
        int s = atoi(size.c_str());
        StValue* stval = (StValue*) m_valueFactory.newStValue();
        stval->set(sval, Value::Type::Octal, s);
        val = stval;
        break;
      }
      case 'd': {
        std::string size = value;
        StringUtils::rtrim(size, '\'');
        int s = atoi(size.c_str());
        StValue* stval = (StValue*) m_valueFactory.newStValue();
        stval->set(sval, Value::Type::Integer, s);
        val = stval;
        break;
      }
      default: {
        std::string size = value;
        StringUtils::rtrim(size, '\'');
        int s = atoi(size.c_str());
        StValue* stval = (StValue*) m_valueFactory.newStValue();
        stval->set(sval, Value::Type::Binary, s);
        val = stval;
        break;
      }
    }
  } else if (strstr(value_ptr, ".")) {
    long double v = std::strtold(value_ptr, 0);
    val = m_valueFactory.newLValue();
    val->set((double) v);  
  } else if (value.size() && value[0] == '-') {
    int64_t v = std::strtoll(value_ptr, 0, 10);
    val = m_valueFactory.newLValue();
    val->set(v);  
  } else {
    uint64_t v = std::strtoull(value_ptr, &end_parse_ptr, 10);
    if (value_ptr != end_parse_ptr) {
      val = m_valueFactory.newLValue();
      val->set(v);
    } else {
      val = m_valueFactory.newStValue();
      val->set(value);
    }
  }
  return val;
}

bool ExprBuilder::unitTest() {
  bool result = true;
  {
    LValue v0, v1, v2;
    v1.set((int64_t)1); v2.set((int64_t)0);
    v0.bitwAnd(&v1, &v2);
    assert(v0.getValueL() == 0 && "bitwAnd failed");
  }
  {
    LValue v0, v1, v2;
    v1.set((int64_t)1); v2.set((int64_t)0);
    v0.bitwOr(&v1, &v2);
    assert(v0.getValueL() == 1 && "bitwOr failed");
  }
  {
    LValue v0, v1;
    v1.set((int64_t)1);
    v0.u_not(&v1);
    assert(v0.getValueL() == 0 && "u_not failed");
  }
  {
    LValue v0, v1, v2;
    v1.set((int64_t)-1); v2.set((int64_t)1);
    v0.plus(&v1, &v2);
    assert(v0.getValueL() == 0 && "plus failed");
  }
  {
    LValue v0, v1, v2;
    v1.set((int64_t)-10); v2.set((int64_t)9);
    v0.plus(&v1, &v2);
    assert(v0.getValueL() == -1 && "plus failed");
    assert(v0.uhdmValue() == "INT:-1" && "plus failed");
  }
  {
    ValueFactory factory;
    Value* v0 = factory.newStValue();
    v0->set("BLAH");
    assert(v0->uhdmValue() == "STRING:BLAH" && "string val failed");
  }
  {
    ExprBuilder builder;
    Value* v1 = builder.fromVpiValue("HEX:A");
    Value* v2 = builder.fromVpiValue("INT:10");
    LValue v0;
    v0.equiv(v1,v2);
    assert(v1->uhdmValue() == "UINT:10" && "hex convertion failed");
    assert(v0.getValueL() == 1 && "hex convertion failed");
  }
  return result;
}
