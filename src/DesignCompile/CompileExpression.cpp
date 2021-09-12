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
#include <math.h>
#include <string.h>

#include <bitset>
#include <iostream>

#include "CommandLine/CommandLineParser.h"
#include "Design/Design.h"
#include "Design/Enum.h"
#include "Design/Function.h"
#include "Design/ParamAssign.h"
#include "Design/Parameter.h"
#include "Design/SimpleType.h"
#include "Design/Struct.h"
#include "Design/Union.h"
#include "DesignCompile/CompileDesign.h"
#include "DesignCompile/CompileHelper.h"
#include "DesignCompile/UhdmWriter.h"
#include "ElaboratorListener.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Expression/ExprBuilder.h"
#include "Expression/Value.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/PreprocessFile.h"
#include "Testbench/Property.h"
#include "Testbench/TypeDef.h"
#include "Utils/FileUtils.h"
#include "Utils/NumUtils.h"
#include "Utils/StringUtils.h"
#include "clone_tree.h"
#include "expr.h"
#include "headers/ExprEval.h"
#include "uhdm.h"
#include "vpi_visitor.h"

using namespace SURELOG;
using namespace UHDM;

bool CompileHelper::substituteAssignedValue(const UHDM::any* oper,
                                            CompileDesign* compileDesign) {
  bool substitute = true;
  if (!oper) {
    return false;
  }
  UHDM_OBJECT_TYPE opType = oper->UhdmType();
  if (opType == uhdmoperation) {
    operation* op = (operation*)oper;
    int opType = op->VpiOpType();
    if (opType == vpiAssignmentPatternOp || opType == vpiConcatOp) {
      substitute = compileDesign->getCompiler()
                       ->getCommandLineParser()
                       ->getParametersSubstitution();
    }
    for (auto operand : *op->Operands()) {
      if (!substituteAssignedValue(operand, compileDesign)) {
        return false;
      }
    }
  }
  return substitute;
}

expr* CompileHelper::reduceBitSelect(
    expr* op, unsigned int index_val, bool& invalidValue,
    DesignComponent* component, CompileDesign* compileDesign,
    ValuedComponentI* instance, const std::string& fileName, int lineNumber,
    any* pexpr, bool muteErrors) {
  Serializer& s = compileDesign->getSerializer();
  expr* result = nullptr;
  expr* exp = reduceExpr(op, invalidValue, component, compileDesign, instance,
                         fileName, lineNumber, pexpr, muteErrors);
  if (exp && (exp->UhdmType() == uhdmconstant)) {
    int64_t val = get_value(invalidValue, exp);
    std::string binary = NumUtils::toBinary(exp->VpiSize(), val);
    constant* c = s.MakeConstant();
    unsigned short lr = 0;
    unsigned short rr = 0;
    if (const typespec* tps = exp->Typespec()) {
      if (tps->UhdmType() == uhdmlogic_typespec) {
        logic_typespec* lts = (logic_typespec*)tps;
        VectorOfrange* ranges = lts->Ranges();
        if (ranges) {
          range* r = ranges->at(0);
          bool invalidValue = false;
          lr = get_value(invalidValue, r->Left_expr());
          rr = get_value(invalidValue, r->Right_expr());
        }
      }
    }
    c->VpiSize(1);
    if (index_val < binary.size()) {
      // TODO: If range does not start at 0
      if (lr > rr) {
        index_val = binary.size() - index_val - 1;
      }
      char bitv = binary[index_val];
      int v = bitv - '0';
      c->VpiValue("BIN:" + std::to_string(v));
      c->VpiDecompile("1'b" + std::to_string(v));
      c->VpiConstType(vpiBinaryConst);
    } else {
      c->VpiValue("BIN:0");
      c->VpiDecompile("1'b0");
      c->VpiConstType(vpiBinaryConst);
    }
    c->VpiFile(fileName);
    c->VpiLineNo(lineNumber);
    c->VpiColumnNo(op->VpiColumnNo());
    c->VpiEndLineNo(lineNumber);
    c->VpiEndColumnNo(op->VpiColumnNo() + 1);
    result = c;
  }
  return result;
}

any* CompileHelper::getObject(const std::string& name,
                              DesignComponent* component,
                              CompileDesign* compileDesign,
                              ValuedComponentI* instance, const any* pexpr) {
  any* result = nullptr;
  while (pexpr) {
    if (const UHDM::scope* s = any_cast<const scope*>(pexpr)) {
      if ((result == nullptr) && s->Variables()) {
        for (auto o : *s->Variables()) {
          if (o->VpiName() == name) {
            result = o;
            break;
          }
        }
      }
    }
    if (const UHDM::task_func* s = any_cast<const task_func*>(pexpr)) {
      if ((result == nullptr) && s->Io_decls()) {
        for (auto o : *s->Io_decls()) {
          if (o->VpiName() == name) {
            result = o;
            break;
          }
        }
      }
    }
    if (result) break;
    pexpr = pexpr->VpiParent();
  }
  if ((result == nullptr) && instance) {
    if (ModuleInstance* inst =
            valuedcomponenti_cast<ModuleInstance*>(instance)) {
      if (expr* complex = instance->getComplexValue(name)) {
        result = complex;
      }
      Netlist* netlist = inst->getNetlist();
      if (netlist) {
        if ((result == nullptr) && netlist->array_nets()) {
          for (auto o : *netlist->array_nets()) {
            if (o->VpiName() == name) {
              result = o;
              break;
            }
          }
        }
        if ((result == nullptr) && netlist->nets()) {
          for (auto o : *netlist->nets()) {
            if (o->VpiName() == name) {
              result = o;
              break;
            }
          }
        }
        if ((result == nullptr) && netlist->variables()) {
          for (auto o : *netlist->variables()) {
            if (o->VpiName() == name) {
              result = o;
              break;
            }
          }
        }
        if ((result == nullptr) && netlist->ports()) {
          for (auto o : *netlist->ports()) {
            if (o->VpiName() == name) {
              result = o;
              break;
            }
          }
        }
        if ((result == nullptr) && netlist->param_assigns()) {
          for (auto o : *netlist->param_assigns()) {
            const std::string& pname = o->Lhs()->VpiName();
            if (pname == name) {
              result = o;
              break;
            }
          }
        }
      }
    }
  }
  // Instance component or package component
  if ((result == nullptr) && component) {
    for (ParamAssign* pass : component->getParamAssignVec()) {
      if (param_assign* p = pass->getUhdmParamAssign()) {
        const std::string& pname = p->Lhs()->VpiName();
        if (pname == name) {
          if (substituteAssignedValue(p->Rhs(), compileDesign)) {
            result = (any*)p->Rhs();
            break;
          }
        }
      }
    }
    const DataType* dtype = component->getDataType(name);
    if ((result == nullptr) && dtype) {
      dtype = dtype->getActual();
      if (dtype->getTypespec()) result = dtype->getTypespec();
    }
  }

  if ((result == nullptr) && instance) {
    if (ModuleInstance* inst =
            valuedcomponenti_cast<ModuleInstance*>(instance)) {
      // Instance component
      if (DesignComponent* comp = inst->getDefinition()) {
        for (ParamAssign* pass : comp->getParamAssignVec()) {
          if (param_assign* p = pass->getUhdmParamAssign()) {
            const std::string& pname = p->Lhs()->VpiName();
            if (pname == name) {
              if (substituteAssignedValue(p->Rhs(), compileDesign)) {
                result = (any*)p->Rhs();
                break;
              }
            }
          }
        }
        const DataType* dtype = comp->getDataType(name);
        if ((result == nullptr) && dtype) {
          dtype = dtype->getActual();
          if (dtype->getTypespec()) result = dtype->getTypespec();
        }
      }
    }
  }

  if (result && (result->UhdmType() == uhdmref_obj)) {
    ref_obj* ref = (ref_obj*)result;
    const std::string& refname = ref->VpiName();
    result = getObject(refname, component, compileDesign, instance, pexpr);
  }
  return result;
}

UHDM::task_func* getFuncFromPackage(const std::string& name,
                                    DesignComponent* component,
                                    std::set<DesignComponent*>& visited) {
  for (Package* pack : component->getAccessPackages()) {
    if (pack->getTask_funcs()) {
      for (UHDM::task_func* tf : *pack->getTask_funcs()) {
        if (tf->VpiName() == name) {
          return tf;
        }
      }
    }
    if (visited.find(pack) == visited.end()) {
      visited.insert(pack);
      UHDM::task_func* res = getFuncFromPackage(name, pack, visited);
      if (res) {
        return res;
      }
    }
  }
  return nullptr;
}

std::pair<UHDM::task_func*, DesignComponent*> CompileHelper::getTaskFunc(
    const std::string& name, DesignComponent* component,
    CompileDesign* compileDesign, any* pexpr) {
  std::pair<UHDM::task_func*, DesignComponent*> result = {nullptr, nullptr};
  DesignComponent* comp = component;
  if (strstr(name.c_str(), "::")) {
    std::vector<std::string> res;
    StringUtils::tokenizeMulti(name, "::", res);
    if (res.size() > 1) {
      const std::string& packName = res[0];
      const std::string& funcName = res[1];
      Design* design = compileDesign->getCompiler()->getDesign();
      if (Package* pack = design->getPackage(packName)) {
        if (pack->getTask_funcs()) {
          for (UHDM::task_func* tf : *pack->getTask_funcs()) {
            if (tf->VpiName() == funcName) {
              result = std::make_pair(tf, pack);
              return result;
            }
          }
        }
      }
    }
  }
  while (comp) {
    if (comp->getTask_funcs()) {
      for (UHDM::task_func* tf : *comp->getTask_funcs()) {
        if (tf->VpiName() == name) {
          result = std::make_pair(tf, component);
          return result;
        }
      }
    }
    comp = valuedcomponenti_cast<DesignComponent*>(
        (DesignComponent*)comp->getParentScope());
  }
  if (component) {
    for (const FileContent* cfC : component->getFileContents()) {
      FileContent* fC = (FileContent*)cfC;
      if (fC->getTask_funcs()) {
        for (UHDM::task_func* tf : *fC->getTask_funcs()) {
          if (tf->VpiName() == name) {
            result = std::make_pair(tf, component);
            return result;
          }
        }
      }
    }
  }
  if (component) {
    std::set<DesignComponent*> visited;
    task_func* res = getFuncFromPackage(name, component, visited);
    if (res) {
      result = std::make_pair(res, component);
      return result;
    }
  }
  Design* design = compileDesign->getCompiler()->getDesign();
  auto& all_files = design->getAllFileContents();
  for (auto file : all_files) {
    FileContent* fC = file.second;
    if (fC->getTask_funcs()) {
      for (UHDM::task_func* tf : *fC->getTask_funcs()) {
        if (tf->VpiName() == name) {
          result = std::make_pair(tf, component);
          return result;
        }
      }
    }
  }
  return result;
}

bool getStringVal(std::string& result, expr* val) {
  const UHDM::constant* hs0 = any_cast<const UHDM::constant*>(val);
  if (hs0) {
    s_vpi_value* sval = String2VpiValue(hs0->VpiValue());
    if (sval) {
      if (sval->format == vpiStringVal) {
        result = sval->value.str;
        return true;
      }
    }
  }
  return false;
}

constant* compileConst(const FileContent* fC, NodeId child, Serializer& s) {
  VObjectType objtype = fC->Type(child);
  constant* result = nullptr;
  switch (objtype) {
    case VObjectType::slIntConst: {
      // Do not evaluate the constant, keep it as in the source text:
      UHDM::constant* c = s.MakeConstant();
      const std::string& value = fC->SymName(child);
      std::string v;
      c->VpiDecompile(value);
      if (strstr(value.c_str(), "'")) {
        char base = 'b';
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
            v = "DEC:" + v;
            c->VpiConstType(vpiDecConst);
            break;
          }
          default: {
            v = "BIN:" + v;
            c->VpiConstType(vpiBinaryConst);
            break;
          }
        }

      } else {
        if (value.size() && value[0] == '-') {
          v = "INT:" + value;
          c->VpiConstType(vpiIntConst);
        } else {
          v = "UINT:" + value;
          c->VpiConstType(vpiUIntConst);
        }
        c->VpiSize(64);
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
      c->VpiSize(64);
      result = c;
      break;
    }
    case VObjectType::slNumber_1Tickb1:
    case VObjectType::slNumber_1TickB1:
    case VObjectType::slInitVal_1Tickb1:
    case VObjectType::slInitVal_1TickB1:
    case VObjectType::slScalar_1Tickb1:
    case VObjectType::slScalar_1TickB1:
    case VObjectType::sl1: {
      UHDM::constant* c = s.MakeConstant();
      std::string value = "BIN:1";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(1);
      c->VpiDecompile("1'b1");
      result = c;
      break;
    }
    case VObjectType::slScalar_Tickb1:
    case VObjectType::slScalar_TickB1:
    case VObjectType::slNumber_Tickb1:
    case VObjectType::slNumber_TickB1: {
      UHDM::constant* c = s.MakeConstant();
      std::string value = "BIN:1";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(0);
      c->VpiDecompile("'b1");
      result = c;
      break;
    }
    case VObjectType::slNumber_Tick1: {
      UHDM::constant* c = s.MakeConstant();
      std::string value = "BIN:1";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(-1);
      c->VpiDecompile("'1");
      result = c;
      break;
    }
    case VObjectType::slNumber_1Tickb0:
    case VObjectType::slNumber_1TickB0:
    case VObjectType::slInitVal_1Tickb0:
    case VObjectType::slInitVal_1TickB0:
    case VObjectType::slScalar_1Tickb0:
    case VObjectType::slScalar_1TickB0:
    case VObjectType::sl0: {
      UHDM::constant* c = s.MakeConstant();
      std::string value = "BIN:0";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(1);
      c->VpiDecompile("1'b0");
      result = c;
      break;
    }
    case VObjectType::slScalar_Tickb0:
    case VObjectType::slScalar_TickB0:
    case VObjectType::slNumber_Tickb0:
    case VObjectType::slNumber_TickB0: {
      UHDM::constant* c = s.MakeConstant();
      std::string value = "BIN:0";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(0);
      c->VpiDecompile("'b0");
      result = c;
      break;
    }
    case VObjectType::slNumber_Tick0: {
      UHDM::constant* c = s.MakeConstant();
      std::string value = "BIN:0";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(-1);
      c->VpiDecompile("'0");
      result = c;
      break;
    }
    case VObjectType::slZ: {
      UHDM::constant* c = s.MakeConstant();
      std::string value = "BIN:Z";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(-1);
      c->VpiDecompile("'Z");
      result = c;
      break;
    }
    case VObjectType::slX: {
      UHDM::constant* c = s.MakeConstant();
      std::string value = "BIN:X";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(-1);
      c->VpiDecompile("'X");
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
    case VObjectType::slInitVal_1TickBX: {
      UHDM::constant* c = s.MakeConstant();
      std::string value = "BIN:X";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(1);
      c->VpiDecompile("1'bX");
      result = c;
      break;
    }
    case VObjectType::slTime_literal: {
      NodeId intC = fC->Child(child);
      std::string value = fC->SymName(intC);
      NodeId unitId = fC->Sibling(intC);
      TimeInfo::Unit unit = TimeInfo::unitFromString(fC->SymName(unitId));
      uint64_t val = std::strtoull(value.c_str(), 0, 10);
      switch (unit) {
        case TimeInfo::Unit::Second: {
          val = 1e12 * val;
          break;
        }
        case TimeInfo::Unit::Millisecond: {
          val = 1e9 * val;
          break;
        }
        case TimeInfo::Unit::Nanosecond: {
          val = 1e6 * val;
          break;
        }
        case TimeInfo::Unit::Microsecond: {
          val = 1e3 * val;
          break;
        }
        case TimeInfo::Unit::Picosecond: {
          val = 1 * val;
          break;
        }
        case TimeInfo::Unit::Femtosecond: {
          val = 1e-3 * val;
          break;
        }
        default:
          break;
      }
      UHDM::constant* c = s.MakeConstant();
      c->VpiValue("UINT:" + std::to_string(val));
      c->VpiConstType(vpiUIntConst);
      c->VpiSize(64);
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
    default:
      break;
  }
  return result;
}

any* CompileHelper::decodeHierPath(hier_path* path, bool& invalidValue,
                                   DesignComponent* component,
                                   CompileDesign* compileDesign,
                                   ValuedComponentI* instance,
                                   const std::string& fileName, int lineNumber,
                                   any* pexpr, bool muteErrors,
                                   bool returnTypespec) {
  std::string baseObject;
  if (path->Path_elems()->size()) {
    any* firstElem = path->Path_elems()->at(0);
    baseObject = firstElem->VpiName();
  }
  any* object =
      getObject(baseObject, component, compileDesign, instance, pexpr);
  if (object == nullptr) {
    object = getValue(baseObject, component, compileDesign, instance, fileName,
                      lineNumber, pexpr, true, muteErrors);
  }
  if (object) {
    // Substitution
    if (param_assign* pass = any_cast<param_assign*>(object)) {
      const any* rhs = pass->Rhs();
      object = reduceExpr((any*)rhs, invalidValue, component, compileDesign,
                          instance, fileName, lineNumber, pexpr, muteErrors);
    } else if (bit_select* bts = any_cast<bit_select*>(object)) {
      object = reduceExpr((any*)bts, invalidValue, component, compileDesign,
                          instance, fileName, lineNumber, pexpr, muteErrors);
    }

    std::vector<std::string> the_path;
    for (auto elem : *path->Path_elems()) {
      std::string elemName = elem->VpiName();
      elemName = StringUtils::rtrim(elemName, '[');
      the_path.push_back(elemName);
      if (elem->UhdmType() == uhdmbit_select) {
        bit_select* select = (bit_select*)elem;
        uint64_t baseIndex = get_value(
            invalidValue, reduceExpr((any*)select->VpiIndex(), invalidValue,
                                     component, compileDesign, instance,
                                     fileName, lineNumber, pexpr, muteErrors));
        the_path.push_back("[" + std::to_string(baseIndex) + "]");
      }
    }

    expr* res = (expr*)hierarchicalSelector(
        the_path, 0, object, invalidValue, component, compileDesign, instance,
        pexpr, fileName, lineNumber, muteErrors, returnTypespec);
    return res;
  }
  return nullptr;
}

expr* CompileHelper::reduceCompOp(operation* op, bool& invalidValue,
                                  DesignComponent* component,
                                  CompileDesign* compileDesign,
                                  ValuedComponentI* instance,
                                  const std::string& fileName, int lineNumber,
                                  any* pexpr, bool muteErrors) {
  expr* result = op;
  Serializer& s = compileDesign->getSerializer();
  UHDM::VectorOfany& operands = *op->Operands();
  int optype = op->VpiOpType();
  std::string s0;
  std::string s1;
  expr* reduc0 = reduceExpr(operands[0], invalidValue, component, compileDesign,
                            instance, fileName, lineNumber, pexpr, muteErrors);
  expr* reduc1 = reduceExpr(operands[1], invalidValue, component, compileDesign,
                            instance, fileName, lineNumber, pexpr, muteErrors);
  bool arg0isString = getStringVal(s0, reduc0);
  bool arg1isString = getStringVal(s1, reduc1);
  bool invalidValueI = false;
  bool invalidValueD = false;
  bool invalidValueS = true;
  uint64_t val = 0;
  if (arg0isString && arg1isString) {
    invalidValueS = false;
    switch (optype) {
      case vpiEqOp:
        val = (s0 == s1);
        break;
      case vpiNeqOp:
        val = (s0 != s1);
        break;
      default:
        break;
    }
  } else {
    int64_t v0 = get_value(invalidValueI, reduc0);
    int64_t v1 = get_value(invalidValueI, reduc1);
    if ((invalidValue == false) && (invalidValueI == false)) {
      switch (optype) {
        case vpiEqOp:
          val = (v0 == v1);
          break;
        case vpiNeqOp:
          val = (v0 != v1);
          break;
        case vpiGtOp:
          val = (v0 > v1);
          break;
        case vpiGeOp:
          val = (v0 >= v1);
          break;
        case vpiLtOp:
          val = (v0 < v1);
          break;
        case vpiLeOp:
          val = (v0 <= v1);
          break;
        default:
          break;
      }
    } else {
      invalidValueD = false;
      long double v0 = get_double(invalidValueD, reduc0);
      long double v1 = get_double(invalidValueD, reduc1);
      if ((invalidValue == false) && (invalidValueD == false)) {
        switch (optype) {
          case vpiEqOp:
            val = (v0 == v1);
            break;
          case vpiNeqOp:
            val = (v0 != v1);
            break;
          case vpiGtOp:
            val = (v0 > v1);
            break;
          case vpiGeOp:
            val = (v0 >= v1);
            break;
          case vpiLtOp:
            val = (v0 < v1);
            break;
          case vpiLeOp:
            val = (v0 <= v1);
            break;
          default:
            break;
        }
      }
    }
  }
  if (invalidValueI && invalidValueD && invalidValueS) {
    invalidValue = true;
  } else {
    UHDM::constant* c = s.MakeConstant();
    c->VpiValue("UINT:" + std::to_string(val));
    c->VpiDecompile(std::to_string(val));
    c->VpiSize(64);
    c->VpiConstType(vpiUIntConst);
    result = c;
  }
  return result;
}

expr* CompileHelper::reduceExpr(any* result, bool& invalidValue,
                                DesignComponent* component,
                                CompileDesign* compileDesign,
                                ValuedComponentI* instance,
                                const std::string& fileName, int lineNumber,
                                any* pexpr, bool muteErrors) {
  Serializer& s = compileDesign->getSerializer();
  UHDM_OBJECT_TYPE objtype = result->UhdmType();
  if (objtype == uhdmoperation) {
    UHDM::operation* op = (UHDM::operation*)result;
    UHDM::VectorOfany* operands = op->Operands();
    bool constantOperands = true;
    if (operands) {
      for (auto oper : *operands) {
        UHDM_OBJECT_TYPE optype = oper->UhdmType();
        if (optype == uhdmref_obj) {
          ref_obj* ref = (ref_obj*)oper;
          const std::string& name = ref->VpiName();
          any* tmp = getValue(name, component, compileDesign, instance,
                              fileName, lineNumber, pexpr, true, muteErrors);
          if (!tmp) {
            constantOperands = false;
            break;
          }
        } else if (optype == uhdmoperation) {
        } else if (optype == uhdmsys_func_call) {
        } else if (optype == uhdmfunc_call) {
        } else if (optype == uhdmbit_select) {
        } else if (optype == uhdmhier_path) {
        } else if (optype == uhdmvar_select) {
        } else if (optype == uhdmenum_var) {
        } else if (optype != uhdmconstant) {
          constantOperands = false;
          break;
        }
      }
      if (constantOperands) {
        UHDM::VectorOfany& operands = *op->Operands();
        int optype = op->VpiOpType();
        switch (optype) {
          case vpiArithRShiftOp:
          case vpiRShiftOp: {
            if (operands.size() == 2) {
              int64_t val0 = get_value(
                  invalidValue, reduceExpr(operands[0], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              int64_t val1 = get_value(
                  invalidValue, reduceExpr(operands[1], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              uint64_t val = ((uint64_t)val0) >> ((uint64_t)val1);
              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(val));
              c->VpiDecompile(std::to_string(val));
              c->VpiSize(64);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiLeOp:
          case vpiLtOp:
          case vpiGeOp:
          case vpiGtOp:
          case vpiNeqOp:
          case vpiEqOp: {
            if (operands.size() == 2) {
              result = reduceCompOp(op, invalidValue, component, compileDesign,
                                    instance, fileName, lineNumber, pexpr,
                                    muteErrors);
            }
            break;
          }
          case vpiPostIncOp:
          case vpiPostDecOp:
          case vpiPreDecOp:
          case vpiPreIncOp: {
            if (operands.size() == 1) {
              expr* reduc0 = reduceExpr(operands[0], invalidValue, component,
                                        compileDesign, instance, fileName,
                                        lineNumber, pexpr, muteErrors);
              bool invalidValueI = false;
              bool invalidValueD = false;
              int64_t val = get_value(invalidValueI, reduc0);
              if ((invalidValue == false) && (invalidValueI == false)) {
                if (op->VpiOpType() == vpiPostIncOp ||
                    op->VpiOpType() == vpiPreIncOp) {
                  val++;
                } else {
                  val--;
                }
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                c->VpiSize(64);
                c->VpiConstType(vpiIntConst);
                result = c;
                Value* argval = m_exprBuilder.getValueFactory().newLValue();
                argval->set(val, Value::Type::Integer, 64);
                instance->setValue(operands[0]->VpiName(), argval,
                                   m_exprBuilder);
              } else {
                invalidValueD = false;
                long double val = get_double(invalidValueD, reduc0);
                if ((invalidValue == false) && (invalidValueD == false)) {
                  if (op->VpiOpType() == vpiPostIncOp ||
                      op->VpiOpType() == vpiPreIncOp) {
                    val++;
                  } else {
                    val--;
                  }
                  UHDM::constant* c = s.MakeConstant();
                  c->VpiValue("REAL:" + std::to_string(val));
                  c->VpiDecompile(std::to_string(val));
                  c->VpiSize(64);
                  c->VpiConstType(vpiRealConst);
                  result = c;
                  Value* argval = m_exprBuilder.getValueFactory().newLValue();
                  argval->set((double)val);
                  instance->setValue(operands[0]->VpiName(), argval,
                                     m_exprBuilder);
                }
              }
            }
            break;
          }
          case vpiArithLShiftOp:
          case vpiLShiftOp: {
            if (operands.size() == 2) {
              int64_t val0 = get_value(
                  invalidValue, reduceExpr(operands[0], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              int64_t val1 = get_value(
                  invalidValue, reduceExpr(operands[1], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              uint64_t val = ((uint64_t)val0) << ((uint64_t)val1);
              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(val));
              c->VpiDecompile(std::to_string(val));
              c->VpiSize(64);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiAddOp:
          case vpiPlusOp: {
            if (operands.size() == 2) {
              expr* expr0 = reduceExpr(operands[0], invalidValue, component,
                                       compileDesign, instance, fileName,
                                       lineNumber, pexpr, muteErrors);
              expr* expr1 = reduceExpr(operands[1], invalidValue, component,
                                       compileDesign, instance, fileName,
                                       lineNumber, pexpr, muteErrors);
              bool invalidValueI = false;
              bool invalidValueD = false;
              int64_t val0 = get_value(invalidValueI, expr0);
              int64_t val1 = get_value(invalidValueI, expr1);
              if ((invalidValue == false) && (invalidValueI == false)) {
                int64_t val = val0 + val1;
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                c->VpiSize(64);
                c->VpiConstType(vpiIntConst);
                result = c;
              } else {
                invalidValueD = false;
                long double val0 = get_double(invalidValueD, expr0);
                long double val1 = get_double(invalidValueD, expr1);
                if ((invalidValue == false) && (invalidValueD == false)) {
                  long double val = val0 + val1;
                  UHDM::constant* c = s.MakeConstant();
                  c->VpiValue("REAL:" + std::to_string(val));
                  c->VpiDecompile(std::to_string(val));
                  c->VpiSize(64);
                  c->VpiConstType(vpiRealConst);
                  result = c;
                }
              }
              if (invalidValueI && invalidValueD) invalidValue = true;
            }
            break;
          }
          case vpiBitOrOp: {
            if (operands.size() == 2) {
              int64_t val0 = get_value(
                  invalidValue, reduceExpr(operands[0], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              int64_t val1 = get_value(
                  invalidValue, reduceExpr(operands[1], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              uint64_t val = ((uint64_t)val0) | ((uint64_t)val1);
              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(val));
              c->VpiDecompile(std::to_string(val));
              c->VpiSize(64);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiBitAndOp: {
            if (operands.size() == 2) {
              int64_t val0 = get_value(
                  invalidValue, reduceExpr(operands[0], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              int64_t val1 = get_value(
                  invalidValue, reduceExpr(operands[1], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              uint64_t val = ((uint64_t)val0) & ((uint64_t)val1);
              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(val));
              c->VpiDecompile(std::to_string(val));
              c->VpiSize(64);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiLogOrOp: {
            if (operands.size() == 2) {
              int64_t val0 = get_value(
                  invalidValue, reduceExpr(operands[0], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              int64_t val1 = get_value(
                  invalidValue, reduceExpr(operands[1], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              uint64_t val = ((uint64_t)val0) || ((uint64_t)val1);
              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(val));
              c->VpiDecompile(std::to_string(val));
              c->VpiSize(64);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiLogAndOp: {
            if (operands.size() == 2) {
              int64_t val0 = get_value(
                  invalidValue, reduceExpr(operands[0], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              int64_t val1 = get_value(
                  invalidValue, reduceExpr(operands[1], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              uint64_t val = ((uint64_t)val0) && ((uint64_t)val1);
              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(val));
              c->VpiDecompile(std::to_string(val));
              c->VpiSize(64);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiMinusOp: {
            if (operands.size() == 1) {
              bool invalidValueI = false;
              bool invalidValueD = false;
              expr* expr0 = reduceExpr(operands[0], invalidValue, component,
                                       compileDesign, instance, fileName,
                                       lineNumber, pexpr, muteErrors);
              int64_t val0 = get_value(invalidValueI, expr0);
              if ((invalidValue == false) && (invalidValueI == false)) {
                int64_t val = -val0;
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                c->VpiSize(64);
                c->VpiConstType(vpiIntConst);
                result = c;
              } else {
                invalidValueD = false;
                long double val0 = get_double(invalidValueD, expr0);
                if ((invalidValue == false) && (invalidValueD == false)) {
                  long double val = -val0;
                  UHDM::constant* c = s.MakeConstant();
                  c->VpiValue("REAL:" + std::to_string(val));
                  c->VpiDecompile(std::to_string(val));
                  c->VpiSize(64);
                  c->VpiConstType(vpiRealConst);
                  result = c;
                }
              }
              if (invalidValueI && invalidValueD) invalidValue = true;
            }
            break;
          }
          case vpiSubOp: {
            if (operands.size() == 2) {
              expr* expr0 = reduceExpr(operands[0], invalidValue, component,
                                       compileDesign, instance, fileName,
                                       lineNumber, pexpr, muteErrors);
              expr* expr1 = reduceExpr(operands[1], invalidValue, component,
                                       compileDesign, instance, fileName,
                                       lineNumber, pexpr, muteErrors);
              bool invalidValueI = false;
              bool invalidValueD = false;
              int64_t val0 = get_value(invalidValueI, expr0);
              int64_t val1 = get_value(invalidValueI, expr1);
              if ((invalidValue == false) && (invalidValueI == false)) {
                int64_t val = val0 - val1;
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                c->VpiSize(64);
                c->VpiConstType(vpiIntConst);
                result = c;
              } else {
                invalidValueD = false;
                long double val0 = get_double(invalidValueD, expr0);
                long double val1 = get_double(invalidValueD, expr1);
                if ((invalidValue == false) && (invalidValueD == false)) {
                  long double val = val0 - val1;
                  UHDM::constant* c = s.MakeConstant();
                  c->VpiValue("REAL:" + std::to_string(val));
                  c->VpiDecompile(std::to_string(val));
                  c->VpiSize(64);
                  c->VpiConstType(vpiRealConst);
                  result = c;
                }
              }
              if (invalidValueI && invalidValueD) invalidValue = true;
            }
            break;
          }
          case vpiMultOp: {
            if (operands.size() == 2) {
              expr* expr0 = reduceExpr(operands[0], invalidValue, component,
                                       compileDesign, instance, fileName,
                                       lineNumber, pexpr, muteErrors);
              expr* expr1 = reduceExpr(operands[1], invalidValue, component,
                                       compileDesign, instance, fileName,
                                       lineNumber, pexpr, muteErrors);
              bool invalidValueI = false;
              bool invalidValueD = false;
              int64_t val0 = get_value(invalidValueI, expr0);
              int64_t val1 = get_value(invalidValueI, expr1);
              if ((invalidValue == false) && (invalidValueI == false)) {
                int64_t val = val0 * val1;
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                c->VpiSize(64);
                c->VpiConstType(vpiIntConst);
                result = c;
              } else {
                invalidValueD = false;
                long double val0 = get_double(invalidValueD, expr0);
                long double val1 = get_double(invalidValueD, expr1);
                if ((invalidValue == false) && (invalidValueD == false)) {
                  long double val = val0 * val1;
                  UHDM::constant* c = s.MakeConstant();
                  c->VpiValue("REAL:" + std::to_string(val));
                  c->VpiDecompile(std::to_string(val));
                  c->VpiSize(64);
                  c->VpiConstType(vpiRealConst);
                  result = c;
                }
              }
              if (invalidValueI && invalidValueD) invalidValue = true;
            }
            break;
          }
          case vpiBitNegOp: {
            if (operands.size() == 1) {
              expr* operand = reduceExpr(operands[0], invalidValue, component,
                                         compileDesign, instance, fileName,
                                         lineNumber, pexpr, muteErrors);
              uint64_t val = (uint64_t)get_value(invalidValue, operand);
              int size = 64;
              if (operand->UhdmType() == uhdmconstant) {
                constant* c = (constant*)operand;
                size = c->VpiSize();
                if (size == 1) {
                  val = !val;
                } else {
                  val = ~val;
                }
              } else {
                val = ~val;
              }

              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(val));
              c->VpiDecompile(std::to_string(val));
              c->VpiSize(size);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiNotOp: {
            if (operands.size() == 1) {
              uint64_t val = !((uint64_t)get_value(
                  invalidValue, reduceExpr(operands[0], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors)));
              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(val));
              c->VpiDecompile(std::to_string(val));
              c->VpiSize(64);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiUnaryAndOp: {
            if (operands.size() == 1) {
              constant* cst = (constant*)(reduceExpr(
                  operands[0], invalidValue, component, compileDesign, instance,
                  fileName, lineNumber, pexpr, muteErrors));
              uint64_t val = get_value(invalidValue, cst);
              uint64_t res = val & 1;
              for (int i = 1; i < cst->VpiSize(); i++) {
                res = res & ((val & (1 << i)) >> i);
              }
              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(res));
              c->VpiDecompile(std::to_string(res));
              c->VpiSize(64);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiUnaryNandOp: {
            if (operands.size() == 1) {
              uint64_t val = get_value(
                  invalidValue, reduceExpr(operands[0], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              uint64_t res = val & 1;
              for (unsigned int i = 1; i < 32; i++) {
                res = res & ((val & (1 << i)) >> i);
              }
              res = !res;
              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(res));
              c->VpiDecompile(std::to_string(res));
              c->VpiSize(64);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiUnaryOrOp: {
            if (operands.size() == 1) {
              uint64_t val = get_value(
                  invalidValue, reduceExpr(operands[0], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              uint64_t res = val & 1;
              for (unsigned int i = 1; i < 32; i++) {
                res = res | ((val & (1 << i)) >> i);
              }
              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(res));
              c->VpiDecompile(std::to_string(res));
              c->VpiSize(64);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiUnaryNorOp: {
            if (operands.size() == 1) {
              uint64_t val = get_value(
                  invalidValue, reduceExpr(operands[0], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              uint64_t res = val & 1;
              for (unsigned int i = 1; i < 64; i++) {
                res = res | ((val & (1 << i)) >> i);
              }
              res = !res;
              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(res));
              c->VpiDecompile(std::to_string(res));
              c->VpiSize(64);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiUnaryXorOp: {
            if (operands.size() == 1) {
              uint64_t val = get_value(
                  invalidValue, reduceExpr(operands[0], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              uint64_t res = val & 1;
              for (unsigned int i = 1; i < 64; i++) {
                res = res ^ ((val & (1 << i)) >> i);
              }
              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(res));
              c->VpiDecompile(std::to_string(res));
              c->VpiSize(64);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiUnaryXNorOp: {
            if (operands.size() == 1) {
              uint64_t val = get_value(
                  invalidValue, reduceExpr(operands[0], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              uint64_t res = val & 1;
              for (unsigned int i = 1; i < 64; i++) {
                res = res ^ ((val & (1 << i)) >> i);
              }
              res = !res;
              UHDM::constant* c = s.MakeConstant();
              c->VpiValue("UINT:" + std::to_string(res));
              c->VpiDecompile(std::to_string(res));
              c->VpiSize(64);
              c->VpiConstType(vpiUIntConst);
              result = c;
            }
            break;
          }
          case vpiModOp: {
            if (operands.size() == 2) {
              expr* expr0 = reduceExpr(operands[0], invalidValue, component,
                                       compileDesign, instance, fileName,
                                       lineNumber, pexpr, muteErrors);
              expr* expr1 = reduceExpr(operands[1], invalidValue, component,
                                       compileDesign, instance, fileName,
                                       lineNumber, pexpr, muteErrors);
              bool invalidValueI = false;
              bool invalidValueD = false;
              int64_t val0 = get_value(invalidValueI, expr0);
              int64_t val1 = get_value(invalidValueI, expr1);
              int64_t val = 0;
              if (val1 && (invalidValue == false) && (invalidValueI == false)) {
                val = val0 % val1;
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                c->VpiSize(64);
                c->VpiConstType(vpiIntConst);
                result = c;
              } else {
                invalidValueD = false;
                long double val0 = get_double(invalidValueD, expr0);
                long double val1 = get_double(invalidValueD, expr1);
                if (val1 && (invalidValue == false) &&
                    (invalidValueD == false)) {
                  long double val = 0;
                  val = std::fmod(val0, val1);
                  UHDM::constant* c = s.MakeConstant();
                  c->VpiValue("REAL:" + std::to_string(val));
                  c->VpiDecompile(std::to_string(val));
                  c->VpiSize(64);
                  c->VpiConstType(vpiRealConst);
                  result = c;
                }
                if ((val1 == 0) && (invalidValue == false) &&
                    (invalidValueD == false)) {
                  // Divide by 0
                  if (!muteErrors) {
                    std::string instanceName;
                    if (instance) {
                      if (ModuleInstance* inst =
                              valuedcomponenti_cast<ModuleInstance*>(instance)) {
                        instanceName = inst->getFullPathName();
                      }
                    } else if (component) {
                      instanceName = component->getName();
                    }
                    ErrorContainer* errors =
                        compileDesign->getCompiler()->getErrorContainer();
                    SymbolTable* symbols =
                        compileDesign->getCompiler()->getSymbolTable();
                    Location loc(symbols->registerSymbol(fileName), lineNumber,
                                 0, symbols->registerSymbol(instanceName));
                    Error err(ErrorDefinition::ELAB_DIVIDE_BY_ZERO, loc);
                    errors->addError(err);
                  }
                  bool replay = false;
                  // GDB: p replay=true
                  if (replay) {
                    expr* tmp = reduceExpr(operands[1], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors);
                    get_double(invalidValue, tmp);
                  }
                }
              }
              if (invalidValueI && invalidValueD) invalidValue = true;
            }
            break;
          }
          case vpiPowerOp: {
            if (operands.size() == 2) {
              expr* expr0 = reduceExpr(operands[0], invalidValue, component,
                                       compileDesign, instance, fileName,
                                       lineNumber, pexpr, muteErrors);
              expr* expr1 = reduceExpr(operands[1], invalidValue, component,
                                       compileDesign, instance, fileName,
                                       lineNumber, pexpr, muteErrors);
              bool invalidValueI = false;
              bool invalidValueD = false;
              int64_t val0 = get_value(invalidValueI, expr0);
              int64_t val1 = get_value(invalidValueI, expr1);
              int64_t val = 0;
              if ((invalidValue == false) && (invalidValueI == false)) {
                val = pow(val0, val1);
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                c->VpiSize(64);
                c->VpiConstType(vpiIntConst);
                result = c;
              } else {
                invalidValueD = false;
                long double val0 = get_double(invalidValueD, expr0);
                long double val1 = get_double(invalidValueD, expr1);
                if ((invalidValue == false) && (invalidValueD == false)) {
                  long double val = 0;
                  val = pow(val0, val1);
                  UHDM::constant* c = s.MakeConstant();
                  c->VpiValue("REAL:" + std::to_string(val));
                  c->VpiDecompile(std::to_string(val));
                  c->VpiSize(64);
                  c->VpiConstType(vpiRealConst);
                  result = c;
                }
              }
              if (invalidValueI && invalidValueD) invalidValue = true;
            }
            break;
          }
          case vpiDivOp: {
            if (operands.size() == 2) {
              bool divideByZero = true;
              expr* div_expr = reduceExpr(operands[1], invalidValue, component,
                                          compileDesign, instance, fileName,
                                          lineNumber, pexpr, muteErrors);
              expr* num_expr = reduceExpr(operands[0], invalidValue, component,
                                          compileDesign, instance, fileName,
                                          lineNumber, pexpr, muteErrors);
              bool invalidValueI = false;
              bool invalidValueD = false;
              int64_t divisor = get_value(invalidValueI, div_expr);
              int64_t num = get_value(invalidValueI, num_expr);
              if (divisor && (invalidValue == false) &&
                  (invalidValueI == false)) {
                divideByZero = false;
                int64_t val = num / divisor;
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("INT:" + std::to_string(val));
                c->VpiDecompile(std::to_string(val));
                c->VpiSize(64);
                c->VpiConstType(vpiIntConst);
                result = c;
              } else {
                invalidValueD = false;
                long double divisor = get_double(invalidValueD, div_expr);
                long double num = get_double(invalidValueD, num_expr);
                if (divisor && (invalidValue == false) &&
                    (invalidValueD == false)) {
                  divideByZero = false;
                  long double val = num / divisor;
                  UHDM::constant* c = s.MakeConstant();
                  c->VpiValue("REAL:" + std::to_string(val));
                  c->VpiDecompile(std::to_string(val));
                  c->VpiSize(64);
                  c->VpiConstType(vpiRealConst);
                  result = c;
                }
              }
              if (invalidValueI && invalidValueD) invalidValue = true;
              if (divideByZero) {
                // Divide by 0
                if (!muteErrors) {
                  std::string instanceName;
                  if (instance) {
                    if (ModuleInstance* inst =
                            valuedcomponenti_cast<ModuleInstance*>(instance)) {
                      instanceName = inst->getFullPathName();
                    }
                  } else if (component) {
                    instanceName = component->getName();
                  }
                  ErrorContainer* errors =
                      compileDesign->getCompiler()->getErrorContainer();
                  SymbolTable* symbols =
                      compileDesign->getCompiler()->getSymbolTable();
                  Location loc(symbols->registerSymbol(fileName), lineNumber, 0,
                               symbols->registerSymbol(instanceName));
                  Error err(ErrorDefinition::ELAB_DIVIDE_BY_ZERO, loc);
                  errors->addError(err);
                }
                bool replay = false;
                // GDB: p replay=true
                if (replay) {
                  expr* tmp = reduceExpr(operands[1], invalidValue, component,
                                         compileDesign, instance, fileName,
                                         lineNumber, pexpr, muteErrors);
                  get_value(invalidValue, tmp);
                }
              }
            }
            break;
          }
          case vpiConditionOp: {
            if (operands.size() == 3) {
              bool localInvalidValue = false;
              expr* cond = reduceExpr(operands[0], invalidValue, component,
                                      compileDesign, instance, fileName,
                                      lineNumber, pexpr, muteErrors);
              int64_t condVal = get_value(invalidValue, cond);
              int64_t val = 0;
              expr* the_val = nullptr;
              if (condVal) {
                the_val = reduceExpr(operands[1], localInvalidValue, component,
                                     compileDesign, instance, fileName,
                                     lineNumber, pexpr, muteErrors);
              } else {
                the_val = reduceExpr(operands[2], localInvalidValue, component,
                                     compileDesign, instance, fileName,
                                     lineNumber, pexpr, muteErrors);
              }
              if (localInvalidValue == false) {
                val = get_value(localInvalidValue, the_val);
                if (localInvalidValue == false) {
                  UHDM::constant* c = s.MakeConstant();
                  c->VpiValue("INT:" + std::to_string(val));
                  c->VpiDecompile(std::to_string(val));
                  c->VpiSize(64);
                  c->VpiConstType(vpiIntConst);
                  result = c;
                } else {
                  result = the_val;
                }
              } else {
                result = the_val;
              }
            }
            break;
          }
          case vpiMultiConcatOp: {
            if (operands.size() == 2) {
              int64_t n = get_value(
                  invalidValue, reduceExpr(operands[0], invalidValue, component,
                                           compileDesign, instance, fileName,
                                           lineNumber, pexpr, muteErrors));
              if (n > 1000) n = 1000;  // Must be -1 or something silly
              if (n < 0) n = 0;
              constant* cv = (constant*)(operands[1]);
              UHDM::constant* c = s.MakeConstant();
              unsigned int width = cv->VpiSize();
              int consttype = cv->VpiConstType();
              c->VpiConstType(consttype);
              if (consttype == vpiBinaryConst) {
                std::string val = cv->VpiValue();
                std::string res;
                for (unsigned int i = 0; i < n; i++) {
                  res += val.c_str() + strlen("BIN:");
                }
                c->VpiValue("BIN:" + res);
                c->VpiDecompile(res);
              } else if (consttype == vpiHexConst) {
                std::string val = cv->VpiValue();
                std::string res;
                for (unsigned int i = 0; i < n; i++) {
                  res += val.c_str() + strlen("HEX:");
                }
                c->VpiValue("HEX:" + res);
                c->VpiDecompile(res);
              } else if (consttype == vpiOctConst) {
                std::string val = cv->VpiValue();
                std::string res;
                for (unsigned int i = 0; i < n; i++) {
                  res += val.c_str() + strlen("OCT:");
                }
                c->VpiValue("OCT:" + res);
                c->VpiDecompile(res);
              } else if (consttype == vpiStringConst) {
                std::string val = cv->VpiValue();
                std::string res;
                for (unsigned int i = 0; i < n; i++) {
                  res += val.c_str() + strlen("STRING:");
                }
                c->VpiValue("STRING:" + res);
                c->VpiDecompile(res);
              } else {
                uint64_t val = get_value(
                    invalidValue,
                    reduceExpr(cv, invalidValue, component, compileDesign,
                               instance, fileName, lineNumber, pexpr));
                uint64_t res = 0;
                for (unsigned int i = 0; i < n; i++) {
                  res |= val << (i * width);
                }
                c->VpiValue("UINT:" + std::to_string(res));
                c->VpiDecompile(std::to_string(res));
                c->VpiConstType(vpiUIntConst);
              }
              c->VpiSize(n * width);
              result = c;
            }
            break;
          }
          case vpiConcatOp: {
            UHDM::constant* c = s.MakeConstant();
            std::string cval;
            int csize = 0;
            for (unsigned int i = 0; i < operands.size(); i++) {
              if (operands[i]->UhdmType() == uhdmconstant) {
                constant* c = (constant*)operands[i];
                std::string v = c->VpiValue();
                unsigned int size = c->VpiSize();
                csize += size;
                int type = c->VpiConstType();
                switch (type) {
                  case vpiBinaryConst: {
                    cval += v.c_str() + strlen("BIN:");
                    break;
                  }
                  case vpiDecConst: {
                    long long iv =
                        std::strtoll(v.c_str() + strlen("DEC:"), 0, 10);
                    cval += NumUtils::toBinary(size, iv);
                    break;
                  }
                  case vpiHexConst: {
                    cval += NumUtils::hexToBin(v.c_str() + strlen("HEX:"));
                    break;
                  }
                  case vpiOctConst: {
                    long long iv =
                        std::strtoll(v.c_str() + strlen("OCT:"), 0, 8);
                    cval += NumUtils::toBinary(size, iv);
                    break;
                  }
                  case vpiIntConst: {
                    int64_t iv =
                        std::strtoll(v.c_str() + strlen("INT:"), 0, 10);
                    cval += NumUtils::toBinary(size, iv);
                    break;
                  }
                  case vpiUIntConst: {
                    uint64_t iv =
                        std::strtoull(v.c_str() + strlen("UINT:"), 0, 10);
                    cval += NumUtils::toBinary(size, iv);
                    break;
                  }
                  default: {
                    if (strstr(v.c_str(), "UINT:")) {
                      uint64_t iv =
                          std::strtoull(v.c_str() + strlen("UINT:"), 0, 10);
                      cval += NumUtils::toBinary(size, iv);
                    } else {
                      int64_t iv =
                          std::strtoll(v.c_str() + strlen("INT:"), 0, 10);
                      cval += NumUtils::toBinary(size, iv);
                    }
                    break;
                  }
                }
              } else {
                c = nullptr;
                break;
              }
            }
            if (c) {
              c->VpiValue("BIN:" + cval);
              c->VpiSize(csize);
              c->VpiConstType(vpiBinaryConst);
              result = c;
            }
            break;
          }
          case vpiCastOp: {
            uint64_t val0 = get_value(
                invalidValue,
                reduceExpr(operands[0], invalidValue, component, compileDesign,
                           instance, fileName, lineNumber, pexpr, true));
            const typespec* tps = op->Typespec();
            if (tps) {
              UHDM_OBJECT_TYPE ttps = tps->UhdmType();
              if (ttps == uhdmint_typespec) {
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("UINT:" + std::to_string((int)val0));
                c->VpiSize(64);
                c->VpiConstType(vpiUIntConst);
                result = c;
              } else if (ttps == uhdmlong_int_typespec) {
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("UINT:" + std::to_string((long int)val0));
                c->VpiSize(64);
                c->VpiConstType(vpiUIntConst);
                result = c;
              } else if (ttps == uhdmshort_int_typespec) {
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("UINT:" + std::to_string((short int)val0));
                c->VpiSize(16);
                c->VpiConstType(vpiUIntConst);
                result = c;
              } else if (ttps == uhdminteger_typespec) {
                integer_typespec* itps = (integer_typespec*)tps;
                uint64_t cast_to = 0;
                if (strstr(itps->VpiValue().c_str(), "UINT:")) {
                  cast_to = std::strtoull(
                      itps->VpiValue().c_str() + strlen("UINT:"), 0, 10);
                } else {
                  cast_to = std::strtoll(
                      itps->VpiValue().c_str() + strlen("INT:"), 0, 10);
                }
                UHDM::constant* c = s.MakeConstant();
                uint64_t mask =
                    ((uint64_t)((uint64_t)1 << cast_to)) - ((uint64_t)1);
                uint64_t res = val0 & mask;
                c->VpiValue("UINT:" + std::to_string(res));
                c->VpiSize(cast_to);
                c->VpiConstType(vpiUIntConst);
                result = c;
              } else if (ttps == uhdmenum_typespec) {
                // TODO: Should check the value is in range of the enum and
                // issue error if not
                UHDM::constant* c = s.MakeConstant();
                c->VpiValue("UINT:" + std::to_string(val0));
                c->VpiSize(64);
                c->VpiConstType(vpiUIntConst);
                result = c;
              }
            }
            break;
          }
          case vpiMultiAssignmentPatternOp:
          case vpiAssignmentPatternOp:
            // Don't reduce these ops
            break;
          default: {
            invalidValue = true;
            break;
          }
        }
      }
    }
    return (expr*)result;
  } else if (objtype == uhdmconstant) {
    return (expr*)result;
  } else if (objtype == uhdmsys_func_call) {
    sys_func_call* scall = (sys_func_call*)result;
    const std::string& name = scall->VpiName();
    if ((name == "$bits") || (name == "$size")) {
      uint64_t bits = 0;
      bool found = false;
      for (auto arg : *scall->Tf_call_args()) {
        UHDM::UHDM_OBJECT_TYPE argtype = arg->UhdmType();
        if (argtype == uhdmref_obj) {
          ref_obj* ref = (ref_obj*)arg;
          const std::string& objname = ref->VpiName();
          any* object =
              getObject(objname, component, compileDesign, instance, pexpr);
          const typespec* tps = nullptr;
          if (expr* exp = any_cast<expr*>(object)) {
            tps = exp->Typespec();
          } else if (typespec* tp = any_cast<typespec*>(object)) {
            tps = tp;
          }
          if (tps) {
            bits += Bits(tps, invalidValue, component, compileDesign, instance,
                         fileName, lineNumber, true, (name == "$size"));
            found = true;
          } else {
            bits +=
                Bits(object, invalidValue, component, compileDesign, instance,
                     fileName, lineNumber, true, (name == "$size"));
            found = true;
          }
        } else if (argtype == uhdmoperation) {
          operation* oper = (operation*)arg;
          if (oper->VpiOpType() == vpiConcatOp) {
            for (auto op : *oper->Operands()) {
              bits += Bits(op, invalidValue, component, compileDesign, instance,
                           fileName, lineNumber, true, (name == "$size"));
            }
            found = true;
          }
        } else if (argtype == uhdmhier_path) {
          hier_path* path = (hier_path*)arg;
          auto elems = path->Path_elems();
          if (elems && (elems->size() > 1)) {
            const std::string& base = elems->at(0)->VpiName();
            const std::string& suffix = elems->at(1)->VpiName();
            any* var =
                getObject(base, component, compileDesign, instance, pexpr);
            if (var) {
              UHDM_OBJECT_TYPE vtype = var->UhdmType();
              if (vtype == uhdmport) {
                port* p = (port*)var;
                if (const typespec* tps = p->Typespec()) {
                  UHDM_OBJECT_TYPE ttps = tps->UhdmType();
                  if (ttps == uhdmstruct_typespec) {
                    struct_typespec* tpss = (struct_typespec*)tps;
                    for (typespec_member* memb : *tpss->Members()) {
                      if (memb->VpiName() == suffix) {
                        const typespec* tps = memb->Typespec();
                        if (tps) {
                          bits += Bits(tps, invalidValue, component,
                                       compileDesign, instance, fileName,
                                       lineNumber, true, (name == "$size"));
                          found = true;
                        }
                        break;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      if (found) {
        UHDM::constant* c = s.MakeConstant();
        c->VpiValue("UINT:" + std::to_string(bits));
        c->VpiDecompile(std::to_string(bits));
        c->VpiSize(64);
        c->VpiConstType(vpiUIntConst);
        result = c;
      }
    } else if (name == "$clog2") {
      bool invalidValue = false;
      for (auto arg : *scall->Tf_call_args()) {
        uint64_t clog2 = 0;
        uint64_t val = get_value(
            invalidValue,
            reduceExpr(arg, invalidValue, component, compileDesign, instance,
                       fileName, lineNumber, pexpr, muteErrors));
        if (val) {
          val = val - 1;
          for (; val > 0; clog2 = clog2 + 1) {
            val = val >> 1;
          }
        }
        if (invalidValue == false) {
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue("UINT:" + std::to_string(clog2));
          c->VpiDecompile(std::to_string(clog2));
          c->VpiSize(64);
          c->VpiConstType(vpiUIntConst);
          result = c;
        }
      }
    }
  } else if (objtype == uhdmfunc_call) {
    func_call* scall = (func_call*)result;
    const std::string& name = scall->VpiName();
    std::vector<any*>* args = scall->Tf_call_args();
    auto [func, actual_comp] =
        getTaskFunc(name, component, compileDesign, pexpr);
    function* actual_func = nullptr;
    if (func) {
      actual_func = any_cast<function*>(func);
    }
    if (actual_func == nullptr) {
      ErrorContainer* errors =
          compileDesign->getCompiler()->getErrorContainer();
      SymbolTable* symbols = compileDesign->getCompiler()->getSymbolTable();
      Location loc(symbols->registerSymbol(scall->VpiFile()),
                   scall->VpiLineNo(), scall->VpiColumnNo(),
                   symbols->registerSymbol(name));
      Error err(ErrorDefinition::COMP_UNDEFINED_USER_FUNCTION, loc);
      errors->addError(err);
      invalidValue = true;
    }
    expr* tmp = EvalFunc(actual_func, args, invalidValue,
                         (instance) ? actual_comp : component, compileDesign,
                         instance, fileName, lineNumber, pexpr);
    if (tmp && (invalidValue == false)) {
      result = tmp;
    }
  } else if (objtype == uhdmref_obj) {
    ref_obj* ref = (ref_obj*)result;
    const std::string& name = ref->VpiName();
    any* tmp = getValue(name, component, compileDesign, instance, fileName,
                        lineNumber, pexpr, true, muteErrors);
    if (tmp) {
      result = tmp;
    }
    return (expr*)result;
  } else if (objtype == uhdmhier_path) {
    hier_path* path = (hier_path*)result;
    expr* res = (expr*)decodeHierPath(path, invalidValue, component,
                                      compileDesign, instance, fileName,
                                      lineNumber, pexpr, muteErrors, false);
    return res;
  } else if (objtype == uhdmbit_select) {
    bit_select* sel = (bit_select*)result;
    const std::string& name = sel->VpiName();
    const expr* index = sel->VpiIndex();
    uint64_t index_val = get_value(
        invalidValue,
        reduceExpr((expr*)index, invalidValue, component, compileDesign,
                   instance, fileName, lineNumber, pexpr, muteErrors));
    if (invalidValue == false) {
      if (FScope* scope = valuedcomponenti_cast<FScope*>(instance)) {
        expr* complex = scope->getComplexValue(name);
        if (complex == nullptr) {
          complex =
              (expr*)getObject(name, component, compileDesign, instance, pexpr);
        }
        if (complex == nullptr) {
          complex =
              (expr*)getValue(name, component, compileDesign, instance,
                              fileName, lineNumber, pexpr, true, muteErrors);
        }
        if (complex) {
          UHDM_OBJECT_TYPE ctype = complex->UhdmType();
          if (ctype == uhdmoperation) {
            operation* op = (operation*)complex;
            int opType = op->VpiOpType();
            if (opType == vpiAssignmentPatternOp) {
              UHDM::VectorOfany* ops = op->Operands();
              if (ops && (index_val < ops->size())) {
                result = ops->at(index_val);
              } else {
                invalidValue = true;
              }
            } else if (opType == vpiConcatOp) {
              UHDM::VectorOfany* ops = op->Operands();
              if (ops && (index_val < ops->size())) {
                result = ops->at(index_val);
              } else {
                invalidValue = true;
              }
            }
          } else if (ctype == uhdmconstant) {
            if (index_val == 0) {
              result = complex;
            }
          }
        }
      } else if (ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(instance)) {
        any* object = getObject(name, component, compileDesign, inst, pexpr);
        if (object == nullptr) {
          object = getValue(name, component, compileDesign, inst, fileName,
                            lineNumber, pexpr, true, muteErrors);
        }
        if (object) {
          UHDM_OBJECT_TYPE otype = object->UhdmType();
          if (otype == uhdmpacked_array_var) {
            packed_array_var* array = (packed_array_var*)object;
            VectorOfany* elems = array->Elements();
            if (index_val < elems->size()) {
              result = elems->at(index_val);
            }
          } else if (otype == uhdmoperation) {
            operation* op = (operation*)object;
            int opType = op->VpiOpType();
            if (opType == vpiAssignmentPatternOp) {
              UHDM::VectorOfany* ops = op->Operands();
              if (ops && (index_val < ops->size())) {
                result = ops->at(index_val);
              } else if (ops) {
                bool defaultTaggedPattern = false;
                for (auto op : *ops) {
                  if (op->UhdmType() == uhdmtagged_pattern) {
                    tagged_pattern* tp = (tagged_pattern*)op;
                    const typespec* tps = tp->Typespec();
                    if (tps->VpiName() == "default") {
                      defaultTaggedPattern = true;
                      break;
                    }
                  }
                }
                if (!defaultTaggedPattern) invalidValue = true;
              } else {
                invalidValue = true;
              }
            } else if (opType == vpiConcatOp) {
              UHDM::VectorOfany* ops = op->Operands();
              if (ops && (index_val < ops->size())) {
                result = ops->at(index_val);
              } else {
                invalidValue = true;
              }
            } else if (opType == vpiConditionOp) {
              expr* exp =
                  reduceExpr(op, invalidValue, component, compileDesign,
                             instance, fileName, lineNumber, pexpr, muteErrors);
              UHDM_OBJECT_TYPE otype = exp->UhdmType();
              if (otype == uhdmoperation) {
                operation* op = (operation*)exp;
                int opType = op->VpiOpType();
                if (opType == vpiAssignmentPatternOp) {
                  UHDM::VectorOfany* ops = op->Operands();
                  if (ops && (index_val < ops->size())) {
                    object = ops->at(index_val);
                  } else {
                    invalidValue = true;
                  }
                } else if (opType == vpiConcatOp) {
                  UHDM::VectorOfany* ops = op->Operands();
                  if (ops && (index_val < ops->size())) {
                    object = ops->at(index_val);
                  } else {
                    invalidValue = true;
                  }
                }
              }
              if (object) result = object;
            } else if (opType == vpiMultiConcatOp) {
              result = reduceBitSelect(op, index_val, invalidValue, component,
                                       compileDesign, instance, fileName,
                                       lineNumber, pexpr, muteErrors);
            }
          } else if (otype == uhdmconstant) {
            result = reduceBitSelect((constant*)object, index_val, invalidValue,
                                     component, compileDesign, instance,
                                     fileName, lineNumber, pexpr, muteErrors);
          }
        }
      }
    }
  } else if (objtype == uhdmpart_select) {
    part_select* sel = (part_select*)result;
    ref_obj* parent = (ref_obj*)sel->VpiParent();
    const std::string& name = parent->VpiName();
    any* object = getObject(name, component, compileDesign, instance, pexpr);
    if (object == nullptr) {
      object = getValue(name, component, compileDesign, instance, fileName,
                        lineNumber, pexpr, true, muteErrors);
      if (object && (object->UhdmType() == uhdmconstant)) {
        constant* co = (constant*)object;
        int64_t val = get_value(invalidValue, co);
        std::string binary = NumUtils::toBinary(co->VpiSize(), val);
        int64_t l = get_value(invalidValue, sel->Left_range());
        int64_t r = get_value(invalidValue, sel->Right_range());
        std::reverse(binary.begin(), binary.end());
        std::string sub;
        if (l > r)
          sub = binary.substr(r, l - r + 1);
        else
          sub = binary.substr(l, r - l + 1);
        UHDM::constant* c = s.MakeConstant();
        c->VpiValue("BIN:" + sub);
        c->VpiDecompile(sub);
        c->VpiSize(sub.size());
        c->VpiConstType(vpiBinaryConst);
        result = c;
      }
    }
  } else if (objtype == uhdmvar_select) {
    var_select* sel = (var_select*)result;
    const std::string& name = sel->VpiName();
    any* object = getObject(name, component, compileDesign, instance, pexpr);
    if (object == nullptr) {
      object = getValue(name, component, compileDesign, instance, fileName,
                        lineNumber, pexpr, true, muteErrors);
    }
    for (auto index : *sel->Exprs()) {
      uint64_t index_val = get_value(
          invalidValue,
          reduceExpr((expr*)index, invalidValue, component, compileDesign,
                     instance, fileName, lineNumber, pexpr, muteErrors));
      if (object) {
        UHDM_OBJECT_TYPE otype = object->UhdmType();
        if (otype == uhdmoperation) {
          operation* op = (operation*)object;
          int opType = op->VpiOpType();
          if (opType == vpiAssignmentPatternOp) {
            UHDM::VectorOfany* ops = op->Operands();
            if (ops && (index_val < ops->size())) {
              object = ops->at(index_val);
            } else {
              invalidValue = true;
            }
          } else if (opType == vpiConcatOp) {
            UHDM::VectorOfany* ops = op->Operands();
            if (ops && (index_val < ops->size())) {
              object = ops->at(index_val);
            } else {
              invalidValue = true;
            }
          } else if (opType == vpiConditionOp) {
            expr* exp =
                reduceExpr(object, invalidValue, component, compileDesign,
                           instance, fileName, lineNumber, pexpr, muteErrors);
            UHDM_OBJECT_TYPE otype = exp->UhdmType();
            if (otype == uhdmoperation) {
              operation* op = (operation*)exp;
              int opType = op->VpiOpType();
              if (opType == vpiAssignmentPatternOp) {
                UHDM::VectorOfany* ops = op->Operands();
                if (ops && (index_val < ops->size())) {
                  object = ops->at(index_val);
                } else {
                  invalidValue = true;
                }
              } else if (opType == vpiConcatOp) {
                UHDM::VectorOfany* ops = op->Operands();
                if (ops && (index_val < ops->size())) {
                  object = ops->at(index_val);
                } else {
                  invalidValue = true;
                }
              }
            }
          }
        }
      }
    }
    if (object) result = object;
  }
  if (result && result->UhdmType() == uhdmref_obj) {
    bool invalidValueTmp = false;
    expr* tmp = reduceExpr(result, invalidValueTmp, component, compileDesign,
                           instance, fileName, lineNumber, pexpr, muteErrors);
    if (tmp && !invalidValueTmp) result = tmp;
  }
  return (expr*)result;
}

any* CompileHelper::hierarchicalSelector(
    std::vector<std::string>& select_path, unsigned int level,
    UHDM::any* object, bool& invalidValue, DesignComponent* component,
    CompileDesign* compileDesign, ValuedComponentI* instance, UHDM::any* pexpr,
    const std::string& fileName, int lineNumber, bool muteErrors,
    bool returnTypespec) {
  if (level >= select_path.size()) {
    return (expr*)object;
  }
  std::string elemName = select_path[level];

  if (variables* var = any_cast<variables*>(object)) {
    UHDM_OBJECT_TYPE ttps = var->UhdmType();
    if (ttps == uhdmstruct_var) {
      struct_typespec* stpt = (struct_typespec*)((struct_var*)var)->Typespec();
      for (typespec_member* member : *stpt->Members()) {
        if (member->VpiName() == elemName) {
          if (returnTypespec)
            return (expr*)member->Typespec();
          else
            return (expr*)member->Default_value();
        }
      }
    }
  } else if (io_decl* decl = any_cast<io_decl*>(object)) {
    const any* exp = decl->Expr();
    if (exp) {
      UHDM_OBJECT_TYPE ttps = exp->UhdmType();
      if (ttps == uhdmstruct_var) {
        struct_typespec* stpt =
            (struct_typespec*)((struct_var*)exp)->Typespec();
        for (typespec_member* member : *stpt->Members()) {
          if (member->VpiName() == elemName) {
            if (returnTypespec)
              return (expr*)member->Typespec();
            else
              return (expr*)member->Default_value();
          }
        }
      }
    }
  } else if (nets* var = any_cast<nets*>(object)) {
    UHDM_OBJECT_TYPE ttps = var->UhdmType();
    if (ttps == uhdmstruct_net) {
      struct_typespec* stpt = (struct_typespec*)((struct_net*)var)->Typespec();
      for (typespec_member* member : *stpt->Members()) {
        if (member->VpiName() == elemName) {
          if (returnTypespec)
            return (expr*)member->Typespec();
          else
            return (expr*)member->Default_value();
        }
      }
    }
  }

  int selectIndex = -1;
  if (strstr(elemName.c_str(), "[")) {
    std::string indexName = StringUtils::ltrim(elemName, '[');
    indexName = StringUtils::rtrim(elemName, ']');
    selectIndex = std::strtoull(indexName.c_str(), 0, 10);
    elemName = "";
    if (operation* oper = any_cast<operation*>(object)) {
      int opType = oper->VpiOpType();
      if (opType == vpiAssignmentPatternOp) {
        UHDM::VectorOfany* operands = oper->Operands();
        int sInd = 0;
        for (auto operand : *operands) {
          if ((selectIndex >= 0) && (sInd == selectIndex)) {
            any* ex = hierarchicalSelector(
                select_path, level + 1, operand, invalidValue, component,
                compileDesign, instance, pexpr, fileName, lineNumber,
                muteErrors, returnTypespec);
            return ex;
          }
          sInd++;
        }
      }
    }

  } else if (level == 0) {
    any* ex = hierarchicalSelector(
        select_path, level + 1, object, invalidValue, component, compileDesign,
        instance, pexpr, fileName, lineNumber, muteErrors, returnTypespec);
    return ex;
  }

  if (operation* oper = any_cast<operation*>(object)) {
    int opType = oper->VpiOpType();

    if (opType == vpiAssignmentPatternOp) {
      UHDM::VectorOfany* operands = oper->Operands();
      any* defaultPattern = nullptr;
      int sInd = 0;

      int bIndex = -1;
      if (component) {
        Parameter* baseP = component->getParameter(select_path[0]);
        if (baseP) {
          parameter* p = any_cast<parameter*>(baseP->getUhdmParam());
          if (p) {
            const typespec* tps = p->Typespec();
            if (tps) {
              if (tps->UhdmType() == uhdmpacked_array_typespec) {
                packed_array_typespec* tmp = (packed_array_typespec*)tps;
                tps = (typespec*)tmp->Elem_typespec();
              }
              if (tps->UhdmType() == uhdmstruct_typespec) {
                struct_typespec* sts = (struct_typespec*)tps;
                UHDM::VectorOftypespec_member* members = sts->Members();
                if (members) {
                  unsigned int i = 0;
                  for (UHDM::typespec_member* member : *members) {
                    if (member->VpiName() == elemName) {
                      bIndex = i;
                      break;
                    }
                    i++;
                  }
                }
              }
            }
          }
        }
      }

      for (auto operand : *operands) {
        UHDM_OBJECT_TYPE operandType = operand->UhdmType();
        if (operandType == uhdmtagged_pattern) {
          tagged_pattern* tpatt = (tagged_pattern*)operand;
          const typespec* tps = tpatt->Typespec();
          if (tps->VpiName() == "default") {
            defaultPattern = (any*)tpatt->Pattern();
          }
          if (elemName.size() && (tps->VpiName() == elemName)) {
            const any* patt = tpatt->Pattern();
            UHDM_OBJECT_TYPE pattType = patt->UhdmType();
            if (pattType == uhdmconstant) {
              expr* ex = reduceExpr((expr*)patt, invalidValue, component,
                                    compileDesign, instance, fileName,
                                    lineNumber, pexpr, muteErrors);
              return ex;
            } else if (pattType == uhdmoperation) {
              any* ex = hierarchicalSelector(
                  select_path, level + 1, (expr*)patt, invalidValue, component,
                  compileDesign, instance, pexpr, fileName, lineNumber,
                  muteErrors, returnTypespec);
              return ex;
            }
          }
        } else if (operandType == uhdmconstant) {
          if ((bIndex >= 0) && (bIndex == sInd)) {
            return (expr*)operand;
          }
        }
        sInd++;
      }
      if (defaultPattern) {
        expr* ex = any_cast<expr*>(defaultPattern);
        if (ex)
          ex = reduceExpr(ex, invalidValue, component, compileDesign, instance,
                          fileName, lineNumber, pexpr, muteErrors);
        return ex;
      }
    }
  }
  return nullptr;
}

long double CompileHelper::get_double(bool& invalidValue,
                                      const UHDM::expr* expr) {
  long double result = 0;
  if (const UHDM::constant* c = any_cast<const UHDM::constant*>(expr)) {
    int type = c->VpiConstType();
    std::string v = c->VpiValue();
    switch (type) {
      case vpiRealConst: {
        result = std::strtold(v.c_str() + strlen("REAL:"), 0);
        break;
      }
      default: {
        result = get_value(invalidValue, expr);
        break;
      }
    }
  } else {
    invalidValue = true;
  }
  return result;
}

int64_t CompileHelper::get_value(bool& invalidValue, const UHDM::expr* expr) {
  int64_t result = 0;
  int type = 0;
  std::string v;
  if (const UHDM::constant* c = any_cast<const UHDM::constant*>(expr)) {
    type = c->VpiConstType();
    v = c->VpiValue();
  } else if (const UHDM::variables* c =
                 any_cast<const UHDM::variables*>(expr)) {
    if (c->UhdmType() == uhdmenum_var) {
      type = vpiUIntConst;
      v = c->VpiValue();
    }
  } else {
    invalidValue = true;
  }
  if (!invalidValue) {
    switch (type) {
      case vpiBinaryConst: {
        StringUtils::ltrim(v, '\'');
        StringUtils::ltrim(v, 'b');
        try {
          result = std::strtoll(v.c_str() + strlen("BIN:"), 0, 2);
        } catch (...) {
          invalidValue = true;
        }
        break;
      }
      case vpiDecConst: {
        try {
          result = std::strtoll(v.c_str() + strlen("DEC:"), 0, 10);
        } catch (...) {
          invalidValue = true;
        }
        break;
      }
      case vpiHexConst: {
        StringUtils::ltrim(v, '\'');
        StringUtils::ltrim(v, 'h');
        try {
          result = std::strtoll(v.c_str() + strlen("HEX:"), 0, 16);
        } catch (...) {
          invalidValue = true;
        }
        break;
      }
      case vpiOctConst: {
        StringUtils::ltrim(v, '\'');
        StringUtils::ltrim(v, 'o');
        try {
          result = std::strtoll(v.c_str() + strlen("OCT:"), 0, 8);
        } catch (...) {
          invalidValue = true;
        }
        break;
      }
      case vpiIntConst: {
        try {
          result = std::strtoll(v.c_str() + strlen("INT:"), 0, 10);
        } catch (...) {
          invalidValue = true;
        }
        break;
      }
      case vpiUIntConst: {
        try {
          result = std::strtoull(v.c_str() + strlen("UINT:"), 0, 10);
        } catch (...) {
          invalidValue = true;
        }
        break;
      }
      case vpiScalar: {
        try {
          result = std::strtoll(v.c_str() + strlen("SCAL:"), 0, 2);
        } catch (...) {
          invalidValue = true;
        }
        break;
      }
      case vpiStringConst: {
        result = 0;
        break;
      }
      case vpiRealConst: {
        // Don't do the double precision math, leave it to client tools
        invalidValue = true;
        break;
      }
      default: {
        try {
          if (strstr(v.c_str(), "UINT:")) {
            result = std::strtoull(v.c_str() + strlen("UINT:"), 0, 10);
          } else {
            result = std::strtoll(v.c_str() + strlen("INT:"), 0, 10);
          }
        } catch (...) {
          invalidValue = true;
        }
        break;
      }
    }
  }
  return result;
}

any* CompileHelper::getValue(const std::string& name,
                             DesignComponent* component,
                             CompileDesign* compileDesign,
                             ValuedComponentI* instance,
                             const std::string& fileName, int lineNumber,
                             any* pexpr, bool reduce, bool muteErrors) {
  Serializer& s = compileDesign->getSerializer();
  Value* sval = nullptr;
  any* result = nullptr;

  if (strstr(name.c_str(), "::")) {
    std::vector<std::string> res;
    StringUtils::tokenizeMulti(name, "::", res);
    if (res.size() > 1) {
      const std::string& packName = res[0];
      const std::string& varName = res[1];
      Design* design = compileDesign->getCompiler()->getDesign();
      if (Package* pack = design->getPackage(packName)) {
        if (expr* val = pack->getComplexValue(varName)) {
          result = val;
        }
        if (result == nullptr) {
          if (Value* sval = pack->getValue(varName)) {
            UHDM::constant* c = s.MakeConstant();
            c->VpiValue(sval->uhdmValue());
            setRange(c, sval, compileDesign);
            c->VpiDecompile(sval->decompiledValue());
            c->VpiConstType(sval->vpiValType());
            c->VpiSize(sval->getSize());
            result = c;
          }
        }
      }
    }
  }

  if ((result == nullptr) && instance) {
    if (expr* val = instance->getComplexValue(name)) {
      result = val;
    }
    if (result == nullptr) {
      sval = instance->getValue(name);
      if (sval && sval->isValid()) {
        UHDM::constant* c = s.MakeConstant();
        c->VpiValue(sval->uhdmValue());
        setRange(c, sval, compileDesign);
        c->VpiDecompile(sval->decompiledValue());
        c->VpiConstType(sval->vpiValType());
        c->VpiSize(sval->getSize());
        result = c;
      }
    }
  }

  ValuedComponentI* tmpInstance = instance;
  while ((result == nullptr) && tmpInstance) {
    if (ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(tmpInstance)) {
      Netlist* netlist = inst->getNetlist();
      if (netlist) {
        UHDM::VectorOfparam_assign* param_assigns = netlist->param_assigns();
        if (param_assigns) {
          for (param_assign* param : *param_assigns) {
            if (param && param->Lhs()) {
              const std::string& param_name = param->Lhs()->VpiName();
              if (param_name == name) {
                if (substituteAssignedValue(param->Rhs(), compileDesign)) {
                  if (param->Rhs()->UhdmType() == uhdmoperation) {
                    operation* op = (operation*)param->Rhs();
                    int opType = op->VpiOpType();
                    if (opType == vpiAssignmentPatternOp) {
                      const any* lhs = param->Lhs();
                      any* rhs = (any*)param->Rhs();

                      rhs = expandPatternAssignment((expr*)lhs, (expr*)rhs,
                                                    component, compileDesign,
                                                    instance);
                      param->Rhs(rhs);
                      reorderAssignmentPattern(component, lhs, rhs,
                                               compileDesign, instance, 0);
                    }
                  }

                  ElaboratorListener listener(&s);
                  result = UHDM::clone_tree((any*)param->Rhs(), s, &listener);
                  break;
                }
              }
            }
          }
        }
      }
    }
    if (result) break;
    if (ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(tmpInstance)) {
      tmpInstance = (ValuedComponentI*)inst->getParentScope();
    } else if (FScope* inst = valuedcomponenti_cast<FScope*>(tmpInstance)) {
      tmpInstance = (ValuedComponentI*)inst->getParentScope();
    } else {
      tmpInstance = nullptr;
    }
  }

  if (result == nullptr) {
    if (instance) {
      if (expr* val = instance->getComplexValue(name)) {
        result = val;
      }
      if (result == nullptr) {
        sval = instance->getValue(name);
        if (sval && sval->isValid()) {
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue(sval->uhdmValue());
          setRange(c, sval, compileDesign);
          c->VpiDecompile(sval->decompiledValue());
          c->VpiConstType(sval->vpiValType());
          c->VpiSize(sval->getSize());
          result = c;
        }
      }
    }
  }

  if (component && (result == nullptr)) {
    if (expr* val = component->getComplexValue(name)) {
      result = val;
    }
    if (result == nullptr) {
      sval = component->getValue(name);
      if (sval && sval->isValid()) {
        UHDM::constant* c = s.MakeConstant();
        c->VpiValue(sval->uhdmValue());
        setRange(c, sval, compileDesign);
        c->VpiDecompile(sval->decompiledValue());
        c->VpiConstType(sval->vpiValType());
        c->VpiSize(sval->getSize());
        result = c;
      }
    }
  }

  if (component && (result == nullptr)) {
    UHDM::VectorOfparam_assign* param_assigns = component->getParam_assigns();
    if (param_assigns) {
      for (param_assign* param : *param_assigns) {
        if (param && param->Lhs()) {
          const std::string& param_name = param->Lhs()->VpiName();
          if (param_name == name) {
            if (substituteAssignedValue(param->Rhs(), compileDesign)) {
              if (param->Rhs()->UhdmType() == uhdmoperation) {
                operation* op = (operation*)param->Rhs();
                int opType = op->VpiOpType();
                if (opType == vpiAssignmentPatternOp) {
                  const any* lhs = param->Lhs();
                  any* rhs = (any*)param->Rhs();

                  rhs =
                      expandPatternAssignment((expr*)lhs, (expr*)rhs, component,
                                              compileDesign, instance);
                  param->Rhs(rhs);
                  reorderAssignmentPattern(component, lhs, rhs, compileDesign,
                                           instance, 0);
                }
              }

              ElaboratorListener listener(&s);
              result = UHDM::clone_tree((any*)param->Rhs(), s, &listener);
              break;
            }
          }
        }
      }
    }
  }
  if (component && (result == nullptr)) {
    for (auto tp : component->getTypeDefMap()) {
      TypeDef* tpd = tp.second;
      typespec* tps = tpd->getTypespec();
      if (tps && tps->UhdmType() == uhdmenum_typespec) {
        enum_typespec* etps = (enum_typespec*)tps;
        for (auto n : *etps->Enum_consts()) {
          if (n->VpiName() == name) {
            UHDM::constant* c = s.MakeConstant();
            c->VpiValue(n->VpiValue());
            setRange(c, sval, compileDesign);
            c->VpiSize(64);
            c->VpiConstType(vpiUIntConst);
            result = c;
          }
        }
      }
    }
  }

  if (result) {
    UHDM_OBJECT_TYPE resultType = result->UhdmType();
    if (resultType == uhdmconstant) {
    } else if (resultType == uhdmref_obj) {
      if (result->VpiName() != name) {
        any* tmp =
            getValue(result->VpiName(), component, compileDesign, instance,
                     fileName, lineNumber, pexpr, true, muteErrors);
        if (tmp) result = tmp;
      }
    } else if (resultType == uhdmoperation || resultType == uhdmhier_path ||
               resultType == uhdmbit_select ||
               resultType == uhdmsys_func_call) {
      if (reduce) {
        bool invalidValue = false;
        any* tmp =
            reduceExpr(result, invalidValue, component, compileDesign, instance,
                       fileName, lineNumber, pexpr, muteErrors);
        if (tmp) result = tmp;
      }
    } else {
      int setBreakpointHere = 1;
      setBreakpointHere++;
    }
  }
  /*
  if (result == nullptr) {
      ErrorContainer* errors =
  compileDesign->getCompiler()->getErrorContainer(); SymbolTable* symbols =
  compileDesign->getCompiler()->getSymbolTable(); std::string fileContent =
  FileUtils::getFileContent(fileName); std::string lineText =
  StringUtils::getLineInString(fileContent, lineNumber); Location loc
  (symbols->registerSymbol(fileName), lineNumber, 0,
                    symbols->registerSymbol(lineText));
      Error err(ErrorDefinition::ELAB_UNDEF_VARIABLE, loc);
      errors->addError(err);
  }
  */
  return result;
}

UHDM::any* CompileHelper::compileSelectExpression(
    DesignComponent* component, const FileContent* fC, NodeId Bit_select,
    const std::string& name, CompileDesign* compileDesign, UHDM::any* pexpr,
    ValuedComponentI* instance, bool reduce, bool muteErrors) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  if ((fC->Type(Bit_select) == slConstant_bit_select) &&
      (!fC->Sibling(Bit_select))) {
    Bit_select = fC->Child(Bit_select);
  }
  if ((fC->Type(Bit_select) == slBit_select) && (!fC->Sibling(Bit_select))) {
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
  NodeId lastBitExp = 0;
  while (Bit_select) {
    if (fC->Type(Bit_select) == VObjectType::slBit_select ||
        fC->Type(Bit_select) == VObjectType::slConstant_bit_select ||
        fC->Type(Bit_select) == VObjectType::slConstant_primary ||
        fC->Type(Bit_select) == VObjectType::slConstant_expression ||
        fC->Type(Bit_select) == VObjectType::slExpression) {
      NodeId bitexp = fC->Child(Bit_select);
      bool advanceBitSelect = false;
      if (fC->Type(Bit_select) == VObjectType::slConstant_expression) {
        bitexp = Bit_select;
        advanceBitSelect = true;
      }
      if (fC->Type(Bit_select) == VObjectType::slExpression) {
        bitexp = Bit_select;
        advanceBitSelect = true;
      }
      if (bitexp) {
        while (bitexp) {
          if ((fC->Type(bitexp) != slConstant_expression) &&
              (fC->Type(bitexp) != slExpression)) {
            break;
          }
          expr* sel =
              (expr*)compileExpression(component, fC, bitexp, compileDesign,
                                       pexpr, instance, reduce, muteErrors);

          if (result) {
            UHDM::var_select* var_select = (UHDM::var_select*)result;
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
            if (sel->VpiParent() == nullptr) sel->VpiParent(bit_select);
            ref_obj* ref = s.MakeRef_obj();
            bit_select->VpiParent(ref);
            ref->VpiName(name);
            ref->VpiParent(pexpr);
          }
          lastBitExp = bitexp;
          if (advanceBitSelect) Bit_select = bitexp;
          bitexp = fC->Sibling(bitexp);
        }
      }
    } else if (fC->Type(Bit_select) == VObjectType::slPart_select_range ||
               fC->Type(Bit_select) ==
                   VObjectType::slConstant_part_select_range) {
      NodeId Constant_range = fC->Child(Bit_select);
      expr* sel = (expr*)compilePartSelectRange(component, fC, Constant_range,
                                                name, compileDesign, pexpr,
                                                instance, reduce, muteErrors);
      if (result) {
        UHDM::var_select* var_select = (UHDM::var_select*)result;
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
      std::string hname = name;
      hier_path* path = s.MakeHier_path();
      UHDM::VectorOfany* elems = s.MakeAnyVec();
      ref_obj* r1 = s.MakeRef_obj();
      r1->VpiName(name);
      r1->VpiFullName(name);
      path->Path_elems(elems);
      elems->push_back(r1);
      r1->VpiParent(path);
      while (Bit_select) {
        if (fC->Type(Bit_select) == VObjectType::slStringConst) {
          NodeId tmp = fC->Sibling(Bit_select);
          if (((fC->Type(tmp) == slConstant_bit_select) ||
               (fC->Type(tmp) == slBit_select)) &&
              (fC->Child(tmp) != 0)) {
            any* sel =
                compileExpression(component, fC, Bit_select, compileDesign,
                                  pexpr, instance, reduce, muteErrors);
            if (sel) {
              if (sel->UhdmType() == uhdmhier_path) {
                hier_path* p = (hier_path*)sel;
                for (auto el : *p->Path_elems()) {
                  elems->push_back(el);
                  el->VpiParent(path);
                  std::string n = el->VpiName();
                  if (el->UhdmType() == uhdmbit_select) {
                    bit_select* s = (bit_select*)el;
                    const expr* index = s->VpiIndex();
                    std::string ind = index->VpiDecompile();
                    if (ind.size() == 0) ind = index->VpiName();
                    n += "[" + ind + "]";
                  }
                  hname += "." + n;
                }
                break;
              } else {
                elems->push_back(sel);
                sel->VpiParent(path);
                hname += "." + sel->VpiName();
              }
            }
          } else {
            ref_obj* r2 = s.MakeRef_obj();
            r2->VpiName(fC->SymName(Bit_select));
            r2->VpiFullName(fC->SymName(Bit_select));
            elems->push_back(r2);
            hname += "." + fC->SymName(Bit_select);
          }
        }
        Bit_select = fC->Sibling(Bit_select);
      }
      path->VpiName(hname);
      path->VpiFullName(hname);
      path->VpiFile(fC->getFileName());
      path->VpiLineNo(fC->Line(Bit_select));
      path->VpiColumnNo(fC->Column(Bit_select));
      path->VpiEndLineNo(fC->EndLine(Bit_select));
      path->VpiEndColumnNo(fC->EndColumn(Bit_select));
      path->VpiParent(pexpr);
      result = path;
      break;
    }
    Bit_select = fC->Sibling(Bit_select);
    if (lastBitExp && (Bit_select == lastBitExp)) {
      Bit_select = fC->Sibling(Bit_select);
    }
  }
  return result;
}

UHDM::any* CompileHelper::compileExpression(
    DesignComponent* component, const FileContent* fC, NodeId parent,
    CompileDesign* compileDesign, UHDM::any* pexpr, ValuedComponentI* instance,
    bool reduce, bool muteErrors) {
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
  switch (parentType) {
    case VObjectType::slIntegerAtomType_Byte: {
      result = s.MakeByte_var();
      break;
    }
    case VObjectType::slIntegerAtomType_Int: {
      result = s.MakeInt_var();
      break;
    }
    case VObjectType::slIntegerAtomType_LongInt: {
      result = s.MakeLong_int_var();
      break;
    }
    case VObjectType::slIntegerAtomType_Shortint: {
      result = s.MakeShort_int_var();
      break;
    }
    case VObjectType::slValue_range: {
      UHDM::operation* list_op = s.MakeOperation();
      list_op->VpiOpType(vpiListOp);
      UHDM::VectorOfany* operands = s.MakeAnyVec();
      list_op->Operands(operands);
      NodeId lexpr = child;
      NodeId rexpr = fC->Sibling(lexpr);
      if (expr* op = any_cast<expr*>(
              compileExpression(component, fC, lexpr, compileDesign, pexpr,
                                instance, reduce, muteErrors))) {
        operands->push_back(op);
      }
      if (rexpr) {
        if (expr* op = any_cast<expr*>(
                compileExpression(component, fC, rexpr, compileDesign, pexpr,
                                  instance, reduce, muteErrors))) {
          operands->push_back(op);
        }
      }
      list_op->VpiFile(fC->getFileName());
      list_op->VpiLineNo(fC->Line(child));
      list_op->VpiColumnNo(fC->Column(child));
      list_op->VpiEndLineNo(fC->EndLine(child));
      list_op->VpiEndColumnNo(fC->EndColumn(child));
      list_op->Attributes(attributes);
      result = list_op;
      result->VpiFile(fC->getFileName(parent));
      result->VpiLineNo(fC->Line(parent));
      result->VpiColumnNo(fC->Column(parent));
      result->VpiEndLineNo(fC->EndLine(parent));
      result->VpiEndColumnNo(fC->EndColumn(parent));
      return result;
    }
    case VObjectType::slNet_lvalue: {
      UHDM::operation* operation = s.MakeOperation();
      UHDM::VectorOfany* operands = s.MakeAnyVec();
      operation->Attributes(attributes);
      result = operation;
      operation->VpiParent(pexpr);
      operation->Operands(operands);
      operation->VpiOpType(vpiConcatOp);
      result->VpiFile(fC->getFileName(parent));
      result->VpiLineNo(fC->Line(parent));
      result->VpiColumnNo(fC->Column(parent));
      result->VpiEndLineNo(fC->EndLine(parent));
      result->VpiEndColumnNo(fC->EndColumn(parent));
      NodeId Expression = parent;
      while (Expression) {
        UHDM::any* exp = compileExpression(component, fC, fC->Child(Expression),
                                           compileDesign, pexpr, instance,
                                           reduce, muteErrors);
        if (exp) {
          operands->push_back(exp);
          if (exp->VpiParent()) {
            ((any*)exp->VpiParent())->VpiParent(operation);
          } else {
            exp->VpiParent(operation);
          }
        }
        Expression = fC->Sibling(Expression);
      }
      return result;
    }
    case VObjectType::slConcatenation: {
      UHDM::operation* operation = s.MakeOperation();
      UHDM::VectorOfany* operands = s.MakeAnyVec();
      operation->Attributes(attributes);
      result = operation;
      operation->VpiParent(pexpr);
      operation->Operands(operands);
      operation->VpiOpType(vpiConcatOp);
      NodeId Expression = fC->Child(parent);
      while (Expression) {
        UHDM::any* exp =
            compileExpression(component, fC, Expression, compileDesign, pexpr,
                              instance, reduce, muteErrors);
        if (exp) operands->push_back(exp);
        Expression = fC->Sibling(Expression);
      }
      break;
    }
    case VObjectType::slDelay2:
    case VObjectType::slDelay3: {
      NodeId MinTypMax = child;
      if (fC->Sibling(MinTypMax)) {
        UHDM::operation* operation = s.MakeOperation();
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        operation->Operands(operands);
        operation->VpiOpType(vpiListOp);
        result = operation;
        NodeId Expression = MinTypMax;
        while (Expression) {
          UHDM::any* exp =
              compileExpression(component, fC, Expression, compileDesign, pexpr,
                                instance, reduce, muteErrors);
          if (exp) operands->push_back(exp);
          Expression = fC->Sibling(Expression);
        }
        return result;
      }
      break;
    }
    case VObjectType::slConstant_mintypmax_expression:
    case VObjectType::slMintypmax_expression: {
      NodeId Expression = child;
      operation* op = s.MakeOperation();
      op->VpiOpType(vpiMinTypMaxOp);
      op->VpiParent(pexpr);
      UHDM::VectorOfany* operands = s.MakeAnyVec();
      op->Operands(operands);
      result = op;
      while (Expression) {
        expr* sExpr =
            (expr*)compileExpression(component, fC, Expression, compileDesign,
                                     op, instance, reduce, muteErrors);
        if (sExpr) operands->push_back(sExpr);
        Expression = fC->Sibling(Expression);
      }
      return result;
    }
    case VObjectType::slExpression: {
      NodeId Iff = fC->Sibling(parent);
      if (fC->Type(Iff) == slIff) {
        operation* op = s.MakeOperation();
        op->VpiOpType(vpiIffOp);
        op->VpiParent(pexpr);
        UHDM::VectorOfany* operands = s.MakeAnyVec();
        op->Operands(operands);
        result = op;
        expr* lExpr =
            (expr*)compileExpression(component, fC, child, compileDesign, op,
                                     instance, reduce, muteErrors);
        if (lExpr) operands->push_back(lExpr);
        NodeId Expr = fC->Sibling(Iff);
        expr* rExpr =
            (expr*)compileExpression(component, fC, Expr, compileDesign, op,
                                     instance, reduce, muteErrors);
        if (rExpr) operands->push_back(rExpr);
        return result;
      }
      break;
    }
    case VObjectType::slClass_new: {
      UHDM::method_func_call* sys = s.MakeMethod_func_call();
      sys->VpiName("new");
      sys->VpiParent(pexpr);
      NodeId argListNode = child;
      UHDM::VectorOfany* arguments =
          compileTfCallArguments(component, fC, argListNode, compileDesign, sys,
                                 instance, reduce, muteErrors);
      sys->Tf_call_args(arguments);
      result = sys;
      return result;
    }
    default:
      break;
  }

  if ((parentType == VObjectType::slVariable_lvalue) &&
      (childType == VObjectType::slVariable_lvalue)) {
    UHDM::operation* operation = s.MakeOperation();
    UHDM::VectorOfany* operands = s.MakeAnyVec();
    operation->Attributes(attributes);
    result = operation;
    operation->VpiParent(pexpr);
    operation->Operands(operands);
    operation->VpiOpType(vpiConcatOp);
    result->VpiFile(fC->getFileName(child));
    result->VpiLineNo(fC->Line(child));
    result->VpiColumnNo(fC->Column(child));
    result->VpiEndLineNo(fC->EndLine(child));
    result->VpiEndColumnNo(fC->EndColumn(child));
    NodeId Expression = child;
    while (Expression) {
      NodeId n = fC->Child(Expression);
      if (fC->Type(n) == slVariable_lvalue) {
        n = Expression;
      }
      UHDM::any* exp = compileExpression(component, fC, n, compileDesign, pexpr,
                                         instance, reduce, muteErrors);
      if (exp) {
        operands->push_back(exp);
        exp->VpiParent(operation);
      }
      Expression = fC->Sibling(Expression);
    }
    return result;
  }

  if (result == nullptr) {
    if (child) {
      switch (childType) {
        case VObjectType::slNull_keyword: {
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue("UINT:0");
          c->VpiDecompile("0");
          c->VpiSize(64);
          c->VpiConstType(vpiNullConst);
          result = c;
          break;
        }
        case VObjectType::slDollar_keyword: {
          UHDM::constant* c = s.MakeConstant();
          c->VpiConstType(vpiUnboundedConst);
          c->VpiValue("STRING:$");
          c->VpiDecompile("$");
          c->VpiSize(1);
          result = c;
          break;
        }
        case VObjectType::slThis_keyword: {
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue("STRING:this");
          c->VpiDecompile("this");
          c->VpiConstType(vpiStringConst);
          c->VpiSize(4);
          result = c;
          break;
        }
        case VObjectType::slSuper_keyword: {
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue("STRING:super");
          c->VpiDecompile("super");
          c->VpiConstType(vpiStringConst);
          c->VpiSize(5);
          result = c;
          break;
        }
        case VObjectType::slThis_dot_super: {
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue("STRING:this.super");
          c->VpiDecompile("this.super");
          c->VpiConstType(vpiStringConst);
          c->VpiSize(10);
          result = c;
          break;
        }
        case VObjectType::slArray_member_label: {
          UHDM::operation* operation = s.MakeOperation();
          UHDM::VectorOfany* operands = s.MakeAnyVec();
          operation->Attributes(attributes);
          result = operation;
          operation->VpiParent(pexpr);
          operation->Operands(operands);
          operation->VpiOpType(vpiConcatOp);
          result->VpiFile(fC->getFileName(child));
          result->VpiLineNo(fC->Line(child));
          result->VpiColumnNo(fC->Column(child));
          result->VpiEndLineNo(fC->EndLine(child));
          result->VpiEndColumnNo(fC->EndColumn(child));
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
              UHDM::any* exp =
                  compileExpression(component, fC, the_exp, compileDesign,
                                    pexpr, instance, reduce, muteErrors);
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
            NodeId var = fC->Sibling(child);
            if (fC->Type(var) == slVariable_lvalue) {
              var = fC->Child(var);
            }
            if (UHDM::any* operand =
                    compileExpression(component, fC, var, compileDesign, op,
                                      instance, reduce, muteErrors)) {
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
          if (UHDM::any* operand = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, op,
                  instance, reduce, muteErrors))
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
          if (UHDM::any* operand = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, op,
                  instance, reduce, muteErrors))
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
          if (UHDM::any* operand = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, op,
                  instance, reduce, muteErrors))
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
          result = compileExpression(component, fC, child, compileDesign, pexpr,
                                     instance, reduce, muteErrors);
          break;
        case VObjectType::slComplex_func_call: {
          result = compileComplexFuncCall(component, fC, child, compileDesign,
                                          pexpr, instance, reduce, muteErrors);
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
            expr* cExpr = (expr*)compileExpression(component, fC, Expression,
                                                   compileDesign, op, instance,
                                                   reduce, muteErrors);
            if (cExpr) operands->push_back(cExpr);
            while (Sibling) {
              expr* sExpr = (expr*)compileExpression(
                  component, fC, Sibling, compileDesign, op, instance, reduce,
                  muteErrors);
              if (sExpr) operands->push_back(sExpr);
              Sibling = fC->Sibling(Sibling);
            }
          } else {
            result = (expr*)compileExpression(component, fC, Expression,
                                              compileDesign, pexpr, instance,
                                              reduce, muteErrors);
          }
          break;
        }
        case VObjectType::slRandomize_call: {
          result = compileRandomizeCall(component, fC, fC->Child(child),
                                        compileDesign, pexpr);
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
            expr* cExpr = (expr*)compileExpression(
                component, fC, fC->Child(child), compileDesign, op, instance,
                reduce, muteErrors);
            if (cExpr) operands->push_back(cExpr);
            while (Sibling) {
              expr* sExpr = (expr*)compileExpression(
                  component, fC, Sibling, compileDesign, op, instance, reduce,
                  muteErrors);
              if (sExpr) operands->push_back(sExpr);
              Sibling = fC->Sibling(Sibling);
            }
          } else {
            result = (expr*)compileExpression(component, fC, fC->Child(child),
                                              compileDesign, pexpr, instance,
                                              reduce, muteErrors);
          }
          break;
        }
        case VObjectType::slTagged: {
          NodeId Identifier = fC->Sibling(child);
          NodeId Expression = fC->Sibling(Identifier);
          UHDM::tagged_pattern* pattern = s.MakeTagged_pattern();
          pattern->VpiName(fC->SymName(Identifier));
          if (Expression)
            pattern->Pattern(compileExpression(component, fC, Expression,
                                               compileDesign, pattern, instance,
                                               reduce, muteErrors));
          result = pattern;
          break;
        }
        case VObjectType::slEvent_expression: {
          NodeId subExpr = child;
          UHDM::any* opL =
              compileExpression(component, fC, subExpr, compileDesign, pexpr,
                                instance, reduce, muteErrors);
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
                  compileExpression(component, fC, subRExpr, compileDesign,
                                    pexpr, instance, reduce, muteErrors);
              operands->push_back(opR);
              op = fC->Sibling(subRExpr);
            } else if (fC->Type(op) == VObjectType::slComma_operator) {
              operation->VpiOpType(vpiListOp);
              NodeId subRExpr = fC->Sibling(op);
              UHDM::any* opR =
                  compileExpression(component, fC, subRExpr, compileDesign,
                                    pexpr, instance, reduce, muteErrors);
              operands->push_back(opR);
              op = fC->Sibling(subRExpr);
            }
          }
          break;
        }
        case VObjectType::slExpression:
        case VObjectType::slConstant_expression: {
          UHDM::any* opL =
              compileExpression(component, fC, child, compileDesign, pexpr,
                                instance, reduce, muteErrors);
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
            UHDM::VectorOfattribute* attributes =
                compileAttributes(component, fC, rval, compileDesign);
            while (fC->Type(rval) == slAttribute_instance)
              rval = fC->Sibling(rval);
            operation->Attributes(attributes);
          }

          if (opType == VObjectType::slInsideOp) {
            // Because open_range_list is stored in { }, it is being interpreted
            // as a concatenation operation. Code below constructs it manually.
            // Example tree:
            // n<> u<164> t<InsideOp> p<180> s<179> l<9>
            // n<> u<179> t<Expression> p<180> c<178> l<9>
            //    n<> u<178> t<Primary> p<179> c<177> l<9>
            //        n<> u<177> t<Concatenation> p<178> c<168> l<9>
            //            n<> u<168> t<Expression> p<177> c<167> s<172> l<9>
            //                n<> u<167> t<Primary> p<168> c<166> l<9>
            //                    n<> u<166> t<Primary_literal> p<167> c<165>
            //                    l<9>
            //                        n<OP_1> u<165> t<StringConst> p<166> l<9>
            //            n<> u<172> t<Expression> p<177> c<171> s<176> l<10>
            //                n<> u<171> t<Primary> p<172> c<170> l<10>
            //                    n<> u<170> t<Primary_literal> p<171> c<169>
            //                    l<10>
            //                        n<OP_2> u<169> t<StringConst> p<170> l<10>
            //            n<> u<176> t<Expression> p<177> c<175> l<11>
            //                n<> u<175> t<Primary> p<176> c<174> l<11>
            //                    n<> u<174> t<Primary_literal> p<175> c<173>
            //                    l<11>
            //                        n<OP_3> u<173> t<StringConst> p<174> l<11>
            NodeId false_concat = fC->Child(fC->Child(rval));
            NodeId Expression = fC->Child(false_concat);
            // Open range list members
            while (Expression) {
              UHDM::any* exp =
                  compileExpression(component, fC, Expression, compileDesign,
                                    pexpr, instance, reduce, muteErrors);
              if (exp) operands->push_back(exp);
              Expression = fC->Sibling(Expression);
            }
            // RHS is done, skip handling below
            break;
          } else if (opType == VObjectType::slOpen_range_list) {
            NodeId Value_range = fC->Child(op);
            NodeId Expression = fC->Child(Value_range);
            while (Expression) {
              UHDM::any* exp =
                  compileExpression(component, fC, Expression, compileDesign,
                                    pexpr, instance, reduce, muteErrors);
              if (exp) operands->push_back(exp);
              Expression = fC->Sibling(Expression);
            }
            // RHS is done, skip handling below
            break;
          }

          UHDM::any* opR =
              compileExpression(component, fC, rval, compileDesign, operation,
                                instance, reduce, muteErrors);
          if (opR) {
            setParentNoOverride(opR, operation);
            operands->push_back(opR);
          }
          if (opType == VObjectType::slQmark ||
              opType == VObjectType::slConditional_operator) {  // Ternary op
            rval = fC->Sibling(rval);
            opR = compileExpression(component, fC, rval, compileDesign,
                                    operation, instance, reduce, muteErrors);
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
            result =
                compileBits(component, fC, List_of_arguments, compileDesign,
                            pexpr, instance, reduce, false, muteErrors);
          } else if (name == "$size") {
            NodeId List_of_arguments = fC->Sibling(child);
            result =
                compileBits(component, fC, List_of_arguments, compileDesign,
                            pexpr, instance, reduce, true, muteErrors);
          } else if (name == "$clog2") {
            NodeId List_of_arguments = fC->Sibling(child);
            result =
                compileClog2(component, fC, List_of_arguments, compileDesign,
                             pexpr, instance, reduce, muteErrors);
          } else if (name == "$typename") {
            NodeId List_of_arguments = fC->Sibling(child);
            result = compileTypename(component, fC, List_of_arguments,
                                     compileDesign, pexpr, instance, reduce);
          } else {
            UHDM::sys_func_call* sys = s.MakeSys_func_call();
            sys->VpiName(name);
            sys->VpiParent(pexpr);
            NodeId argListNode = fC->Sibling(child);
            VectorOfany* arguments = compileTfCallArguments(
                component, fC, argListNode, compileDesign, sys, instance,
                reduce, muteErrors);
            sys->Tf_call_args(arguments);
            result = sys;
          }
          break;
        }
        case VObjectType::slVariable_lvalue: {
          UHDM::any* variable =
              compileExpression(component, fC, fC->Child(child), compileDesign,
                                pexpr, instance, reduce, muteErrors);
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
                UHDM::VectorOfattribute* attributes =
                    compileAttributes(component, fC, rval, compileDesign);
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
                UHDM::VectorOfattribute* attributes =
                    compileAttributes(component, fC, rval, compileDesign);
                while (fC->Type(rval) == slAttribute_instance)
                  rval = fC->Sibling(rval);
                operation->Attributes(attributes);
              }

              UHDM::any* rexp =
                  compileExpression(component, fC, rval, compileDesign, pexpr,
                                    instance, reduce, muteErrors);
              operands->push_back(rexp);
            }
          } else {
            result = variable;
          }
          break;
        }
        case VObjectType::slAssignment_pattern: {
          result = compileAssignmentPattern(component, fC, child, compileDesign,
                                            pexpr, instance);
          break;
        }
        case VObjectType::slSequence_expr: {
          if (fC->Sibling(parent) == 0) {
            result = compileExpression(component, fC, child, compileDesign,
                                       nullptr, instance, reduce, muteErrors);
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
                                  nullptr, instance, reduce, muteErrors);
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
            if (tps && tps->UhdmType() == uhdmunsupported_typespec) {
              component->needLateTypedefBinding(operation);
            }
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
            NodeId paramId = fC->Sibling(child);
            NodeId selectId = fC->Sibling(paramId);
            const std::string& n = fC->SymName(paramId);
            name = packageName + "::" + n;
            Package* pack =
                compileDesign->getCompiler()->getDesign()->getPackage(
                    packageName);
            if (pack) {
              UHDM::VectorOfparam_assign* param_assigns =
                  pack->getParam_assigns();
              if (param_assigns) {
                for (param_assign* param : *param_assigns) {
                  if (param && param->Lhs()) {
                    const std::string& param_name = param->Lhs()->VpiName();
                    if (param_name == n) {
                      if (substituteAssignedValue(param->Rhs(),
                                                  compileDesign)) {
                        ElaboratorListener listener(&s);
                        result =
                            UHDM::clone_tree((any*)param->Rhs(), s, &listener);
                      }
                      break;
                    }
                  }
                }
              }
              if (result && selectId) {
                if (fC->Type(selectId) == slConstant_select) {
                  selectId = fC->Child(selectId);
                }
                if (fC->Child(selectId) || fC->Sibling(selectId))
                  result = compileSelectExpression(
                      component, fC, selectId, name, compileDesign, pexpr,
                      instance, reduce, muteErrors);
              }
              if (result == nullptr) sval = pack->getValue(n);
            }
          } else if (childType == VObjectType::slClass_type) {
            const std::string& packageName = fC->SymName(fC->Child(child));
            const std::string& n = fC->SymName(fC->Sibling(parent));
            name = packageName + "::" + n;
            Package* pack =
                compileDesign->getCompiler()->getDesign()->getPackage(
                    packageName);
            if (pack) {
              UHDM::VectorOfparam_assign* param_assigns =
                  pack->getParam_assigns();
              if (param_assigns) {
                for (param_assign* param : *param_assigns) {
                  if (param && param->Lhs()) {
                    const std::string& param_name = param->Lhs()->VpiName();
                    if (param_name == n) {
                      if (substituteAssignedValue(param->Rhs(),
                                                  compileDesign)) {
                        ElaboratorListener listener(&s);
                        result =
                            UHDM::clone_tree((any*)param->Rhs(), s, &listener);
                      }
                      break;
                    }
                  }
                }
              }
              if (result == nullptr) sval = pack->getValue(n);
            }
          } else {
            NodeId rhs = 0;
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
                result = compileSelectExpression(component, fC, Bit_select,
                                                 name, compileDesign, pexpr,
                                                 instance, reduce, muteErrors);
              }
              if (result) break;
            }
            if (result) break;
            if (reduce && instance) sval = instance->getValue(name);
          }
          if (result) break;

          if (sval == NULL || (sval && !sval->isValid())) {
            if (instance) {
              ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(instance);
              if (inst) {
                Netlist* netlist = inst->getNetlist();
                if (netlist) {
                  UHDM::VectorOfparam_assign* param_assigns =
                      netlist->param_assigns();
                  if (param_assigns) {
                    for (param_assign* param_ass : *param_assigns) {
                      if (param_ass && param_ass->Lhs()) {
                        const std::string& param_name =
                            param_ass->Lhs()->VpiName();
                        if (param_name == name) {
                          if (reduce ||
                              (param_ass->Rhs()->UhdmType() == uhdmconstant)) {
                            if (substituteAssignedValue(param_ass->Rhs(),
                                                        compileDesign)) {
                              ElaboratorListener listener(&s);
                              result = UHDM::clone_tree((any*)param_ass->Rhs(),
                                                        s, &listener);
                              const any* lhs = param_ass->Lhs();
                              expr* res = (expr*)result;
                              const typespec* tps = nullptr;
                              if (lhs->UhdmType() == UHDM::uhdmtype_parameter) {
                                tps = ((UHDM::type_parameter*)lhs)->Typespec();
                              } else {
                                tps = ((UHDM::parameter*)lhs)->Typespec();
                              }
                              if (tps && (res->Typespec() == nullptr)) {
                                res->Typespec((UHDM::typespec*)tps);
                              }
                              break;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            if (component && (result == nullptr)) {
              UHDM::VectorOfparam_assign* param_assigns =
                  component->getParam_assigns();
              if (param_assigns) {
                for (param_assign* param_ass : *param_assigns) {
                  if (param_ass && param_ass->Lhs()) {
                    const std::string& param_name = param_ass->Lhs()->VpiName();
                    bool paramFromPackage = false;
                    if (param_ass->Lhs()->UhdmType() == uhdmparameter) {
                      const parameter* tp = (parameter*)param_ass->Lhs();
                      if (tp->VpiImported() != "") {
                        paramFromPackage = true;
                      }
                    }
                    if (param_name == name) {
                      if (reduce ||
                          (paramFromPackage &&
                           (param_ass->Rhs()->UhdmType() == uhdmconstant))) {
                        if (substituteAssignedValue(param_ass->Rhs(),
                                                    compileDesign)) {
                          ElaboratorListener listener(&s);
                          result = UHDM::clone_tree((any*)param_ass->Rhs(), s,
                                                    &listener);
                          const any* lhs = param_ass->Lhs();
                          expr* res = (expr*)result;
                          const typespec* tps = nullptr;
                          if (lhs->UhdmType() == UHDM::uhdmtype_parameter) {
                            tps = ((UHDM::type_parameter*)lhs)->Typespec();
                          } else {
                            tps = ((UHDM::parameter*)lhs)->Typespec();
                          }
                          if (tps && (res->Typespec() == nullptr)) {
                            res->Typespec((UHDM::typespec*)tps);
                          }
                          break;
                        }
                      }
                    }
                  }
                }
              }
            }
            if (result == nullptr) {
              UHDM::ref_obj* ref = s.MakeRef_obj();
              ref->VpiName(name);
              ref->VpiParent(pexpr);
              if (pexpr) {
                UHDM::any* var =
                    bindVariable(component, pexpr, name, compileDesign);
                if (var)
                  ref->Actual_group(var);
                else if (component)
                  component->needLateBinding(ref);
              } else if (instance) {
                UHDM::any* var =
                    bindVariable(component, instance, name, compileDesign);
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
            c->VpiConstType(sval->vpiValType());
            c->VpiSize(sval->getSize());
            result = c;
          }
          break;
        }
        case VObjectType::slIntConst:
        case VObjectType::slRealConst:
        case VObjectType::slNumber_1Tickb1:
        case VObjectType::slNumber_1TickB1:
        case VObjectType::slInitVal_1Tickb1:
        case VObjectType::slInitVal_1TickB1:
        case VObjectType::slScalar_1Tickb1:
        case VObjectType::slScalar_1TickB1:
        case VObjectType::sl1:
        case VObjectType::slScalar_Tickb1:
        case VObjectType::slScalar_TickB1:
        case VObjectType::slNumber_Tickb1:
        case VObjectType::slNumber_TickB1:
        case VObjectType::slNumber_Tick1:
        case VObjectType::slNumber_1Tickb0:
        case VObjectType::slNumber_1TickB0:
        case VObjectType::slInitVal_1Tickb0:
        case VObjectType::slInitVal_1TickB0:
        case VObjectType::slScalar_1Tickb0:
        case VObjectType::slScalar_1TickB0:
        case VObjectType::sl0:
        case VObjectType::slScalar_Tickb0:
        case VObjectType::slScalar_TickB0:
        case VObjectType::slNumber_Tickb0:
        case VObjectType::slNumber_TickB0:
        case VObjectType::slNumber_Tick0:
        case VObjectType::slNumber_1TickBX:
        case VObjectType::slNumber_1TickbX:
        case VObjectType::slNumber_1Tickbx:
        case VObjectType::slNumber_1TickBx:
        case VObjectType::slInitVal_1Tickbx:
        case VObjectType::slInitVal_1TickbX:
        case VObjectType::slInitVal_1TickBx:
        case VObjectType::slInitVal_1TickBX:
        case VObjectType::slX:
        case VObjectType::slZ:
        case VObjectType::slTime_literal:
        case VObjectType::slStringLiteral: {
          result = compileConst(fC, child, s);
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
              exp_slice = compileBits(component, fC, Type, compileDesign, pexpr,
                                      instance, true, false, muteErrors);
            } else {
              exp_slice = compileExpression(component, fC, Constant_expression,
                                            compileDesign, pexpr, instance,
                                            reduce, muteErrors);
            }
            Stream_concatenation = fC->Sibling(Slice_size);
          } else {
            Stream_concatenation = Slice_size;
          }

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
          if (exp_slice) operands->push_back(exp_slice);

          UHDM::operation* concat_op = s.MakeOperation();
          UHDM::VectorOfany* concat_ops = s.MakeAnyVec();
          operands->push_back(concat_op);
          concat_op->VpiParent(operation);
          concat_op->Operands(concat_ops);
          concat_op->VpiOpType(vpiConcatOp);

          NodeId Stream_expression = fC->Child(Stream_concatenation);
          while (Stream_expression) {
            NodeId Expression = fC->Child(Stream_expression);
            UHDM::any* exp_var =
                compileExpression(component, fC, Expression, compileDesign,
                                  pexpr, instance, reduce, muteErrors);
            if (exp_var) concat_ops->push_back(exp_var);
            Stream_expression = fC->Sibling(Stream_expression);
          }
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
          UHDM::VectorOfany* operands = s.MakeAnyVec();
          NodeId Expression = fC->Child(child);
          while (Expression) {
            UHDM::any* exp =
                compileExpression(component, fC, Expression, compileDesign,
                                  pexpr, instance, reduce, muteErrors);
            if (exp) operands->push_back(exp);
            Expression = fC->Sibling(Expression);
          }
          UHDM::operation* operation = s.MakeOperation();
          operation->Attributes(attributes);
          result = operation;
          operation->VpiParent(pexpr);
          operation->Operands(operands);
          operation->VpiOpType(vpiConcatOp);
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
            UHDM::any* exp =
                compileExpression(component, fC, Expression, compileDesign,
                                  pexpr, instance, reduce, muteErrors);
            if (exp) operands->push_back(exp);
            Expression = fC->Sibling(Expression);
          }
          break;
        }
        case VObjectType::slSubroutine_call: {
          NodeId Dollar_keyword = fC->Child(child);
          NodeId nameId = 0;
          if (fC->Type(Dollar_keyword) == slStringConst) {
            nameId = Dollar_keyword;
          } else {
            nameId = fC->Sibling(Dollar_keyword);
          }
          NodeId List_of_arguments = fC->Sibling(nameId);
          std::string name = fC->SymName(nameId);
          if (name == "bits") {
            NodeId Expression = fC->Child(List_of_arguments);
            result = compileBits(component, fC, Expression, compileDesign,
                                 pexpr, instance, reduce, false, muteErrors);
          } else if (name == "size") {
            NodeId Expression = fC->Child(List_of_arguments);
            result = compileBits(component, fC, Expression, compileDesign,
                                 pexpr, instance, reduce, true, muteErrors);
          } else if (name == "clog2") {
            result =
                compileClog2(component, fC, List_of_arguments, compileDesign,
                             pexpr, instance, reduce, muteErrors);
          } else if (name == "typename") {
            result = compileTypename(component, fC, List_of_arguments,
                                     compileDesign, pexpr, instance, reduce);
          } else if (fC->Type(Dollar_keyword) == slStringConst ||
                     fC->Type(Dollar_keyword) == slClass_scope) {
            if (fC->Type(Dollar_keyword) == slClass_scope) {
              NodeId Class_type = fC->Child(Dollar_keyword);
              NodeId Class_type_name = fC->Child(Class_type);
              NodeId Class_scope_name = fC->Sibling(Dollar_keyword);
              name = fC->SymName(Class_type_name) +
                     "::" + fC->SymName(Class_scope_name);
            }
            NodeId Select = fC->Sibling(Dollar_keyword);
            if (fC->Type(Select) == slConstant_bit_select ||
                fC->Type(Select) == slBit_select) {
              result = compileExpression(component, fC, Dollar_keyword,
                                         compileDesign, pexpr, instance, reduce,
                                         muteErrors);
            } else {
              bool invalidValue = false;
              UHDM::func_call* fcall = s.MakeFunc_call();
              fcall->VpiName(name);

              auto [func, actual_comp] =
                  getTaskFunc(name, component, compileDesign, pexpr);
              fcall->Function(any_cast<function*>(func));
              VectorOfany* args = compileTfCallArguments(
                  component, fC, List_of_arguments, compileDesign, fcall,
                  instance, reduce, muteErrors);
              if (reduce) {
                const std::string& fileName = fC->getFileName();
                int lineNumber = fC->Line(nameId);
                if (func == nullptr) {
                  ErrorContainer* errors =
                      compileDesign->getCompiler()->getErrorContainer();
                  SymbolTable* symbols =
                      compileDesign->getCompiler()->getSymbolTable();
                  Location loc(symbols->registerSymbol(fileName), lineNumber, 0,
                               symbols->registerSymbol(name));
                  Error err(ErrorDefinition::COMP_UNDEFINED_USER_FUNCTION, loc);
                  errors->addError(err);
                }
                result = EvalFunc(any_cast<function*>(func), args, invalidValue,
                    (instance) ? actual_comp : component, compileDesign,
                    instance, fileName, lineNumber, pexpr);
              }
              if (result == nullptr || invalidValue == true) {
                fcall->Tf_call_args(args);
                result = fcall;
              }
            }
          } else {
            UHDM::sys_func_call* sys = s.MakeSys_func_call();
            sys->VpiName("$" + name);
            VectorOfany* arguments = compileTfCallArguments(
                component, fC, List_of_arguments, compileDesign, sys, instance,
                reduce, muteErrors);
            sys->Tf_call_args(arguments);
            result = sys;
          }
          break;
        }
        case VObjectType::slData_type:
          // When trying to evaluate type parameters
          return nullptr;
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
            if (UHDM::any* operand = compileExpression(
                    component, fC, fC->Sibling(parent), compileDesign, op,
                    instance, reduce, muteErrors)) {
              operands->push_back(operand);
            }
            op->Operands(operands);
            result = op;
          }
          break;
        }
        case VObjectType::slNull_keyword: {
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue("UINT:0");
          c->VpiDecompile("0");
          c->VpiSize(64);
          c->VpiConstType(vpiNullConst);
          result = c;
          break;
        }
        case VObjectType::slDollar_keyword: {
          UHDM::constant* c = s.MakeConstant();
          c->VpiConstType(vpiUnboundedConst);
          c->VpiValue("STRING:$");
          c->VpiDecompile("$");
          c->VpiSize(1);
          result = c;
          break;
        }
        case VObjectType::slThis_keyword: {
          // TODO: To be changed to class var
          UHDM::constant* c = s.MakeConstant();
          c->VpiConstType(vpiStringConst);
          c->VpiValue("STRING:this");
          c->VpiDecompile("this");
          c->VpiSize(4);
          result = c;
          break;
        }
        case VObjectType::slSuper_keyword: {
          // TODO: To be changed to class var
          UHDM::constant* c = s.MakeConstant();
          c->VpiConstType(vpiStringConst);
          c->VpiValue("STRING:super");
          c->VpiDecompile("super");
          c->VpiSize(5);
          result = c;
          break;
        }
        case VObjectType::slThis_dot_super: {
          // TODO: To be changed to class var
          UHDM::constant* c = s.MakeConstant();
          c->VpiConstType(vpiStringConst);
          c->VpiValue("STRING:this.super");
          c->VpiDecompile("this.super");
          c->VpiSize(10);
          result = c;
          break;
        }
        case VObjectType::slConstraint_block: {
          // Empty constraint block
          UHDM::constraint* cons = s.MakeConstraint();
          result = cons;
          break;
        }
        case VObjectType::slIntConst:
        case VObjectType::slRealConst:
        case VObjectType::slNumber_1Tickb1:
        case VObjectType::slNumber_1TickB1:
        case VObjectType::slInitVal_1Tickb1:
        case VObjectType::slInitVal_1TickB1:
        case VObjectType::slScalar_1Tickb1:
        case VObjectType::slScalar_1TickB1:
        case VObjectType::sl1:
        case VObjectType::slScalar_Tickb1:
        case VObjectType::slScalar_TickB1:
        case VObjectType::slNumber_Tickb1:
        case VObjectType::slNumber_TickB1:
        case VObjectType::slNumber_Tick1:
        case VObjectType::slNumber_1Tickb0:
        case VObjectType::slNumber_1TickB0:
        case VObjectType::slInitVal_1Tickb0:
        case VObjectType::slInitVal_1TickB0:
        case VObjectType::slScalar_1Tickb0:
        case VObjectType::slScalar_1TickB0:
        case VObjectType::sl0:
        case VObjectType::slScalar_Tickb0:
        case VObjectType::slScalar_TickB0:
        case VObjectType::slNumber_Tickb0:
        case VObjectType::slNumber_TickB0:
        case VObjectType::slNumber_Tick0:
        case VObjectType::slNumber_1TickBX:
        case VObjectType::slNumber_1TickbX:
        case VObjectType::slNumber_1Tickbx:
        case VObjectType::slNumber_1TickBx:
        case VObjectType::slInitVal_1Tickbx:
        case VObjectType::slInitVal_1TickbX:
        case VObjectType::slInitVal_1TickBx:
        case VObjectType::slInitVal_1TickBX:
        case VObjectType::slX:
        case VObjectType::slZ:
        case VObjectType::slTime_literal:
        case VObjectType::slStringLiteral: {
          result = compileConst(fC, parent, s);
          break;
        }
        case VObjectType::slStringConst:
        case VObjectType::slDollar_root_keyword: {
          std::string name = fC->SymName(parent).c_str();
          if (type == slDollar_root_keyword) {
            name = "$root";
          }
          NodeId dotedName = fC->Sibling(parent);
          bool hierPath = false;
          NodeId tmp = dotedName;
          while (tmp) {
            if (fC->Type(tmp) == slStringConst) {
              hierPath = true;
              break;
            }
            tmp = fC->Sibling(tmp);
          }
          if (!hierPath) {
            VObjectType dtype = fC->Type(dotedName);
            if (dotedName == 0) {
              ref_obj* ref = s.MakeRef_obj();
              ref->VpiName(name);
              ref->VpiFullName(name);
              result = ref;
            } else if (dtype == VObjectType::slSelect ||
                       dtype == VObjectType::slConstant_bit_select ||
                       dtype == VObjectType::slBit_select ||
                       dtype == VObjectType::slConstant_select) {
              std::string ind;
              NodeId Bit_select = fC->Child(dotedName);
              NodeId Expression = fC->Child(Bit_select);
              expr* index = nullptr;
              if (Expression)
                index = (expr*)compileExpression(
                    component, fC, Expression, compileDesign, pexpr, instance);
              if (index) {
                bit_select* select = s.MakeBit_select();
                select->VpiIndex(index);
                if (index->UhdmType() == uhdmconstant) {
                  ind = index->VpiDecompile();
                  name += "[" + ind + "]";
                } else if (index->UhdmType() == uhdmref_obj) {
                  ind = index->VpiName();
                  name += "[" + ind + "]";
                } else if (index->UhdmType() == uhdmoperation) {
                  ind = "...";
                  name += "[" + ind + "]";
                }
                select->VpiFullName(name);
                select->VpiName(name);
                result = select;
              } else {
                ref_obj* ref = s.MakeRef_obj();
                ref->VpiName(name);
                ref->VpiFullName(name);
                result = ref;
              }
            }
            break;
          }

          UHDM::hier_path* path = s.MakeHier_path();
          VectorOfany* elems = s.MakeAnyVec();
          std::string tmpName = name;
          path->Path_elems(elems);
          bool is_hierarchical = false;
          while (dotedName) {
            VObjectType dtype = fC->Type(dotedName);
            if (dtype == VObjectType::slStringConst) {
              name += "." + fC->SymName(dotedName);
              if (tmpName != "") {
                ref_obj* ref = s.MakeRef_obj();
                elems->push_back(ref);
                ref->VpiName(tmpName);
                ref->VpiFullName(tmpName);
                tmpName = "";
                is_hierarchical = true;
              }
              tmpName = fC->SymName(dotedName);
            } else if (dtype == VObjectType::slSelect ||
                       dtype == VObjectType::slBit_select ||
                       dtype == VObjectType::slConstant_bit_select ||
                       dtype == VObjectType::slConstant_expression) {
              std::string ind;
              NodeId Bit_select = fC->Child(dotedName);
              NodeId Expression = fC->Child(Bit_select);
              if (Expression == 0) {
                if (Bit_select) Expression = fC->Sibling(Bit_select);
              }
              if (dtype == VObjectType::slConstant_expression) {
                Expression = dotedName;
              }

              is_hierarchical = true;
              if (Expression && (fC->Type(Expression) == slPart_select_range) &&
                  fC->Child(Expression)) {
                expr* select = (expr*)compilePartSelectRange(
                    component, fC, fC->Child(Expression),
                    "CREATE_UNNAMED_PARENT", compileDesign, nullptr, instance,
                    reduce, muteErrors);
                ref_obj* parent = (ref_obj*)select->VpiParent();
                if (parent) parent->VpiDefName(tmpName);
                elems->push_back(select);
                if (part_select* pselect = any_cast<part_select*>(select)) {
                  std::string selectRange =
                      "[" + pselect->Left_range()->VpiDecompile() + ":" +
                      pselect->Right_range()->VpiDecompile() + "]";
                  name += selectRange;
                } else if (indexed_part_select* pselect =
                               any_cast<indexed_part_select*>(select)) {
                  std::string selectRange =
                      "[" + pselect->Base_expr()->VpiDecompile() +
                      ((pselect->VpiIndexedPartSelectType() == vpiPosIndexed)
                           ? "+"
                           : "-") +
                      std::string(":") + pselect->Width_expr()->VpiDecompile() +
                      "]";
                  name += selectRange;
                }
              } else if (Expression) {
                expr* index = (expr*)compileExpression(
                    component, fC, Expression, compileDesign, pexpr, instance,
                    reduce, muteErrors);
                if (index) {
                  bit_select* select = s.MakeBit_select();
                  elems->push_back(select);
                  select->VpiIndex(index);
                  select->VpiName(tmpName);
                  select->VpiFullName(tmpName);
                  if (index->UhdmType() == uhdmconstant) {
                    ind = index->VpiDecompile();
                    name += "[" + ind + "]";
                  } else if (index->UhdmType() == uhdmref_obj) {
                    ind = index->VpiName();
                    name += "[" + ind + "]";
                  } else if (index->UhdmType() == uhdmoperation) {
                    ind = "...";
                    name += "[" + ind + "]";
                  }
                }
              } else {
                ref_obj* ref = s.MakeRef_obj();
                elems->push_back(ref);
                ref->VpiName(tmpName);
                ref->VpiFullName(tmpName);
              }
              tmpName = "";
            }
            dotedName = fC->Sibling(dotedName);
          }
          if (is_hierarchical) {
            if (tmpName != "") {
              ref_obj* ref = s.MakeRef_obj();
              elems->push_back(ref);
              ref->VpiName(tmpName);
              ref->VpiFullName(tmpName);
              tmpName = "";
              result = path;
            }
          } else {
            ref_obj* ref = s.MakeRef_obj();
            ref->VpiName(tmpName);
            ref->VpiParent(pexpr);
            tmpName = "";
            result = ref;
            break;
          }

          path->VpiName(name);
          path->VpiFullName(name);
          path->VpiParent(pexpr);
          Value* sval = NULL;
          if (instance) sval = instance->getValue(name);
          if (sval == NULL) {
            NodeId op = fC->Sibling(parent);
            VObjectType opType = fC->Type(op);
            if (op && (opType != VObjectType::slStringConst) &&
                (opType != VObjectType::slExpression) &&
                (opType != VObjectType::slBit_select) &&
                (opType != VObjectType::slConstant_bit_select)) {
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
              path->VpiParent(pexpr);
              result = path;
            }
          } else {
            UHDM::constant* c = s.MakeConstant();
            c->VpiValue(sval->uhdmValue());
            c->VpiDecompile(sval->decompiledValue());
            c->VpiConstType(sval->vpiValType());
            c->VpiSize(sval->getSize());
            result = c;
          }
          break;
        }
        default:
          break;
      }
    }
  }

  NodeId the_node = 0;
  if (child) {
    the_node = child;
  } else {
    the_node = parent;
  }
  if ((result == nullptr) && (muteErrors == false)) {
    VObjectType exprtype = fC->Type(the_node);
    if ((exprtype != VObjectType::slEnd)) {
      ErrorContainer* errors =
          compileDesign->getCompiler()->getErrorContainer();
      SymbolTable* symbols = compileDesign->getCompiler()->getSymbolTable();
      unsupported_expr* exp = s.MakeUnsupported_expr();
      std::string fileContent = FileUtils::getFileContent(fC->getFileName());
      std::string lineText =
          StringUtils::getLineInString(fileContent, fC->Line(the_node));
      Location loc(
          symbols->registerSymbol(fC->getFileName(the_node)),
          fC->Line(the_node), 0,
          symbols->registerSymbol(std::string("<") + fC->printObject(the_node) +
                                  std::string("> ") + lineText));
      Error err(ErrorDefinition::UHDM_UNSUPPORTED_EXPR, loc);
      errors->addError(err);
      exp->VpiValue("STRING:" + lineText);
      exp->VpiFile(fC->getFileName(the_node));
      exp->VpiLineNo(fC->Line(the_node));
      exp->VpiColumnNo(fC->Column(the_node));
      exp->VpiEndLineNo(fC->EndLine(the_node));
      exp->VpiEndColumnNo(fC->EndColumn(the_node));
      exp->VpiParent(pexpr);
      result = exp;
    }
  }

  if ((result != nullptr) && reduce) {
    // Reduce
    bool invalidValue = false;
    any* tmp = reduceExpr(result, invalidValue, component, compileDesign,
                          instance, fC->getFileName(the_node),
                          fC->Line(the_node), pexpr, muteErrors);
    if (tmp && (invalidValue == false)) {
      result = tmp;
    }
    /*
    if (invalidValue) {
      // Can't reduce an expression
      ErrorContainer* errors =
          compileDesign->getCompiler()->getErrorContainer();
      SymbolTable* symbols = compileDesign->getCompiler()->getSymbolTable();
      std::string fileContent = FileUtils::getFileContent(fC->getFileName());
      std::string lineText =
          StringUtils::getLineInString(fileContent, fC->Line(the_node));
      Location loc(
          symbols->registerSymbol(fC->getFileName(the_node)),
          fC->Line(the_node), 0,
          symbols->registerSymbol(std::string("<") + fC->printObject(the_node) +
                                  std::string("> ") + lineText));
      Error err(ErrorDefinition::UHDM_UNSUPPORTED_EXPR, loc);
      errors->addError(err);
    }
    */
  }

  if (result) {
    if (child) {
      result->VpiFile(fC->getFileName(child));
      result->VpiLineNo(fC->Line(child));
      result->VpiColumnNo(fC->Column(child));
      result->VpiEndLineNo(fC->EndLine(child));
      result->VpiEndColumnNo(fC->EndColumn(child));
    } else {
      result->VpiFile(fC->getFileName(parent));
      result->VpiLineNo(fC->Line(parent));
      result->VpiColumnNo(fC->Column(parent));
      result->VpiEndLineNo(fC->EndLine(parent));
      result->VpiEndColumnNo(fC->EndColumn(parent));
    }
  }

  return result;
}

UHDM::any* CompileHelper::compileAssignmentPattern(DesignComponent* component,
                                                   const FileContent* fC,
                                                   NodeId Assignment_pattern,
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
  bool reduce = false;
  if (component && valuedcomponenti_cast<Package*>(component)) {
    reduce = true;
  }
  // Page 1035: For an operation of type vpiAssignmentPatternOp, the operand
  // iteration shall return the expressions as if the assignment pattern were
  // written with the positional notation. Nesting of assignment patterns shall
  // be preserved.

  // We forward the structure without reordering the bits or interpreting,
  // we deviate from the Standard by forwarding the complete spec to the client
  // and letting them do the reordering if need be.
  NodeId Structure_pattern_key = fC->Child(Assignment_pattern);
  bool with_key = true;
  if (fC->Type(Structure_pattern_key) == VObjectType::slExpression ||
      fC->Type(Structure_pattern_key) == VObjectType::slConstant_expression) {
    with_key = false;
  }
  if (!with_key && fC->Type(Structure_pattern_key) == slConstant_expression) {
    // '{2{1}}
    NodeId Expression = Structure_pattern_key;
    if (any* exp = compileExpression(component, fC, Expression, compileDesign,
                                     operation, instance, reduce, false)) {
      Structure_pattern_key = fC->Sibling(Structure_pattern_key);
      Expression = Structure_pattern_key;
      any* val = compileExpression(component, fC, Expression, compileDesign,
                                   operation, instance, reduce, false);

      operation->VpiOpType(vpiMultiAssignmentPatternOp);
      operands->push_back(exp);
      operands->push_back(val);
    }
    return result;
  }
  while (Structure_pattern_key) {
    NodeId Expression;
    if (!with_key) {
      Expression = Structure_pattern_key;
      if (Expression) {
        // No key '{1,2,...}
        if (any* exp =
                compileExpression(component, fC, Expression, compileDesign,
                                  operation, instance, reduce, false)) {
          operands->push_back(exp);
        }
      }
    } else {
      Expression =
          fC->Sibling(Structure_pattern_key);  // With key '{a: 1, b: 2,...}

      if (Expression) {
        if (any* exp =
                compileExpression(component, fC, Expression, compileDesign,
                                  operation, instance, reduce, false)) {
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
            tps->VpiColumnNo(fC->Column(Constant_expression));
            tps->VpiEndLineNo(fC->EndLine(Constant_expression));
            tps->VpiEndColumnNo(fC->EndColumn(Constant_expression));
            pattern->Typespec(tps);
          } else {
            NodeId Primary_literal = Constant_primary;
            if (fC->Type(Primary_literal) != slPrimary_literal)
              Primary_literal = fC->Child(Constant_primary);
            pattern->Typespec(compileTypespec(component, fC, Primary_literal,
                                              compileDesign, nullptr, instance,
                                              true));
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

bool CompileHelper::errorOnNegativeConstant(DesignComponent* component,
                                            Value* value,
                                            CompileDesign* compileDesign,
                                            ValuedComponentI* instance) {
  if (value == nullptr) return false;
  const std::string& val = value->uhdmValue();
  return errorOnNegativeConstant(component, val, compileDesign, instance, "", 0,
                                 0);
}

bool CompileHelper::errorOnNegativeConstant(DesignComponent* component,
                                            expr* exp,
                                            CompileDesign* compileDesign,
                                            ValuedComponentI* instance) {
  if (exp == nullptr) return false;
  if (exp->UhdmType() != uhdmconstant) return false;
  const std::string& val = exp->VpiValue();
  return errorOnNegativeConstant(component, val, compileDesign, instance,
                                 exp->VpiFile(), exp->VpiLineNo(),
                                 exp->VpiColumnNo());
}

bool CompileHelper::errorOnNegativeConstant(
    DesignComponent* component, const std::string& val,
    CompileDesign* compileDesign, ValuedComponentI* instance,
    const std::string& fileName, unsigned int lineNo, unsigned short columnNo) {
  if (val[4] == '-') {
    std::string instanceName;
    if (instance) {
      if (ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(instance)) {
        instanceName = inst->getFullPathName();
      }
    } else if (component) {
      instanceName = component->getName();
    }
    std::string message;
    message += "\"" + instanceName + "\"\n";
    std::string fileContent = FileUtils::getFileContent(fileName);
    std::string lineText = StringUtils::getLineInString(fileContent, lineNo);
    message += "             text: " + lineText;
    message += "             value: " + val;
    ErrorContainer* errors = compileDesign->getCompiler()->getErrorContainer();
    SymbolTable* symbols = compileDesign->getCompiler()->getSymbolTable();
    Location loc(symbols->registerSymbol(fileName), lineNo, columnNo,
                 symbols->registerSymbol(message));
    Error err(ErrorDefinition::ELAB_NEGATIVE_VALUE, loc);

    bool replay = false;
    // GDB: p replay=true
    if (replay) {
      if (instance) {
        ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(instance);
        while (inst) {
          std::cout << "Instance:" << inst->getFullPathName() << " "
                    << inst->getFileName() << "\n";
          std::cout << "Mod: " << inst->getModuleName() << " "
                    << component->getFileContents()[0]->getFileName() << "\n";

          for (auto ps : inst->getMappedValues()) {
            const std::string& name = ps.first;
            Value* val = ps.second.first;
            std::cout << std::string("    " + name + " = " + val->uhdmValue() +
                                     "\n");
          }
          for (auto ps : inst->getComplexValues()) {
            const std::string& name = ps.first;
            std::cout << std::string("    " + name + " =  complex\n");
          }
          if (inst->getNetlist() && inst->getNetlist()->param_assigns()) {
            for (auto ps : *inst->getNetlist()->param_assigns()) {
              std::cout << ps->Lhs()->VpiName() << " = "
                        << "\n";
              decompile((any*)ps->Rhs());
            }
          }
          inst = inst->getParent();
        }
      }
    }
    errors->addError(err);
    return true;
  }
  return false;
}

std::vector<UHDM::range*>* CompileHelper::compileRanges(
    DesignComponent* component, const FileContent* fC, NodeId Packed_dimension,
    CompileDesign* compileDesign, UHDM::any* pexpr, ValuedComponentI* instance,
    bool reduce, int& size, bool muteErrors) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  VectorOfrange* ranges = nullptr;
  size = 0;
  if (Packed_dimension &&
      ((fC->Type(Packed_dimension) == VObjectType::slPacked_dimension) ||
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
        UHDM::range* range = s.MakeRange();
        if (reduce) {
          Value* leftV = m_exprBuilder.evalExpr(fC, lexpr, instance, true);
          Value* rightV = m_exprBuilder.evalExpr(fC, rexpr, instance, true);
          uint64_t lint = 0;
          uint64_t rint = 0;
          if (leftV->isValid()) {
            lint = leftV->getValueUL();
          }
          if (rightV->isValid()) {
            rint = rightV->getValueUL();
          }
          uint64_t tmp = (lint > rint) ? lint - rint + 1 : rint - lint + 1;
          size = size * tmp;
        }

        expr* lexp = any_cast<expr*>(
            compileExpression(component, fC, lexpr, compileDesign, pexpr,
                              instance, reduce, muteErrors));
        if (reduce) {
          if (errorOnNegativeConstant(component, lexp, compileDesign,
                                      instance)) {
            bool replay = false;
            // GDB: p replay=true
            if (replay) {
              compileExpression(component, fC, lexpr, compileDesign, pexpr,
                                instance, reduce, muteErrors);
            }
          }
        }
        range->Left_expr(lexp);
        if (lexp) lexp->VpiParent(range);
        expr* rexp = any_cast<expr*>(
            compileExpression(component, fC, rexpr, compileDesign, pexpr,
                              instance, reduce, muteErrors));
        if (reduce) {
          if (errorOnNegativeConstant(component, rexp, compileDesign,
                                      instance)) {
            bool replay = false;
            // GDB: p replay=true
            if (replay) {
              compileExpression(component, fC, rexpr, compileDesign, pexpr,
                                instance, reduce, muteErrors);
            }
          }
        }
        if (rexp) rexp->VpiParent(range);
        range->Right_expr(rexp);
        range->VpiFile(fC->getFileName());
        range->VpiLineNo(fC->Line(Constant_range));
        range->VpiColumnNo(fC->Column(Constant_range));
        range->VpiEndLineNo(fC->EndLine(Constant_range));
        range->VpiEndColumnNo(fC->EndColumn(Constant_range));
        ranges->push_back(range);
        range->VpiParent(pexpr);
      } else if (fC->Type(Constant_range) ==
                 VObjectType::slConstant_expression) {
        // Specified by size
        NodeId rexpr = Constant_range;
        UHDM::range* range = s.MakeRange();

        constant* lexpc = s.MakeConstant();
        lexpc->VpiConstType(vpiUIntConst);
        lexpc->VpiSize(64);
        lexpc->VpiValue("UINT:0");
        lexpc->VpiDecompile("0");
        lexpc->VpiFile(fC->getFileName());
        lexpc->VpiLineNo(fC->Line(rexpr));
        lexpc->VpiColumnNo(fC->Column(rexpr));
        lexpc->VpiEndLineNo(fC->EndLine(rexpr));
        lexpc->VpiEndColumnNo(fC->Column(rexpr) + 1);
        expr* lexp = lexpc;

        range->Left_expr(lexp);
        lexp->VpiParent(range);

        if (reduce) {
          Value* rightV = m_exprBuilder.evalExpr(fC, rexpr, instance, true);
          if (rightV->isValid()) {
            int64_t rint = rightV->getValueL();
            size = size * rint;
          }
        }

        expr* rexp = any_cast<expr*>(
            compileExpression(component, fC, rexpr, compileDesign, pexpr,
                              instance, reduce, muteErrors));
        bool associativeArray = false;
        if (rexp && rexp->UhdmType() == uhdmconstant) {
          constant* c = (constant*)rexp;
          if (c->VpiConstType() == vpiUnboundedConst) associativeArray = true;
        }
        if (!associativeArray) {
          operation* op = s.MakeOperation();  // Decr by 1
          op->VpiOpType(vpiSubOp);
          op->Operands(s.MakeAnyVec());
          op->Operands()->push_back(rexp);
          constant* one = s.MakeConstant();
          one->VpiValue("INT:1");
          one->VpiConstType(vpiIntConst);
          one->VpiSize(64);
          op->Operands()->push_back(one);
          rexp = op;
        }

        if (rexp) rexp->VpiParent(range);
        range->Right_expr(rexp);
        range->VpiFile(fC->getFileName());
        range->VpiLineNo(fC->Line(Constant_range));
        range->VpiColumnNo(fC->Column(Constant_range));
        range->VpiEndLineNo(fC->EndLine(Constant_range));
        range->VpiEndColumnNo(fC->EndColumn(Constant_range));
        ranges->push_back(range);
        range->VpiParent(pexpr);
      } else if (fC->Type(fC->Child(Packed_dimension)) ==
                 VObjectType::slUnsized_dimension) {
        return nullptr;
      }
      Packed_dimension = fC->Sibling(Packed_dimension);
    }
  }
  return ranges;
}

UHDM::any* CompileHelper::compilePartSelectRange(
    DesignComponent* component, const FileContent* fC, NodeId Constant_range,
    const std::string& name, CompileDesign* compileDesign, UHDM::any* pexpr,
    ValuedComponentI* instance, bool reduce, bool muteErrors) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  if (fC->Type(Constant_range) == VObjectType::slConstant_range) {
    NodeId Constant_expression = fC->Child(Constant_range);
    UHDM::expr* lexp = (expr*)compileExpression(
        component, fC, Constant_expression, compileDesign, pexpr, instance);
    UHDM::expr* rexp = (expr*)compileExpression(
        component, fC, fC->Sibling(Constant_expression), compileDesign, pexpr,
        instance);
    UHDM::part_select* part_select = s.MakePart_select();
    part_select->Left_range(lexp);
    part_select->Right_range(rexp);
    if (name == "CREATE_UNNAMED_PARENT") {
      UHDM::ref_obj* ref = s.MakeRef_obj();
      part_select->VpiParent(ref);
    } else if (!name.empty()) {
      UHDM::ref_obj* ref = s.MakeRef_obj();
      ref->VpiName(name);
      ref->VpiDefName(name);
      part_select->VpiParent(ref);
    }
    part_select->VpiConstantSelect(true);
    result = part_select;
  } else {
    // constant_indexed_range
    NodeId Constant_expression = fC->Child(Constant_range);
    UHDM::expr* lexp = (expr*)compileExpression(
        component, fC, Constant_expression, compileDesign, pexpr, instance,
        reduce, muteErrors);
    NodeId op = fC->Sibling(Constant_expression);
    UHDM::expr* rexp =
        (expr*)compileExpression(component, fC, fC->Sibling(op), compileDesign,
                                 pexpr, instance, reduce, muteErrors);
    bool reduced = false;
    if (reduce && (lexp->UhdmType() == uhdmconstant) &&
        (rexp->UhdmType() == uhdmconstant)) {
      if (!name.empty()) {
        any* v = getValue(name, component, compileDesign, instance,
                          fC->getFileName(), fC->Line(Constant_expression),
                          pexpr, reduce, muteErrors);
        if (v && (v->UhdmType() == uhdmconstant)) {
          constant* cv = (constant*)v;
          Value* cvv =
              m_exprBuilder.fromVpiValue(cv->VpiValue(), cv->VpiSize());
          Value* left =
              m_exprBuilder.fromVpiValue(lexp->VpiValue(), lexp->VpiSize());
          Value* range =
              m_exprBuilder.fromVpiValue(rexp->VpiValue(), rexp->VpiSize());
          uint64_t l = left->getValueUL();
          uint64_t r = range->getValueUL();
          uint64_t res = 0;
          if ((cvv->getType() == Value::Type::Hexadecimal) &&
              (cvv->getSize() >
               64 /* hex val stored as string above 64 bits */)) {
            std::string val = cvv->getValueS();
            std::string part;
            if (fC->Type(op) == VObjectType::slIncPartSelectOp) {
              int steps = r / 4;
              l = l / 4;
              for (unsigned int i = l; i < l + steps; i++) {
                part += val[val.size() - 1 - i];
              }
            } else {
              int steps = r / 4;
              l = l / 4;
              for (unsigned int i = l; i > l - steps; i--) {
                part += val[val.size() - 1 - i];
              }
            }
            res = std::strtoull(part.c_str(), 0, 16);
          } else {
            uint64_t iv = cvv->getValueUL();
            uint64_t mask = 0;
            if (fC->Type(op) == VObjectType::slIncPartSelectOp) {
              for (uint64_t i = l; i > uint64_t(l - r); i--) {
                mask |= ((uint64_t)1 << i);
              }
              res = iv & mask;
              res = res >> (l - r);
            } else {
              for (uint64_t i = l; i < uint64_t(l + r); i++) {
                mask |= ((uint64_t)1 << i);
              }
              res = iv & mask;
              res = res >> l;
            }
          }

          std::string sval = "UINT:" + std::to_string(res);
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue(sval);
          c->VpiDecompile(std::to_string(res));
          c->VpiSize(r);
          c->VpiConstType(vpiUIntConst);
          result = c;
          reduced = true;
        }
      }
    }

    if (!reduced) {
      UHDM::indexed_part_select* part_select = s.MakeIndexed_part_select();
      part_select->Base_expr(lexp);
      part_select->Width_expr(rexp);
      if (fC->Type(op) == VObjectType::slIncPartSelectOp)
        part_select->VpiIndexedPartSelectType(vpiPosIndexed);
      else
        part_select->VpiIndexedPartSelectType(vpiNegIndexed);
      if (name == "CREATE_UNNAMED_PARENT") {
        UHDM::ref_obj* ref = s.MakeRef_obj();
        part_select->VpiParent(ref);
      } else if (!name.empty()) {
        UHDM::ref_obj* ref = s.MakeRef_obj();
        ref->VpiName(name);
        ref->VpiDefName(name);
        part_select->VpiParent(ref);
      }
      part_select->VpiConstantSelect(true);
      result = part_select;
    }
  }
  return result;
}

uint64_t CompileHelper::Bits(const UHDM::any* typespec, bool& invalidValue,
                             DesignComponent* component,
                             CompileDesign* compileDesign,
                             ValuedComponentI* instance,
                             const std::string& fileName, int lineNumber,
                             bool reduce, bool sizeMode) {
  uint64_t bits = 0;
  if (typespec) {
    const UHDM::typespec* tps = any_cast<const UHDM::typespec*>(typespec);
    if (tps) {
      if (const UHDM::instance* inst = tps->Instance()) {
        if (Package* pack =
                compileDesign->getCompiler()->getDesign()->getPackage(
                    inst->VpiName())) {
          component = pack;
        }
      }
    }
  }
  UHDM::VectorOfrange* ranges = nullptr;
  if (typespec) {
    UHDM_OBJECT_TYPE ttps = typespec->UhdmType();
    switch (ttps) {
      case UHDM::uhdmhier_path: {
        typespec = decodeHierPath((hier_path*)typespec, invalidValue, component,
                                  compileDesign, instance, fileName, lineNumber,
                                  nullptr, true, true);
        bits = Bits(typespec, invalidValue, component, compileDesign, instance,
                    fileName, lineNumber, reduce, sizeMode);
        break;
      }
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
        integer_typespec* itps = (integer_typespec*)typespec;
        if (strstr(itps->VpiValue().c_str(), "UINT:")) {
          bits =
              std::strtoull(itps->VpiValue().c_str() + strlen("UINT:"), 0, 10);
        } else {
          bits = std::strtoll(itps->VpiValue().c_str() + strlen("INT:"), 0, 10);
        }
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
      case UHDM::uhdmlogic_net: {
        bits = 1;
        UHDM::logic_net* lts = (UHDM::logic_net*)typespec;
        ranges = lts->Ranges();
        break;
      }
      case UHDM::uhdmlogic_var: {
        bits = 1;
        UHDM::logic_var* lts = (UHDM::logic_var*)typespec;
        ranges = lts->Ranges();
        break;
      }
      case UHDM::uhdmbit_var: {
        bits = 1;
        UHDM::bit_var* lts = (UHDM::bit_var*)typespec;
        ranges = lts->Ranges();
        break;
      }
      case UHDM::uhdmbyte_var: {
        bits = 8;
        break;
      }
      case UHDM::uhdmstruct_var: {
        const UHDM::typespec* tp = ((struct_var*)typespec)->Typespec();
        bits += Bits(tp, invalidValue, component, compileDesign, instance,
                     fileName, lineNumber, reduce, sizeMode);
        break;
      }
      case UHDM::uhdmstruct_net: {
        const UHDM::typespec* tp = ((struct_net*)typespec)->Typespec();
        bits += Bits(tp, invalidValue, component, compileDesign, instance,
                     fileName, lineNumber, reduce, sizeMode);
        break;
      }
      case UHDM::uhdmstruct_typespec: {
        UHDM::struct_typespec* sts = (UHDM::struct_typespec*)typespec;
        UHDM::VectorOftypespec_member* members = sts->Members();
        if (members) {
          for (UHDM::typespec_member* member : *members) {
            bits +=
                Bits(member->Typespec(), invalidValue, component, compileDesign,
                     instance, fileName, lineNumber, reduce, sizeMode);
          }
        }
        break;
      }
      case UHDM::uhdmenum_typespec: {
        const UHDM::enum_typespec* sts =
            any_cast<const UHDM::enum_typespec*>(typespec);
        if (sts)
          bits =
              Bits(sts->Base_typespec(), invalidValue, component, compileDesign,
                   instance, fileName, lineNumber, reduce, sizeMode);
        break;
      }
      case UHDM::uhdmunion_typespec: {
        UHDM::union_typespec* sts = (UHDM::union_typespec*)typespec;
        UHDM::VectorOftypespec_member* members = sts->Members();
        if (members) {
          for (UHDM::typespec_member* member : *members) {
            unsigned int max =
                Bits(member->Typespec(), invalidValue, component, compileDesign,
                     instance, fileName, lineNumber, reduce, sizeMode);
            if (max > bits) bits = max;
          }
        }
        break;
      }
      case uhdmunsupported_typespec:
        invalidValue = true;
        break;
      case uhdmconstant: {
        constant* c = (constant*)typespec;
        bits = c->VpiSize();
        break;
      }
      case uhdmref_obj: {
        ref_obj* ref = (ref_obj*)typespec;
        if (const any* act = ref->Actual_group()) {
          bits = Bits(act, invalidValue, component, compileDesign, instance,
                      fileName, lineNumber, reduce, sizeMode);
        } else {
          any* object = getObject(ref->VpiName(), component, compileDesign,
                                  instance, nullptr);
          if (object == nullptr) {
            object =
                getValue(ref->VpiName(), component, compileDesign, instance,
                         fileName, lineNumber, nullptr, true, true);
          }
          if (object) {
            // Substitution
            if (param_assign* pass = any_cast<param_assign*>(object)) {
              const any* rhs = pass->Rhs();
              object =
                  reduceExpr((any*)rhs, invalidValue, component, compileDesign,
                             instance, fileName, lineNumber, nullptr, true);
            } else if (bit_select* bts = any_cast<bit_select*>(object)) {
              object =
                  reduceExpr((any*)bts, invalidValue, component, compileDesign,
                             instance, fileName, lineNumber, nullptr, true);
            }
            bits = Bits(object, invalidValue, component, compileDesign,
                        instance, fileName, lineNumber, reduce, sizeMode);
          } else {
            invalidValue = true;
          }
        }
        break;
      }
      case uhdmoperation: {
        operation* op = (operation*)typespec;
        if (op->VpiOpType() == vpiConcatOp) {
          if (auto ops = op->Operands()) {
            for (auto op : *ops) {
              bits += Bits(op, invalidValue, component, compileDesign, instance,
                           fileName, lineNumber, reduce, sizeMode);
            }
          }
        } else {
          invalidValue = true;
        }
        break;
      }
      case uhdmpacked_array_typespec: {
        packed_array_typespec* tmp = (packed_array_typespec*)typespec;
        const UHDM::typespec* tps = (UHDM::typespec*)tmp->Elem_typespec();
        bits += Bits(tps, invalidValue, component, compileDesign, instance,
                     fileName, lineNumber, reduce, sizeMode);
        ranges = tmp->Ranges();
        break;
      }
      default:
        invalidValue = true;
        break;
    }
  }
  if (ranges) {
    if (sizeMode) {
      UHDM::range* last_range = nullptr;
      for (UHDM::range* ran : *ranges) {
        last_range = ran;
      }
      expr* lexpr = (expr*)last_range->Left_expr();
      expr* rexpr = (expr*)last_range->Right_expr();
      int64_t lv =
          get_value(invalidValue,
                    reduceExpr(lexpr, invalidValue, component, compileDesign,
                               instance, fileName, lineNumber, nullptr));
      int64_t rv =
          get_value(invalidValue,
                    reduceExpr(rexpr, invalidValue, component, compileDesign,
                               instance, fileName, lineNumber, nullptr));
      if (lv > rv)
        bits = bits * (lv - rv + 1);
      else
        bits = bits * (rv - lv + 1);
    } else {
      for (UHDM::range* ran : *ranges) {
        expr* lexpr = (expr*)ran->Left_expr();
        expr* rexpr = (expr*)ran->Right_expr();
        int64_t lv =
            get_value(invalidValue,
                      reduceExpr(lexpr, invalidValue, component, compileDesign,
                                 instance, fileName, lineNumber, nullptr));
        int64_t rv =
            get_value(invalidValue,
                      reduceExpr(rexpr, invalidValue, component, compileDesign,
                                 instance, fileName, lineNumber, nullptr));

        if (lv > rv)
          bits = bits * (lv - rv + 1);
        else
          bits = bits * (rv - lv + 1);
      }
    }
  }
  return bits;
}

const typespec* getMemberTypespec(const typespec* tpss,
                                  const std::vector<std::string>& suffixes,
                                  uint32_t index) {
  const typespec* result = nullptr;
  if (tpss->UhdmType() == uhdmstruct_typespec) {
    const struct_typespec* ts = (const struct_typespec*)tpss;
    for (typespec_member* memb : *ts->Members()) {
      if (memb->VpiName() == suffixes[index]) {
        result = memb->Typespec();
        if (index < (suffixes.size() - 1)) {
          if (result->UhdmType() == uhdmstruct_typespec) {
            result = getMemberTypespec(result, suffixes, index + 1);
          }
        }
        break;
      }
    }
  }
  return result;
}

const typespec* CompileHelper::getTypespec(DesignComponent* component,
                                           const FileContent* fC, NodeId id,
                                           CompileDesign* compileDesign,
                                           ValuedComponentI* instance,
                                           bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  const DataType* dtype = nullptr;
  const typespec* result = nullptr;
  std::string basename;
  std::vector<std::string> suffixnames;
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
      while (suffix && (fC->Type(suffix) == slStringConst)) {
        suffixnames.push_back(fC->SymName(suffix));
        suffix = fC->Sibling(suffix);
      }
      break;
    }
    case VObjectType::slIntVec_TypeLogic: {
      result = s.MakeLogic_typespec();
      break;
    }
    case VObjectType::slIntVec_TypeBit: {
      result = s.MakeBit_typespec();
      break;
    }
    case VObjectType::slIntVec_TypeReg: {
      result = s.MakeLogic_typespec();
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
      } else {
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
    if (component) dtype = component->getDataType(basename);
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
        result =
            compileTypespec(component, fC, sig->getTypeSpecId(), compileDesign,
                            nullptr, instance, reduce, true);
      } else {
        NodeId Packed_dimension = sig->getPackedDimension();
        if (fC->Type(Packed_dimension) != VObjectType::slNull_rule) {
          NodeId DataType = fC->Parent(Packed_dimension);
          result = compileTypespec(component, fC, DataType, compileDesign,
                                   nullptr, instance, reduce);
        }
      }
    }
  }
  while (dtype) {
    const TypeDef* typed = datatype_cast<const TypeDef*>(dtype);
    if (typed) {
      const DataType* dt = typed->getDataType();
      const Enum* en = datatype_cast<const Enum*>(dt);
      if (en) {
        result = en->getTypespec();
        break;
      }
      const Struct* st = datatype_cast<const Struct*>(dt);
      if (st) {
        result = st->getTypespec();
        if (!suffixnames.empty()) {
          result = getMemberTypespec(result, suffixnames, 0);
        }
        break;
      }
      const Union* un = datatype_cast<const Union*>(dt);
      if (un) {
        result = un->getTypespec();
        break;
      }
      const SimpleType* sit = datatype_cast<const SimpleType*>(dt);
      if (sit) {
        result = sit->getTypespec();
        break;
      }
    }
    dtype = dtype->getDefinition();
  }

  if (result == nullptr) {
    ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(instance);
    if (inst) {
      Netlist* netlist = inst->getNetlist();
      if (netlist) {
        if (netlist->ports()) {
          for (port* p : *netlist->ports()) {
            if (p->VpiName() == basename) {
              const typespec* tps = p->Typespec();
              if (!suffixnames.empty()) {
                result = getMemberTypespec(tps, suffixnames, 0);
              }
            }
            if (result) break;
          }
        }
      }
    }
  } else {
    if (!suffixnames.empty()) {
      result = getMemberTypespec(result, suffixnames, 0);
    }
  }
  return result;
}

UHDM::any* CompileHelper::compileBits(
    DesignComponent* component, const FileContent* fC, NodeId List_of_arguments,
    CompileDesign* compileDesign, UHDM::any* pexpr, ValuedComponentI* instance,
    bool reduce, bool sizeMode, bool muteErrors) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  NodeId Expression = List_of_arguments;
  if (fC->Type(Expression) == slList_of_arguments) {
    Expression = fC->Child(Expression);
  } else if (fC->Type(Expression) == slData_type) {
    Expression = fC->Child(Expression);
  }
  NodeId typeSpecId = 0;
  uint64_t bits = 0;
  bool invalidValue = false;
  const typespec* tps = nullptr;
  const any* exp = nullptr;
  switch (fC->Type(Expression)) {
    case slIntegerAtomType_Byte:
    case slIntegerAtomType_Int:
    case slIntegerAtomType_LongInt:
    case slIntegerAtomType_Shortint:
    case slIntegerAtomType_Time:
    case slIntVec_TypeLogic:
    case slIntVec_TypeBit:
    case slIntVec_TypeReg:
      typeSpecId = Expression;
      break;
    default: {
      NodeId Primary = fC->Child(Expression);
      NodeId Primary_literal = fC->Child(Primary);
      if (fC->Type(Primary_literal) == slConcatenation) {
        NodeId ConcatExpression = fC->Child(Primary_literal);
        while (ConcatExpression) {
          NodeId Primary = fC->Child(ConcatExpression);
          NodeId Primary_literal = fC->Child(Primary);
          NodeId StringConst = fC->Child(Primary_literal);
          typeSpecId = StringConst;
          tps = getTypespec(component, fC, typeSpecId, compileDesign, instance,
                            reduce);
          if (!reduce && tps) {
            UHDM::ExprEval eval;
            if (eval.isFullySpecified(tps)) {
              reduce = true;
            }
          }
          if (reduce && tps)
            bits += Bits(tps, invalidValue, component, compileDesign, instance,
                         fC->getFileName(typeSpecId), fC->Line(typeSpecId),
                         reduce, sizeMode);
          ConcatExpression = fC->Sibling(ConcatExpression);
        }
      } else {
        NodeId StringConst = fC->Child(Primary_literal);
        typeSpecId = StringConst;
      }
    }
  }

  if (bits == 0) {
    tps =
        getTypespec(component, fC, typeSpecId, compileDesign, instance, reduce);
    if (!reduce && tps) {
      UHDM::ExprEval eval;
      if (eval.isFullySpecified(tps)) {
        reduce = true;
      }
    }
    if (reduce && tps)
      bits = Bits(tps, invalidValue, component, compileDesign, instance,
                  fC->getFileName(typeSpecId), fC->Line(typeSpecId), reduce,
                  sizeMode);

    if (reduce && (!tps)) {
      exp = compileExpression(component, fC, Expression, compileDesign, nullptr,
                              instance, true, true);
      if (exp) {
        bits = Bits(exp, invalidValue, component, compileDesign, instance,
                    fC->getFileName(typeSpecId), fC->Line(typeSpecId), reduce,
                    sizeMode);
      }
    }
  }

  if (reduce && tps && (!invalidValue)) {
    UHDM::constant* c = s.MakeConstant();
    c->VpiValue("UINT:" + std::to_string(bits));
    c->VpiDecompile(std::to_string(bits));
    c->VpiConstType(vpiUIntConst);
    c->VpiSize(64);
    result = c;
  } else if (reduce && exp && (!invalidValue)) {
    UHDM::constant* c = s.MakeConstant();
    c->VpiValue("UINT:" + std::to_string(bits));
    c->VpiDecompile(std::to_string(bits));
    c->VpiConstType(vpiUIntConst);
    c->VpiSize(64);
    result = c;
  } else if (sizeMode) {
    UHDM::sys_func_call* sys = s.MakeSys_func_call();
    sys->VpiName("$size");
    VectorOfany* arguments =
        compileTfCallArguments(component, fC, List_of_arguments, compileDesign,
                               sys, instance, reduce, muteErrors);
    sys->Tf_call_args(arguments);
    result = sys;
  } else {
    UHDM::sys_func_call* sys = s.MakeSys_func_call();
    sys->VpiName("$bits");
    VectorOfany* arguments =
        compileTfCallArguments(component, fC, List_of_arguments, compileDesign,
                               sys, instance, reduce, muteErrors);
    sys->Tf_call_args(arguments);
    result = sys;
  }

  return result;
}

UHDM::any* CompileHelper::compileTypename(
    DesignComponent* component, const FileContent* fC, NodeId Expression,
    CompileDesign* compileDesign, UHDM::any* pexpr, ValuedComponentI* instance,
    bool reduce) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  UHDM::constant* c = s.MakeConstant();
  if (fC->Type(Expression) == slData_type) Expression = fC->Child(Expression);
  VObjectType type = fC->Type(Expression);
  switch (type) {
    case slIntVec_TypeLogic:
      c->VpiValue("STRING:logic");
      c->VpiDecompile("logic");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case slIntVec_TypeBit:
      c->VpiValue("STRING:bit");
      c->VpiDecompile("bit");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case slIntVec_TypeReg:
      c->VpiValue("STRING:reg");
      c->VpiDecompile("reg");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case slIntegerAtomType_Byte:
      c->VpiValue("STRING:byte");
      c->VpiDecompile("byte");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case slIntegerAtomType_Shortint:
      c->VpiValue("STRING:shortint");
      c->VpiDecompile("shortint");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case slIntegerAtomType_Int:
      c->VpiValue("STRING:int");
      c->VpiDecompile("int");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case slIntegerAtomType_LongInt:
      c->VpiValue("STRING:longint");
      c->VpiDecompile("longint");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case slIntegerAtomType_Time:
      c->VpiValue("STRING:time");
      c->VpiDecompile("time");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case slNonIntType_ShortReal:
      c->VpiValue("STRING:shortreal");
      c->VpiDecompile("shortreal");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case slNonIntType_Real:
      c->VpiValue("STRING:real");
      c->VpiDecompile("real");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case slNonIntType_RealTime:
      c->VpiValue("STRING:realtime");
      c->VpiDecompile("realtime");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    default:
      UHDM::sys_func_call* sys = s.MakeSys_func_call();
      sys->VpiName("$typename");
      result = sys;
      const std::string& arg = fC->SymName(Expression);
      c->VpiValue("STRING:" + arg);
      c->VpiDecompile(arg);
      c->VpiConstType(vpiStringConst);
      break;
  }
  return result;
}

UHDM::any* CompileHelper::compileClog2(
    DesignComponent* component, const FileContent* fC, NodeId List_of_arguments,
    CompileDesign* compileDesign, UHDM::any* pexpr, ValuedComponentI* instance,
    bool reduce, bool muteErrors) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  NodeId Expression = List_of_arguments;
  if (fC->Type(Expression) == slList_of_arguments) {
    Expression = fC->Child(Expression);
  }
  expr* operand =
      (expr*)compileExpression(component, fC, Expression, compileDesign, pexpr,
                               instance, reduce, muteErrors);
  bool invalidValue = false;
  int64_t val = 0;
  if (reduce)
    val = get_value(
        invalidValue,
        reduceExpr(operand, invalidValue, component, compileDesign, instance,
                   fC->getFileName(), fC->Line(Expression), pexpr, muteErrors));
  if (reduce && (invalidValue == false)) {
    val = val - 1;
    uint64_t clog2 = 0;
    for (; val > 0; clog2 = clog2 + 1) {
      val = val >> 1;
    }
    UHDM::constant* c = s.MakeConstant();
    c->VpiValue("UINT:" + std::to_string(clog2));
    c->VpiDecompile(std::to_string(clog2));
    c->VpiConstType(vpiUIntConst);
    c->VpiSize(64);
    result = c;
  } else {
    UHDM::sys_func_call* sys = s.MakeSys_func_call();
    sys->VpiName("$clog2");
    VectorOfany* arguments =
        compileTfCallArguments(component, fC, List_of_arguments, compileDesign,
                               sys, instance, reduce, muteErrors);
    sys->Tf_call_args(arguments);
    result = sys;
  }
  return result;
}

UHDM::any* CompileHelper::compileComplexFuncCall(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, UHDM::any* pexpr, ValuedComponentI* instance,
    bool reduce, bool muteErrors) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::any* result = nullptr;
  NodeId name = fC->Child(nodeId);
  NodeId dotedName = fC->Sibling(name);
  if (fC->Type(name) == VObjectType::slDollar_root_keyword) {
    hier_path* path = s.MakeHier_path();
    VectorOfany* elems = s.MakeAnyVec();
    path->Path_elems(elems);
    NodeId Dollar_root_keyword = name;
    NodeId nameId = fC->Sibling(Dollar_root_keyword);
    ref_obj* ref = s.MakeRef_obj();
    elems->push_back(ref);
    ref->VpiName("$root");
    ref->VpiFullName("$root");
    std::string name = "$root." + fC->SymName(nameId);
    ref = s.MakeRef_obj();
    elems->push_back(ref);
    ref->VpiName(fC->SymName(nameId));
    ref->VpiFullName(fC->SymName(nameId));
    nameId = fC->Sibling(nameId);
    while (nameId) {
      if (fC->Type(nameId) == slStringConst) {
        name += "." + fC->SymName(nameId);
        ref = s.MakeRef_obj();
        elems->push_back(ref);
        ref->VpiName(fC->SymName(nameId));
        ref->VpiFullName(fC->SymName(nameId));
      } else if (fC->Type(nameId) == slConstant_expression) {
        NodeId Constant_expresion = fC->Child(nameId);
        if (Constant_expresion) {
          name += "[";
          expr* select = (expr*)compileExpression(
              component, fC, Constant_expresion, compileDesign, pexpr, instance,
              reduce, muteErrors);
          name += select->VpiDecompile();
          name += "]";
          bit_select* sel = s.MakeBit_select();
          sel->VpiIndex(select);
          elems->push_back(sel);
        }
      } else {
        break;
      }
      nameId = fC->Sibling(nameId);
    }
    path->VpiName(name);
    result = path;
  } else if (fC->Type(name) == VObjectType::slDollar_keyword) {
    NodeId Dollar_keyword = name;
    NodeId nameId = fC->Sibling(Dollar_keyword);
    const std::string& name = fC->SymName(nameId);
    if (name == "bits") {
      NodeId List_of_arguments = fC->Sibling(nameId);
      result = compileBits(component, fC, List_of_arguments, compileDesign,
                           pexpr, instance, reduce, false, muteErrors);
    } else if (name == "size") {
      NodeId List_of_arguments = fC->Sibling(nameId);
      result = compileBits(component, fC, List_of_arguments, compileDesign,
                           pexpr, instance, reduce, true, muteErrors);
    } else if (name == "clog2") {
      NodeId List_of_arguments = fC->Sibling(nameId);
      result = compileClog2(component, fC, List_of_arguments, compileDesign,
                            pexpr, instance, reduce, muteErrors);
    } else {
      NodeId List_of_arguments = fC->Sibling(nameId);
      UHDM::sys_func_call* sys = s.MakeSys_func_call();
      sys->VpiName("$" + name);
      VectorOfany* arguments = compileTfCallArguments(
          component, fC, List_of_arguments, compileDesign, sys, instance,
          reduce, muteErrors);
      sys->Tf_call_args(arguments);
      result = sys;
    }
  } else if (fC->Type(name) == VObjectType::slImplicit_class_handle) {
    NodeId Handle = fC->Child(name);
    NodeId Method = fC->Sibling(name);
    if (Method == 0) {
      return compileExpression(component, fC, Handle, compileDesign, pexpr,
                               instance, reduce, muteErrors);
    }
    const std::string& name = fC->SymName(Method);
    NodeId List_of_arguments = fC->Sibling(Method);
    if (fC->Type(List_of_arguments) == slList_of_arguments) {
      method_func_call* fcall = s.MakeMethod_func_call();
      expr* object =
          (expr*)compileExpression(component, fC, Handle, compileDesign, pexpr,
                                   instance, reduce, muteErrors);
      fcall->Prefix(object);
      fcall->VpiName(name);
      VectorOfany* arguments = compileTfCallArguments(
          component, fC, List_of_arguments, compileDesign, fcall, instance,
          reduce, muteErrors);
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
                                       compileDesign, pexpr, instance, reduce,
                                       muteErrors);
      if (result == nullptr) {
        // TODO: this is a mockup
        constant* cvar = s.MakeConstant();
        cvar->VpiDecompile("this");
        result = cvar;
      }
    } else if (fC->Type(List_of_arguments) == slConstant_bit_select) {
      // TODO: Fill this
      method_func_call* fcall = s.MakeMethod_func_call();
      expr* object =
          (expr*)compileExpression(component, fC, Handle, compileDesign, pexpr,
                                   instance, reduce, muteErrors);
      VectorOfany* arguments = compileTfCallArguments(
          component, fC, fC->Sibling(fC->Sibling(List_of_arguments)),
          compileDesign, fcall, instance, reduce, muteErrors);
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
    NodeId Bit_Select = 0;
    if (List_of_arguments) {
      if (fC->Type(List_of_arguments) == slSelect) {
        Bit_Select = fC->Child(List_of_arguments);
        if (fC->Child(Bit_Select) == 0) {
          List_of_arguments = 0;
        }
      }
    }

    std::string packagename = fC->SymName(Class_type_name);
    std::string functionname = fC->SymName(Class_scope_name);
    std::string basename = packagename + "::" + functionname;
    tf_call* call = nullptr;
    std::pair<task_func*, DesignComponent*> ret =
        getTaskFunc(basename, component, compileDesign, pexpr);
    task_func* tf = ret.first;
    if (tf) {
      if (tf->UhdmType() == uhdmfunction) {
        func_call* fcall = s.MakeFunc_call();
        fcall->Function(any_cast<function*>(tf));
        call = fcall;
      } else {
        task_call* tcall = s.MakeTask_call();
        tcall->Task(any_cast<task*>(tf));
        call = tcall;
      }
    }
    Design* design = compileDesign->getCompiler()->getDesign();
    Package* pack = design->getPackage(packagename);
    if (call == nullptr) {
      if (pack && (List_of_arguments == 0)) {
        Value* val = pack->getValue(functionname);
        if (val && val->isValid()) {
          if (Bit_Select) {
            if (fC->Type(Bit_Select) == slConstant_select) {
              Bit_Select = fC->Child(Bit_Select);
            }
            any* tmpResult = compileSelectExpression(
                component, fC, Bit_Select, basename, compileDesign, pexpr,
                instance, reduce, muteErrors);
            if (tmpResult) return tmpResult;
          }
          UHDM::constant* c = s.MakeConstant();
          c->VpiValue(val->uhdmValue());
          c->VpiDecompile(val->decompiledValue());
          c->VpiSize(val->getSize());
          c->VpiConstType(val->vpiValType());
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
              result = compileSelectExpression(
                  component, fC, fC->Child(List_of_arguments), "",
                  compileDesign, pexpr, instance, reduce, muteErrors);
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
          component, fC, List_of_arguments, compileDesign, call, instance,
          reduce, muteErrors);
      call->Tf_call_args(arguments);
      result = call;
    } else {
      result = compileExpression(component, fC, name, compileDesign, pexpr,
                                 instance, reduce, muteErrors);
    }
  } else if (fC->Type(dotedName) == VObjectType::slStringConst) {
    result = compileExpression(component, fC, name, compileDesign, pexpr,
                               instance, reduce, muteErrors);
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
          fcall = compileRandomizeCall(component, fC, fC->Child(randomize_call),
                                       compileDesign, pexpr);
          fcall->Prefix(prefix);
          result = fcall;
          return result;
        }

        fcall = s.MakeMethod_func_call();
        fcall->VpiName(method_name);
        NodeId list_of_arguments =
            fC->Sibling(fC->Child(fC->Child(method_child)));
        NodeId with_conditions_node;
        if (fC->Type(list_of_arguments) == slList_of_arguments) {
          VectorOfany* arguments = compileTfCallArguments(
              component, fC, list_of_arguments, compileDesign, fcall, instance,
              reduce, muteErrors);
          fcall->Tf_call_args(arguments);
          with_conditions_node = fC->Sibling(list_of_arguments);
        } else {
          with_conditions_node = list_of_arguments;
        }
        // vpiWith: with conditions (expression in node u<62> above)
        // (not in every method, node id is 0 if missing)
        if (with_conditions_node != 0) {
          expr* with_conditions = (expr*)compileExpression(
              component, fC, with_conditions_node, compileDesign, pexpr,
              instance, reduce, muteErrors);
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
      expr* index =
          (expr*)compileExpression(component, fC, dotedName, compileDesign,
                                   pexpr, instance, reduce, muteErrors);
      const std::string& sel = fC->SymName(selectName);
      UHDM::hier_path* path = s.MakeHier_path();
      VectorOfany* elems = s.MakeAnyVec();
      bit_select* select = s.MakeBit_select();
      select->VpiIndex(index);
      select->VpiName(sval);
      select->VpiFullName(sval);
      select->VpiParent(path);
      path->Path_elems(elems);
      elems->push_back(select);
      std::string indexval;
      if (index) {
        if (index->UhdmType() == uhdmconstant) {
          indexval = "[" + index->VpiDecompile() + "]";
        } else if (index->UhdmType() == uhdmref_obj) {
          indexval += "[" + index->VpiName() + "]";
        }
      }
      ref_obj* selobj = s.MakeRef_obj();
      selobj->VpiParent(path);
      selobj->VpiName(sel);
      selobj->VpiFullName(sel);
      elems->push_back(selobj);
      std::string fullName = sval + indexval + "." + sel;
      path->VpiName(fullName);
      path->VpiFullName(fullName);
      path->VpiParent(pexpr);
      result = path;
    } else if (UHDM::any* st = getValue(
                   sval, component, compileDesign, instance, fC->getFileName(),
                   fC->Line(Bit_select), pexpr, reduce, muteErrors)) {
      UHDM_OBJECT_TYPE type = st->UhdmType();
      NodeId Select = dotedName;
      if (NodeId Bit_select = fC->Child(Select)) {
        NodeId Expression = fC->Child(Bit_select);
        while (Expression) {
          expr* index =
              (expr*)compileExpression(component, fC, Expression, compileDesign,
                                       pexpr, instance, reduce, muteErrors);
          if (index && index->UhdmType() == uhdmconstant) {
            bool invalidValue = false;
            uint64_t ind = (uint64_t)get_value(invalidValue, index);
            if (invalidValue == false && type == uhdmoperation) {
              operation* op = (operation*)st;
              int opType = op->VpiOpType();
              if (opType == vpiAssignmentPatternOp) {
                VectorOfany* operands = op->Operands();
                if (ind < operands->size()) {
                  result = operands->at(ind);
                  st = result;
                }
              } else if (opType == vpiConcatOp) {
                VectorOfany* operands = op->Operands();
                if (ind < operands->size()) {
                  result = operands->at(ind);
                  st = result;
                }
              }
            }
          }
          Expression = fC->Sibling(Expression);
        }
      }
      if (result == nullptr) {
        result = compileSelectExpression(component, fC, Bit_select, sval,
                                         compileDesign, pexpr, instance, reduce,
                                         muteErrors);
      }
    } else {
      result = compileSelectExpression(component, fC, Bit_select, sval,
                                       compileDesign, pexpr, instance, reduce,
                                       muteErrors);
    }
    if (result == nullptr) {
      const std::string& n = fC->SymName(name);
      ref_obj* ref = s.MakeRef_obj();
      ref->VpiName(n);
      ref->VpiParent(pexpr);
      if (pexpr) {
        UHDM::any* var = bindVariable(component, pexpr, n, compileDesign);
        if (var)
          ref->Actual_group(var);
        else if (component)
          component->needLateBinding(ref);
      } else if (instance) {
        UHDM::any* var = bindVariable(component, instance, n, compileDesign);
        if (var)
          ref->Actual_group(var);
        else if (component)
          component->needLateBinding(ref);
      }
      result = ref;
    }
  } else if (fC->Type(dotedName) == slList_of_arguments) {
    result = compileTfCall(component, fC, nodeId, compileDesign);
  } else if (fC->Type(name) == VObjectType::slStringConst) {
    const std::string& n = fC->SymName(name);
    ref_obj* ref = s.MakeRef_obj();
    ref->VpiName(n);
    ref->VpiParent(pexpr);
    if (pexpr) {
      UHDM::any* var = bindVariable(component, pexpr, n, compileDesign);
      if (var)
        ref->Actual_group(var);
      else if (component)
        component->needLateBinding(ref);
    } else if (instance) {
      UHDM::any* var = bindVariable(component, instance, n, compileDesign);
      if (var)
        ref->Actual_group(var);
      else if (component)
        component->needLateBinding(ref);
    }
    result = ref;
  }
  return result;
}

int64_t CompileHelper::getValue(bool& validValue, DesignComponent* component,
                                const FileContent* fC, NodeId nodeId,
                                CompileDesign* compileDesign, UHDM::any* pexpr,
                                ValuedComponentI* instance, bool reduce,
                                bool muteErrors) {
  int64_t result = 0;
  validValue = true;
  UHDM::any* expr = compileExpression(component, fC, nodeId, compileDesign,
                                      pexpr, instance, reduce, muteErrors);
  if (expr && expr->UhdmType() == UHDM::uhdmconstant) {
    UHDM::constant* c = (UHDM::constant*)expr;
    const std::string& v = c->VpiValue();
    int type = c->VpiConstType();
    switch (type) {
      case vpiBinaryConst: {
        result = std::strtoll(v.c_str() + strlen("BIN:"), 0, 2);
        break;
      }
      case vpiDecConst: {
        result = std::strtoll(v.c_str() + strlen("DEC:"), 0, 10);
        break;
      }
      case vpiHexConst: {
        result = std::strtoll(v.c_str() + strlen("HEX:"), 0, 16);
        break;
      }
      case vpiOctConst: {
        result = std::strtoll(v.c_str() + strlen("OCT:"), 0, 8);
        break;
      }
      case vpiIntConst: {
        result = std::strtoll(v.c_str() + strlen("INT:"), 0, 10);
        break;
      }
      case vpiUIntConst: {
        result = std::strtoull(v.c_str() + strlen("UINT:"), 0, 10);
        break;
      }
      default: {
        if (strstr(v.c_str(), "UINT:")) {
          result = std::strtoull(v.c_str() + strlen("UINT:"), 0, 10);
        } else {
          result = std::strtoll(v.c_str() + strlen("INT:"), 0, 10);
        }
        break;
      }
    }
  } else {
    validValue = false;
  }
  return result;
}

void CompileHelper::reorderAssignmentPattern(DesignComponent* mod,
                                             const UHDM::any* lhs,
                                             UHDM::any* rhs,
                                             CompileDesign* compileDesign,
                                             ValuedComponentI* instance,
                                             unsigned int level) {
  if (rhs->UhdmType() != uhdmoperation) return;
  operation* op = (operation*)rhs;
  int optype = op->VpiOpType();
  if (optype == vpiConditionOp) {
    bool invalidValue = false;
    expr* tmp = reduceExpr(op, invalidValue, mod, compileDesign, instance, "",
                           0, nullptr, true);
    if (tmp && (tmp->UhdmType() == uhdmoperation) && (invalidValue == false)) {
      op = (operation*)tmp;
      optype = op->VpiOpType();
    }
  }
  if (op->VpiReordered()) return;
  if ((optype != vpiAssignmentPatternOp) && (optype != vpiConcatOp)) return;
  VectorOfany* operands = op->Operands();
  bool ordered = true;
  for (any* operand : *operands) {
    if (operand->UhdmType() == uhdmtagged_pattern) {
      ordered = false;
      break;
    }
  }
  if (ordered) {
    if (lhs->UhdmType() == uhdmparameter) {
      parameter* p = (parameter*)lhs;
      VectorOfrange* ranges = nullptr;
      if (p->Ranges()) {
        ranges = p->Ranges();
      } else if (const typespec* tps = p->Typespec()) {
        UHDM_OBJECT_TYPE ttype = tps->UhdmType();
        if (ttype == uhdmbit_typespec) {
          ranges = ((bit_typespec*)tps)->Ranges();
        } else if (ttype == uhdmlogic_typespec) {
          ranges = ((logic_typespec*)tps)->Ranges();
        } else if (ttype == uhdmarray_typespec) {
          ranges = ((array_typespec*)tps)->Ranges();
        } else if (ttype == uhdmpacked_array_typespec) {
          ranges = ((packed_array_typespec*)tps)->Ranges();
        }
      }
      if (ranges) {
        if (level < ranges->size()) {
          range* r = ranges->at(level);
          expr* lr = (expr*)r->Left_expr();
          expr* rr = (expr*)r->Right_expr();
          bool invalidValue = false;
          lr = reduceExpr(lr, invalidValue, mod, compileDesign, instance, "", 0,
                          nullptr, true);
          int64_t lrv = get_value(invalidValue, lr);
          rr = reduceExpr(rr, invalidValue, mod, compileDesign, instance, "", 0,
                          nullptr, true);
          int64_t rrv = get_value(invalidValue, rr);
          if (lrv > rrv) {
            op->VpiReordered(true);
            std::reverse(operands->begin(), operands->end());
            if (level == 0) {
              if (instance) {
                instance->setComplexValue(p->VpiName(), op);
              } else {
                mod->setComplexValue(p->VpiName(), op);
              }
            }
          }
        }
      }
    }
  }
  for (any* operand : *operands) {
    if (operand->UhdmType() == uhdmoperation) {
      reorderAssignmentPattern(mod, lhs, operand, compileDesign, instance,
                               level + 1);
    }
  }
}
