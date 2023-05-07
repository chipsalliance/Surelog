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

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/FileSystem.h>
#include <Surelog/Design/Enum.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/ModuleDefinition.h>
#include <Surelog/Design/ModuleInstance.h>
#include <Surelog/Design/Netlist.h>
#include <Surelog/Design/ParamAssign.h>
#include <Surelog/Design/Parameter.h>
#include <Surelog/Design/SimpleType.h>
#include <Surelog/Design/Struct.h>
#include <Surelog/Design/TimeInfo.h>
#include <Surelog/Design/Union.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/CompileHelper.h>
#include <Surelog/DesignCompile/UhdmWriter.h>
#include <Surelog/Package/Package.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Testbench/TypeDef.h>
#include <Surelog/Utils/NumUtils.h>
#include <Surelog/Utils/StringUtils.h>

#include <cmath>
#include <cstring>

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_visitor.h>

namespace SURELOG {

using namespace UHDM;  // NOLINT (using a bunch of them)

bool CompileHelper::substituteAssignedValue(const UHDM::any *oper,
                                            CompileDesign *compileDesign) {
  bool substitute = true;
  if (!oper) {
    return false;
  }
  UHDM_OBJECT_TYPE opType = oper->UhdmType();
  if (opType == uhdmoperation) {
    operation *op = (operation *)oper;
    int32_t opType = op->VpiOpType();
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

any *CompileHelper::getObject(std::string_view name, DesignComponent *component,
                              CompileDesign *compileDesign,
                              ValuedComponentI *instance, const any *pexpr) {
  any *result = nullptr;
  while (pexpr) {
    if (const UHDM::scope *s = any_cast<const scope *>(pexpr)) {
      if ((result == nullptr) && s->Variables()) {
        for (auto o : *s->Variables()) {
          if (o->VpiName() == name) {
            result = o;
            break;
          }
        }
      }
    }
    if (const UHDM::task_func *s = any_cast<const task_func *>(pexpr)) {
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
    if (ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(instance)) {
      while (inst) {
        Netlist *netlist = inst->getNetlist();
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
              const std::string_view pname = o->Lhs()->VpiName();
              if (pname == name) {
                result = o;
                break;
              }
            }
          }
        }
        if ((result == nullptr) ||
            (result && (result->UhdmType() != uhdmconstant) &&
             (result->UhdmType() != uhdmparam_assign))) {
          if (expr *complex = instance->getComplexValue(name)) {
            result = complex;
          }
        }
        if (result) break;
        if (inst) {
          VObjectType insttype = inst->getType();
          if ((insttype != VObjectType::slInterface_instantiation) &&
              (insttype != VObjectType::slConditional_generate_construct) &&
              (insttype != VObjectType::slLoop_generate_construct) &&
              (insttype != VObjectType::slGenerate_item) &&
              (insttype !=
               VObjectType::slGenerate_module_conditional_statement) &&
              (insttype !=
               VObjectType::slGenerate_interface_conditional_statement) &&
              (insttype != VObjectType::slGenerate_module_loop_statement) &&
              (insttype != VObjectType::slGenerate_interface_loop_statement) &&
              (insttype != VObjectType::slGenerate_module_named_block) &&
              (insttype != VObjectType::slGenerate_interface_named_block) &&
              (insttype != VObjectType::slGenerate_module_block) &&
              (insttype != VObjectType::slGenerate_interface_block) &&
              (insttype != VObjectType::slGenerate_module_item) &&
              (insttype != VObjectType::slGenerate_interface_item) &&
              (insttype != VObjectType::slGenerate_block)) {
            break;
          } else {
            inst = inst->getParent();
          }
        }
      }
    }
  }
  // Instance component or package component
  if ((result == nullptr) && component) {
    for (ParamAssign *pass : component->getParamAssignVec()) {
      if (param_assign *p = pass->getUhdmParamAssign()) {
        const std::string_view pname = p->Lhs()->VpiName();
        if (pname == name) {
          if (substituteAssignedValue(p->Rhs(), compileDesign)) {
            result = (any *)p->Rhs();
            break;
          }
        }
      }
    }
    const DataType *dtype = component->getDataType(name);
    if ((result == nullptr) && dtype) {
      dtype = dtype->getActual();
      if (dtype->getTypespec()) result = dtype->getTypespec();
    }

    Signal *sig = nullptr;
    for (auto s : component->getPorts()) {
      if (s->getName() == name) {
        sig = s;
        break;
      }
    }
    if (sig == nullptr) {
      for (auto s : component->getSignals()) {
        if (s->getName() == name) {
          sig = s;
          break;
        }
      }
    }
    if (sig) {
      if (sig->getTypeSpecId()) {
        result = compileTypespec(component, sig->getFileContent(),
                                 sig->getTypeSpecId(), compileDesign,
                                 Reduce::No, nullptr, instance, true);
      }
    }
  }

  if ((result == nullptr) && instance) {
    if (ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(instance)) {
      // Instance component
      if (DesignComponent *comp = inst->getDefinition()) {
        for (ParamAssign *pass : comp->getParamAssignVec()) {
          if (param_assign *p = pass->getUhdmParamAssign()) {
            const std::string_view pname = p->Lhs()->VpiName();
            if (pname == name) {
              if (substituteAssignedValue(p->Rhs(), compileDesign)) {
                result = (any *)p->Rhs();
                break;
              }
            }
          }
        }

        const DataType *dtype = comp->getDataType(name);
        if ((result == nullptr) && dtype) {
          dtype = dtype->getActual();
          if (dtype->getTypespec()) result = dtype->getTypespec();
        }
      }
    }
  }

  if (result && (result->UhdmType() == uhdmref_obj)) {
    ref_obj *ref = (ref_obj *)result;
    const std::string_view refname = ref->VpiName();
    if (refname != name)
      result = getObject(refname, component, compileDesign, instance, pexpr);
    if (result) {
      if (UHDM::param_assign *passign = any_cast<param_assign *>(result)) {
        result = (any *)passign->Rhs();
      }
    }
  }
  if (result && result->UhdmType() == uhdmconstant) {
    if (instance) {
      Value *sval = instance->getValue(name);
      if (sval && sval->isValid()) {
        setRange((constant *)result, sval, compileDesign);
      }
    }
  }
  return result;
}

UHDM::task_func *getFuncFromPackage(std::string_view name,
                                    DesignComponent *component,
                                    std::set<DesignComponent *> &visited) {
  for (Package *pack : component->getAccessPackages()) {
    if (pack->getTask_funcs()) {
      for (UHDM::task_func *tf : *pack->getTask_funcs()) {
        if (tf->VpiName() == name) {
          return tf;
        }
      }
    }
    if (visited.find(pack) == visited.end()) {
      visited.insert(pack);
      UHDM::task_func *res = getFuncFromPackage(name, pack, visited);
      if (res) {
        return res;
      }
    }
  }
  return nullptr;
}

std::pair<UHDM::task_func *, DesignComponent *> CompileHelper::getTaskFunc(
    std::string_view name, DesignComponent *component,
    CompileDesign *compileDesign, ValuedComponentI *instance, any *pexpr) {
  std::pair<UHDM::task_func *, DesignComponent *> result = {nullptr, nullptr};
  DesignComponent *comp = component;
  if (name.find("::") != std::string::npos) {
    std::vector<std::string_view> res;
    StringUtils::tokenizeMulti(name, "::", res);
    if (res.size() > 1) {
      const std::string_view packName = res[0];
      const std::string_view funcName = res[1];
      Design *design = compileDesign->getCompiler()->getDesign();
      if (Package *pack = design->getPackage(packName)) {
        if (pack->getTask_funcs()) {
          for (UHDM::task_func *tf : *pack->getTask_funcs()) {
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
      for (UHDM::task_func *tf : *comp->getTask_funcs()) {
        if (tf->VpiName() == name) {
          result = std::make_pair(tf, component);
          return result;
        }
      }
    }
    comp = valuedcomponenti_cast<DesignComponent *>(
        (DesignComponent *)comp->getParentScope());
  }
  if (component) {
    for (const FileContent *cfC : component->getFileContents()) {
      FileContent *fC = (FileContent *)cfC;
      if (fC->getTask_funcs()) {
        for (UHDM::task_func *tf : *fC->getTask_funcs()) {
          if (tf->VpiName() == name) {
            result = std::make_pair(tf, component);
            return result;
          }
        }
      }
    }
  }
  if (component) {
    std::set<DesignComponent *> visited;
    task_func *res = getFuncFromPackage(name, component, visited);
    if (res) {
      result = std::make_pair(res, component);
      return result;
    }
  }
  if (instance) {
    ModuleInstance *inst = valuedcomponenti_cast<ModuleInstance *>(instance);
    while (inst) {
      DesignComponent *def = inst->getDefinition();
      if (def) {
        if (def->getTask_funcs()) {
          for (UHDM::task_func *tf : *def->getTask_funcs()) {
            if (tf->VpiName() == name) {
              result = std::make_pair(tf, def);
              return result;
            }
          }
        }
      }
      inst = inst->getParent();
    }
  }
  Design *design = compileDesign->getCompiler()->getDesign();
  auto &all_files = design->getAllFileContents();
  for (const auto &file : all_files) {
    FileContent *fC = file.second;
    if (fC->getTask_funcs()) {
      for (UHDM::task_func *tf : *fC->getTask_funcs()) {
        if (tf->VpiName() == name) {
          result = std::make_pair(tf, component);
          return result;
        }
      }
    }
  }
  return result;
}

bool getStringVal(std::string &result, expr *val) {
  const UHDM::constant *hs0 = any_cast<const UHDM::constant *>(val);
  if (hs0) {
    s_vpi_value *sval = String2VpiValue(hs0->VpiValue());
    if (sval) {
      if (sval->format == vpiStringVal || sval->format == vpiBinStrVal) {
        result = sval->value.str;
        return true;
      }
    }
  }
  return false;
}

static bool largeInt(std::string_view str) {
  bool isSigned = false;
  size_t pos = str.find('\'');
  if (pos != std::string::npos) {
    if (str.find_first_of("sS") != std::string::npos) {
      isSigned = true;
      str = str.substr(pos + 3);
    } else {
      str = str.substr(pos + 2);
    }
  }
  std::string value(str);
  value = StringUtils::replaceAll(value, "_", "");
  bool isLarge = false;
  if (value.size() > 20) {
    isLarge = true;
  } else if (value.size() == 20) {
    if (isSigned) {
      int64_t test = 0;
      isLarge = NumUtils::parseInt64(value, &test) == nullptr;
    } else {
      uint64_t test = 0;
      isLarge = NumUtils::parseUint64(value, &test) == nullptr;
    }
  }
  return isLarge;
}

constant *compileConst(const FileContent *fC, NodeId child, Serializer &s) {
  VObjectType objtype = fC->Type(child);
  constant *result = nullptr;
  switch (objtype) {
    case VObjectType::slIntConst: {
      // Do not evaluate the constant, keep it as in the source text:
      UHDM::constant *c = s.MakeConstant();
      const std::string_view value = fC->SymName(child);
      std::string v;
      c->VpiDecompile(value);
      bool tickNumber = (value.find('\'') != std::string::npos);
      if (tickNumber || largeInt(value)) {
        char base = 'd';
        uint32_t i = 0;
        bool isSigned = false;
        std::string size(value);
        if (tickNumber) {
          for (i = 0; i < value.size(); i++) {
            if (value[i] == '\'') {
              base = value[i + 1];
              if (base == 's' || base == 'S') base = value[i + 2];
              break;
            }
          }
          if (value.find_first_of("sS") != std::string::npos) {
            isSigned = true;
            v = value.substr(i + 3);
          } else {
            v = value.substr(i + 2);
          }
        } else {
          v = value;
          size = "";
        }
        v = StringUtils::replaceAll(v, "#", "");
        v = StringUtils::replaceAll(v, "_", "");
        size = StringUtils::rtrim_until(size, '\'');
        if (size.empty()) {
          c->VpiSize(-1);
        } else {
          int32_t s = 0;
          if (NumUtils::parseInt32(size, &s) == nullptr) {
            s = 0;
          }
          c->VpiSize(s);
        }
        if (isSigned) {
          int_typespec *tps = s.MakeInt_typespec();
          tps->VpiSigned(true);
          c->Typespec(tps);
        }
        switch (base) {
          case 'h':
          case 'H': {
            v = "HEX:" + v;
            c->VpiConstType(vpiHexConst);
            break;
          }
          case 'b':
          case 'B': {
            v = "BIN:" + v;
            c->VpiConstType(vpiBinaryConst);
            break;
          }
          case 'o':
          case 'O': {
            v = "OCT:" + v;
            c->VpiConstType(vpiOctConst);
            break;
          }
          case 'd':
          case 'D': {
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
        if (!value.empty() && value[0] == '-') {
          v.assign("INT:").append(value);
          c->VpiConstType(vpiIntConst);
        } else {
          v.assign("UINT:").append(value);
          c->VpiConstType(vpiUIntConst);
          v = StringUtils::replaceAll(v, "#", "");
        }
        c->VpiSize(64);
      }

      c->VpiValue(v);
      result = c;
      break;
    }
    case VObjectType::slRealConst: {
      UHDM::constant *c = s.MakeConstant();
      const std::string_view value = fC->SymName(child);
      c->VpiDecompile(value);
      c->VpiValue(StrCat("REAL:", value));
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
      UHDM::constant *c = s.MakeConstant();
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
      UHDM::constant *c = s.MakeConstant();
      std::string value = "BIN:1";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(0);
      c->VpiDecompile("'b1");
      result = c;
      break;
    }
    case VObjectType::slNumber_Tick1: {
      UHDM::constant *c = s.MakeConstant();
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
      UHDM::constant *c = s.MakeConstant();
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
      UHDM::constant *c = s.MakeConstant();
      std::string value = "BIN:0";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(0);
      c->VpiDecompile("'b0");
      result = c;
      break;
    }
    case VObjectType::slNumber_Tick0: {
      UHDM::constant *c = s.MakeConstant();
      std::string value = "BIN:0";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(-1);
      c->VpiDecompile("'0");
      result = c;
      break;
    }
    case VObjectType::slZ: {
      UHDM::constant *c = s.MakeConstant();
      std::string value = "BIN:Z";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(-1);
      c->VpiDecompile("'Z");
      result = c;
      break;
    }
    case VObjectType::slX: {
      UHDM::constant *c = s.MakeConstant();
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
      UHDM::constant *c = s.MakeConstant();
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
      const std::string_view value = fC->SymName(intC);
      NodeId unitId = fC->Sibling(intC);
      TimeInfo::Unit unit = TimeInfo::unitFromString(fC->SymName(unitId));
      uint64_t val = 0;
      if (NumUtils::parseUint64(value, &val) == nullptr) {
        val = 0;
      }
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
      UHDM::constant *c = s.MakeConstant();
      c->VpiValue("UINT:" + std::to_string(val));
      c->VpiConstType(vpiUIntConst);
      c->VpiSize(64);
      result = c;
      break;
    }
    case VObjectType::slStringLiteral: {
      UHDM::constant *c = s.MakeConstant();
      std::string_view value = StringUtils::unquoted(fC->SymName(child));
      c->VpiDecompile(fC->SymName(child));
      c->VpiSize(value.length() * 8);
      c->VpiValue(StrCat("STRING:", value));
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    }
    default:
      break;
  }
  return result;
}

any *CompileHelper::decodeHierPath(hier_path *path, bool &invalidValue,
                                   DesignComponent *component,
                                   CompileDesign *compileDesign, Reduce reduce,
                                   ValuedComponentI *instance, PathId fileId,
                                   uint32_t lineNumber, any *pexpr,
                                   bool muteErrors, bool returnTypespec) {
  UHDM::GetObjectFunctor getObjectFunctor =
      [&](std::string_view name, const any *inst,
          const any *pexpr) -> UHDM::any * {
    return getObject(name, component, compileDesign, instance, pexpr);
  };
  UHDM::GetObjectFunctor getValueFunctor =
      [&](std::string_view name, const any *inst,
          const any *pexpr) -> UHDM::any * {
    return (expr *)getValue(name, component, compileDesign, Reduce::Yes,
                            instance, fileId, lineNumber, (any *)pexpr, false);
  };
  UHDM::GetTaskFuncFunctor getTaskFuncFunctor =
      [&](std::string_view name, const any *inst) -> UHDM::task_func * {
    auto ret = getTaskFunc(name, component, compileDesign, instance, pexpr);
    return ret.first;
  };
  UHDM::ExprEval eval(muteErrors);
  eval.setGetObjectFunctor(getObjectFunctor);
  eval.setGetValueFunctor(getValueFunctor);
  eval.setGetTaskFuncFunctor(getTaskFuncFunctor);
  if (m_exprEvalPlaceHolder == nullptr) {
    m_exprEvalPlaceHolder = compileDesign->getSerializer().MakeModule_inst();
    m_exprEvalPlaceHolder->Param_assigns(
        compileDesign->getSerializer().MakeParam_assignVec());
  } else {
    m_exprEvalPlaceHolder->Param_assigns()->erase(
        m_exprEvalPlaceHolder->Param_assigns()->begin(),
        m_exprEvalPlaceHolder->Param_assigns()->end());
  }
  any *res = eval.decodeHierPath(path, invalidValue, m_exprEvalPlaceHolder,
                                 pexpr, returnTypespec, muteErrors);

  if (res == nullptr) {
    if ((reduce == Reduce::Yes) && (!muteErrors)) {
      ErrorContainer *errors =
          compileDesign->getCompiler()->getErrorContainer();
      SymbolTable *symbols = compileDesign->getCompiler()->getSymbolTable();
      // std::string fileContent = FileUtils::getFileContent(fileName);
      // std::string_view lineText =
      //     StringUtils::getLineInString(fileContent, lineNumber);
      const std::string_view lineText = path->VpiFullName();
      Location loc(fileId, lineNumber, 0, symbols->registerSymbol(lineText));
      Error err(ErrorDefinition::UHDM_UNRESOLVED_HIER_PATH, loc);
      errors->addError(err);
    }
  }
  return res;
}

expr *CompileHelper::reduceExpr(any *result, bool &invalidValue,
                                DesignComponent *component,
                                CompileDesign *compileDesign,
                                ValuedComponentI *instance, PathId fileId,
                                uint32_t lineNumber, any *pexpr,
                                bool muteErrors) {
  UHDM::GetObjectFunctor getObjectFunctor =
      [&](std::string_view name, const any *inst,
          const any *pexpr) -> UHDM::any * {
    return getObject(name, component, compileDesign, instance, pexpr);
  };
  UHDM::GetObjectFunctor getValueFunctor =
      [&](std::string_view name, const any *inst,
          const any *pexpr) -> UHDM::any * {
    return (expr *)getValue(name, component, compileDesign, Reduce::Yes,
                            instance, fileId, lineNumber, (any *)pexpr,
                            muteErrors);
  };
  UHDM::GetTaskFuncFunctor getTaskFuncFunctor =
      [&](std::string_view name, const any *inst) -> UHDM::task_func * {
    auto ret = getTaskFunc(name, component, compileDesign, instance, pexpr);
    return ret.first;
  };
  UHDM::ExprEval eval(muteErrors);
  eval.setGetObjectFunctor(getObjectFunctor);
  eval.setGetValueFunctor(getValueFunctor);
  eval.setGetTaskFuncFunctor(getTaskFuncFunctor);
  if (m_exprEvalPlaceHolder == nullptr) {
    m_exprEvalPlaceHolder = compileDesign->getSerializer().MakeModule_inst();
    m_exprEvalPlaceHolder->Param_assigns(
        compileDesign->getSerializer().MakeParam_assignVec());
  } else {
    m_exprEvalPlaceHolder->Param_assigns()->erase(
        m_exprEvalPlaceHolder->Param_assigns()->begin(),
        m_exprEvalPlaceHolder->Param_assigns()->end());
  }
  expr *res = eval.reduceExpr(result, invalidValue, m_exprEvalPlaceHolder,
                              pexpr, muteErrors);
  // If loop was detected, drop the partially constructed new value!
  return m_unwind ? nullptr : res;
}

any *CompileHelper::getValue(std::string_view name, DesignComponent *component,
                             CompileDesign *compileDesign, Reduce reduce,
                             ValuedComponentI *instance, PathId fileId,
                             uint32_t lineNumber, any *pexpr, bool muteErrors) {
  Serializer &s = compileDesign->getSerializer();
  Value *sval = nullptr;
  any *result = nullptr;
  if (loopDetected(fileId, lineNumber, compileDesign, instance)) {
    return nullptr;
  }
  if (m_checkForLoops) {
    m_stackLevel++;
  }
  if (name.find("::") != std::string::npos) {
    std::vector<std::string_view> res;
    StringUtils::tokenizeMulti(name, "::", res);
    if (res.size() > 1) {
      const std::string_view packName = res[0];
      const std::string_view varName = res[1];
      Design *design = compileDesign->getCompiler()->getDesign();
      if (Package *pack = design->getPackage(packName)) {
        if (expr *val = pack->getComplexValue(varName)) {
          result = val;
          if (result) {
            if (result->UhdmType() == uhdmoperation) {
              operation *op = (operation *)result;
              UHDM::ExprEval eval;
              expr *res = eval.flattenPatternAssignments(s, op->Typespec(),
                                                         (UHDM::expr *)result);
              if (res->UhdmType() == uhdmoperation) {
                ((operation *)result)->Operands(((operation *)res)->Operands());
              }
            }
          }
        }
        if (result == nullptr) {
          if (Value *sval = pack->getValue(varName)) {
            UHDM::constant *c = s.MakeConstant();
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
    if (expr *val = instance->getComplexValue(name)) {
      result = val;
      if (result->UhdmType() == uhdmconstant) {
        sval = instance->getValue(name);
        if (sval && sval->isValid()) {
          setRange((constant *)result, sval, compileDesign);
        }
      }
    }
    if (result == nullptr) {
      sval = instance->getValue(name);
      if (sval && sval->isValid()) {
        UHDM::constant *c = s.MakeConstant();
        c->VpiValue(sval->uhdmValue());
        setRange(c, sval, compileDesign);
        c->VpiDecompile(sval->decompiledValue());
        c->VpiConstType(sval->vpiValType());
        c->VpiSize(sval->getSize());
        result = c;
      }
    }
  }

  ValuedComponentI *tmpInstance = instance;
  while ((result == nullptr) && tmpInstance) {
    if (ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(tmpInstance)) {
      Netlist *netlist = inst->getNetlist();
      if (netlist) {
        UHDM::VectorOfparam_assign *param_assigns = netlist->param_assigns();
        if (param_assigns) {
          for (param_assign *param : *param_assigns) {
            if (param && param->Lhs()) {
              const std::string_view param_name = param->Lhs()->VpiName();
              if (param_name == name) {
                if (substituteAssignedValue(param->Rhs(), compileDesign)) {
                  if (param->Rhs()->UhdmType() == uhdmoperation) {
                    operation *op = (operation *)param->Rhs();
                    int32_t opType = op->VpiOpType();
                    if (opType == vpiAssignmentPatternOp) {
                      const any *lhs = param->Lhs();
                      any *rhs = (any *)param->Rhs();
                      const typespec *ts = nullptr;
                      if (lhs->UhdmType() == uhdmparameter) {
                        ts = ((parameter *)lhs)->Typespec();
                      }
                      rhs = expandPatternAssignment(ts, (expr *)rhs, component,
                                                    compileDesign, instance);
                      param->Rhs(rhs);
                      reorderAssignmentPattern(component, lhs, rhs,
                                               compileDesign, instance, 0);
                    }
                  }

                  ElaboratorListener listener(&s, false, true);
                  result = UHDM::clone_tree((any *)param->Rhs(), s, &listener);
                  break;
                }
              }
            }
          }
        }
        if (auto variables = netlist->variables()) {
          for (auto var : *variables) {
            if (var->VpiName() == name) {
              if (const expr *exp = var->Expr()) {
                UHDM_OBJECT_TYPE vartype = var->UhdmType();
                if (vartype == uhdmint_var || vartype == uhdminteger_var ||
                    vartype == uhdmreal_var || vartype == uhdmshort_int_var ||
                    vartype == uhdmlong_int_var)
                  result = (expr *)exp;
                break;
              }
            }
          }
        }
      }
    }
    if (result) break;
    if (ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(tmpInstance)) {
      tmpInstance = (ValuedComponentI *)inst->getParentScope();
    } else if (FScope *inst = valuedcomponenti_cast<FScope *>(tmpInstance)) {
      tmpInstance = (ValuedComponentI *)inst->getParentScope();
    } else {
      tmpInstance = nullptr;
    }
  }

  if (result == nullptr) {
    if (instance) {
      if (expr *val = instance->getComplexValue(name)) {
        result = val;
      }
      if (result == nullptr) {
        sval = instance->getValue(name);
        if (sval && sval->isValid()) {
          UHDM::constant *c = s.MakeConstant();
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
    if (expr *val = component->getComplexValue(name)) {
      result = val;
    }
    if (result == nullptr) {
      sval = component->getValue(name);
      if (sval && sval->isValid()) {
        UHDM::constant *c = s.MakeConstant();
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
    UHDM::VectorOfparam_assign *param_assigns = component->getParam_assigns();
    if (param_assigns) {
      for (param_assign *param : *param_assigns) {
        if (param && param->Lhs()) {
          const std::string_view param_name = param->Lhs()->VpiName();
          if (param_name == name) {
            if (substituteAssignedValue(param->Rhs(), compileDesign)) {
              if (param->Rhs()->UhdmType() == uhdmoperation) {
                operation *op = (operation *)param->Rhs();
                int32_t opType = op->VpiOpType();
                if (opType == vpiAssignmentPatternOp) {
                  const any *lhs = param->Lhs();
                  any *rhs = (any *)param->Rhs();
                  const typespec *ts = nullptr;
                  if (lhs->UhdmType() == uhdmparameter) {
                    ts = ((parameter *)lhs)->Typespec();
                  }
                  rhs = expandPatternAssignment(ts, (expr *)rhs, component,
                                                compileDesign, instance);
                  param->Rhs(rhs);
                  reorderAssignmentPattern(component, lhs, rhs, compileDesign,
                                           instance, 0);
                }
              }

              ElaboratorListener listener(&s, false, true);
              result = UHDM::clone_tree((any *)param->Rhs(), s, &listener);
              break;
            }
          }
        }
      }
    }
  }
  if (component && (result == nullptr)) {
    for (const auto &tp : component->getTypeDefMap()) {
      TypeDef *tpd = tp.second;
      typespec *tps = tpd->getTypespec();
      if (tps && tps->UhdmType() == uhdmenum_typespec) {
        enum_typespec *etps = (enum_typespec *)tps;
        for (auto n : *etps->Enum_consts()) {
          if (n->VpiName() == name) {
            UHDM::constant *c = s.MakeConstant();
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
        any *tmp =
            getValue(result->VpiName(), component, compileDesign, Reduce::Yes,
                     instance, fileId, lineNumber, pexpr, muteErrors);
        if (tmp) result = tmp;
      }
    } else if (resultType == uhdmoperation || resultType == uhdmhier_path ||
               resultType == uhdmbit_select ||
               resultType == uhdmsys_func_call) {
      if (reduce == Reduce::Yes) {
        bool invalidValue = false;
        any *tmp = reduceExpr(result, invalidValue, component, compileDesign,
                              instance, fileId, lineNumber, pexpr, muteErrors);
        if (tmp) result = tmp;
      }
    } else {
      int32_t setBreakpointHere = 1;
      setBreakpointHere++;
    }
  }
  if (m_checkForLoops) {
    m_stackLevel--;
  }
  return result;
}

UHDM::any *CompileHelper::compileSelectExpression(
    DesignComponent *component, const FileContent *fC, NodeId Bit_select,
    std::string_view name, CompileDesign *compileDesign, Reduce reduce,
    UHDM::any *pexpr, ValuedComponentI *instance, bool muteErrors) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  if ((fC->Type(Bit_select) == VObjectType::slConstant_bit_select) &&
      (!fC->Sibling(Bit_select))) {
    Bit_select = fC->Child(Bit_select);
  }
  if ((fC->Type(Bit_select) == VObjectType::slBit_select) &&
      (!fC->Sibling(Bit_select))) {
    Bit_select = fC->Child(Bit_select);
  }
  if (fC->Child(Bit_select) && fC->Sibling(Bit_select)) {
    // More than one
    UHDM::var_select *var_select = s.MakeVar_select();
    VectorOfexpr *exprs = s.MakeExprVec();
    var_select->Exprs(exprs);
    var_select->VpiName(name);
    result = var_select;
  }
  NodeId lastBitExp;
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
          if ((fC->Type(bitexp) != VObjectType::slConstant_expression) &&
              (fC->Type(bitexp) != VObjectType::slExpression)) {
            break;
          }
          expr *sel =
              (expr *)compileExpression(component, fC, bitexp, compileDesign,
                                        reduce, pexpr, instance, muteErrors);

          if (result) {
            UHDM::var_select *var_select = (UHDM::var_select *)result;
            VectorOfexpr *exprs = var_select->Exprs();
            exprs->push_back(sel);
            if (sel->VpiParent() == nullptr) sel->VpiParent(var_select);
          } else if (fC->Child(Bit_select) && fC->Sibling(Bit_select)) {
            UHDM::var_select *var_select = s.MakeVar_select();
            VectorOfexpr *exprs = s.MakeExprVec();
            var_select->Exprs(exprs);
            var_select->VpiName(name);
            exprs->push_back(sel);
            result = var_select;
            if (sel->VpiParent() == nullptr) sel->VpiParent(var_select);
          } else {
            bit_select *bit_select = s.MakeBit_select();
            bit_select->VpiName(name);
            bit_select->VpiIndex(sel);
            result = bit_select;
            if (sel->VpiParent() == nullptr) sel->VpiParent(bit_select);
            ref_obj *ref = s.MakeRef_obj();
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
      expr *sel = (expr *)compilePartSelectRange(component, fC, Constant_range,
                                                 name, compileDesign, reduce,
                                                 pexpr, instance, muteErrors);
      if (result) {
        UHDM::var_select *var_select = (UHDM::var_select *)result;
        VectorOfexpr *exprs = var_select->Exprs();
        exprs->push_back(sel);
        sel->VpiParent(var_select);
      } else if (fC->Child(Bit_select) && fC->Sibling(Bit_select)) {
        UHDM::var_select *var_select = s.MakeVar_select();
        VectorOfexpr *exprs = s.MakeExprVec();
        var_select->Exprs(exprs);
        var_select->VpiName(name);
        exprs->push_back(sel);
        sel->VpiParent(var_select);
      } else {
        result = sel;
      }
    } else if ((fC->Type(Bit_select) == VObjectType::slStringConst) ||
               (fC->Type(Bit_select) ==
                VObjectType::slPs_or_hierarchical_identifier)) {
      std::string hname(name);
      hier_path *path = s.MakeHier_path();
      UHDM::VectorOfany *elems = s.MakeAnyVec();
      ref_obj *r1 = s.MakeRef_obj();
      r1->VpiName(name);
      r1->VpiFullName(name);
      path->Path_elems(elems);
      elems->push_back(r1);
      r1->VpiParent(path);
      while (Bit_select) {
        if ((fC->Type(Bit_select) ==
             VObjectType::slPs_or_hierarchical_identifier)) {
          ref_obj *r = s.MakeRef_obj();
          NodeId nameId = fC->Child(Bit_select);
          r->VpiName(fC->SymName(nameId));
          elems->push_back(r);
          hname.append(".").append(fC->SymName(nameId));
        } else if ((fC->Type(Bit_select) == VObjectType::slSelect)) {
          ref_obj *r = s.MakeRef_obj();
          NodeId nameId = fC->Child(Bit_select);
          if (nameId && (fC->Type(nameId) == VObjectType::slStringConst)) {
            r->VpiName(fC->SymName(nameId));
            elems->push_back(r);
            hname.append(".").append(fC->SymName(nameId));
          }
        } else if (fC->Type(Bit_select) == VObjectType::slStringConst) {
          NodeId tmp = fC->Sibling(Bit_select);
          if (((fC->Type(tmp) == VObjectType::slConstant_bit_select) ||
               (fC->Type(tmp) == VObjectType::slBit_select)) &&
              fC->Child(tmp)) {
            any *sel =
                compileExpression(component, fC, Bit_select, compileDesign,
                                  reduce, pexpr, instance, muteErrors);
            if (sel) {
              if (sel->UhdmType() == uhdmhier_path) {
                hier_path *p = (hier_path *)sel;
                for (auto el : *p->Path_elems()) {
                  elems->push_back(el);
                  std::string n(el->VpiName());
                  if (el->UhdmType() == uhdmbit_select) {
                    bit_select *bs = (bit_select *)el;
                    const expr *index = bs->VpiIndex();
                    std::string_view ind = index->VpiDecompile();
                    if (ind.empty()) ind = index->VpiName();
                    n.append("[").append(ind).append("]");
                    hname += "." + n;
                    ref_obj *r = nullptr;
                    if ((bs->VpiParent() != nullptr) &&
                        (bs->VpiParent()->UhdmType() == uhdmref_obj)) {
                      r = (ref_obj *)bs->VpiParent();
                    } else {
                      r = s.MakeRef_obj();
                      bs->VpiParent(r);
                    }
                    r->VpiName(hname);
                    r->VpiParent(path);
                  } else {
                    hname += "." + n;
                    el->VpiParent(path);
                  }
                }
                break;
              } else {
                hname.append(".").append(sel->VpiName());
                if (sel->UhdmType() == uhdmbit_select) {
                  ref_obj *r = nullptr;
                  if ((sel->VpiParent() != nullptr) &&
                      (sel->VpiParent()->UhdmType() == uhdmref_obj)) {
                    r = (ref_obj *)sel->VpiParent();
                  } else {
                    r = s.MakeRef_obj();
                    sel->VpiParent(r);
                  }
                  r->VpiName(hname);
                  r->VpiParent(path);
                } else {
                  sel->VpiParent(path);
                }
                elems->push_back(sel);
              }
            }
          } else {
            ref_obj *r2 = s.MakeRef_obj();
            r2->VpiName(fC->SymName(Bit_select));
            r2->VpiFullName(fC->SymName(Bit_select));
            r2->VpiParent(path);
            elems->push_back(r2);
            hname.append(".").append(fC->SymName(Bit_select));
          }
        }
        Bit_select = fC->Sibling(Bit_select);
      }
      path->VpiName(hname);
      path->VpiFullName(hname);
      fC->populateCoreMembers(Bit_select, Bit_select, path);
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

// This is a a very large function and probably should be split into
// smaller chunks.
UHDM::any *CompileHelper::compileExpression(
    DesignComponent *component, const FileContent *fC, NodeId parent,
    CompileDesign *compileDesign, Reduce reduce, UHDM::any *pexpr,
    ValuedComponentI *instance, bool muteErrors) {
  if (m_checkForLoops) {
    m_stackLevel++;
  }
  FileSystem *const fileSystem = FileSystem::getInstance();
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  VObjectType parentType = fC->Type(parent);
  UHDM::VectorOfattribute *attributes = nullptr;
  if (parentType == VObjectType::slAttribute_instance) {
    attributes = compileAttributes(component, fC, parent, compileDesign);
    while (fC->Type(parent) == VObjectType::slAttribute_instance)
      parent = fC->Sibling(parent);
  }
  parentType = fC->Type(parent);
  NodeId child = fC->Child(parent);
  VObjectType childType = VObjectType::sl_INVALID_;
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
    case VObjectType::slIntegerAtomType_Integer: {
      result = s.MakeInteger_var();
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
      UHDM::operation *list_op = s.MakeOperation();
      list_op->VpiOpType(vpiListOp);
      UHDM::VectorOfany *operands = s.MakeAnyVec();
      list_op->Operands(operands);
      NodeId lexpr = child;
      NodeId rexpr = fC->Sibling(lexpr);
      if (expr *op = any_cast<expr *>(
              compileExpression(component, fC, lexpr, compileDesign, reduce,
                                pexpr, instance, muteErrors))) {
        operands->push_back(op);
      }
      if (rexpr) {
        if (expr *op = any_cast<expr *>(
                compileExpression(component, fC, rexpr, compileDesign, reduce,
                                  pexpr, instance, muteErrors))) {
          operands->push_back(op);
        }
      }
      list_op->Attributes(attributes);
      result = list_op;
      fC->populateCoreMembers(parent, parent, result);
      if (m_checkForLoops) {
        m_stackLevel--;
      }
      return result;
    }
    case VObjectType::slNet_lvalue: {
      UHDM::operation *operation = s.MakeOperation();
      UHDM::VectorOfany *operands = s.MakeAnyVec();
      operation->Attributes(attributes);
      result = operation;
      operation->VpiParent(pexpr);
      operation->Operands(operands);
      operation->VpiOpType(vpiConcatOp);
      fC->populateCoreMembers(parent, parent, result);
      NodeId Expression = parent;
      while (Expression) {
        UHDM::any *exp = compileExpression(component, fC, fC->Child(Expression),
                                           compileDesign, reduce, pexpr,
                                           instance, muteErrors);
        if (exp) {
          operands->push_back(exp);
          if (exp->VpiParent()) {
            ((any *)exp->VpiParent())->VpiParent(operation);
          } else {
            exp->VpiParent(operation);
          }
        }
        Expression = fC->Sibling(Expression);
      }
      if (m_checkForLoops) {
        m_stackLevel--;
      }
      return result;
    }
    case VObjectType::slConcatenation:
    case VObjectType::slConstant_concatenation: {
      UHDM::operation *operation = s.MakeOperation();
      UHDM::VectorOfany *operands = s.MakeAnyVec();
      operation->Attributes(attributes);
      result = operation;
      operation->VpiParent(pexpr);
      operation->Operands(operands);
      operation->VpiOpType(vpiConcatOp);
      fC->populateCoreMembers(parent, parent, result);
      NodeId Expression = fC->Child(parent);
      while (Expression) {
        UHDM::any *exp =
            compileExpression(component, fC, Expression, compileDesign, reduce,
                              pexpr, instance, muteErrors);
        if (exp) operands->push_back(exp);
        Expression = fC->Sibling(Expression);
      }
      child = InvalidNodeId;  // Use parent for location info computation down
                              // below!
      break;
    }
    case VObjectType::slDelay2:
    case VObjectType::slDelay3: {
      NodeId MinTypMax = child;
      if (fC->Sibling(MinTypMax)) {
        UHDM::operation *operation = s.MakeOperation();
        UHDM::VectorOfany *operands = s.MakeAnyVec();
        operation->Operands(operands);
        operation->VpiOpType(vpiListOp);
        fC->populateCoreMembers(parent, parent, operation);
        result = operation;
        NodeId Expression = MinTypMax;
        while (Expression) {
          UHDM::any *exp =
              compileExpression(component, fC, Expression, compileDesign,
                                reduce, pexpr, instance, muteErrors);
          if (exp) operands->push_back(exp);
          Expression = fC->Sibling(Expression);
        }
        if (m_checkForLoops) {
          m_stackLevel--;
        }
        return result;
      }
      break;
    }
    case VObjectType::slConstant_mintypmax_expression:
    case VObjectType::slMintypmax_expression: {
      NodeId Expression = child;
      operation *op = s.MakeOperation();
      op->VpiOpType(vpiMinTypMaxOp);
      op->VpiParent(pexpr);
      fC->populateCoreMembers(parent, parent, op);
      UHDM::VectorOfany *operands = s.MakeAnyVec();
      op->Operands(operands);
      result = op;
      while (Expression) {
        expr *sExpr =
            (expr *)compileExpression(component, fC, Expression, compileDesign,
                                      reduce, op, instance, muteErrors);
        if (sExpr) operands->push_back(sExpr);
        Expression = fC->Sibling(Expression);
      }
      if (m_checkForLoops) {
        m_stackLevel--;
      }
      return result;
    }
    case VObjectType::slExpression: {
      NodeId Iff = fC->Sibling(parent);
      if (fC->Type(Iff) == VObjectType::slIFF) {
        operation *op = s.MakeOperation();
        op->VpiOpType(vpiIffOp);
        op->VpiParent(pexpr);
        UHDM::VectorOfany *operands = s.MakeAnyVec();
        op->Operands(operands);
        result = op;
        expr *lExpr =
            (expr *)compileExpression(component, fC, child, compileDesign,
                                      reduce, op, instance, muteErrors);
        if (lExpr) operands->push_back(lExpr);
        NodeId Expr = fC->Sibling(Iff);
        expr *rExpr =
            (expr *)compileExpression(component, fC, Expr, compileDesign,
                                      reduce, op, instance, muteErrors);
        if (rExpr) operands->push_back(rExpr);
        if (m_checkForLoops) {
          m_stackLevel--;
        }
        return result;
      }
      break;
    }
    case VObjectType::slClass_new: {
      UHDM::method_func_call *sys = s.MakeMethod_func_call();
      sys->VpiName("new");
      sys->VpiParent(pexpr);
      NodeId argListNode = child;
      UHDM::VectorOfany *arguments =
          compileTfCallArguments(component, fC, argListNode, compileDesign,
                                 reduce, sys, instance, muteErrors);
      sys->Tf_call_args(arguments);
      result = sys;
      if (m_checkForLoops) {
        m_stackLevel--;
      }
      return result;
    }
    case VObjectType::slPort_expression: {
      operation *op = s.MakeOperation();
      op->VpiParent(pexpr);
      op->VpiOpType(vpiConcatOp);
      op->Operands(s.MakeAnyVec());
      auto ops = op->Operands();
      result = op;
      NodeId Port_reference = child;
      while (Port_reference) {
        NodeId Name = fC->Child(Port_reference);
        NodeId Constant_select = fC->Sibling(Name);

        if (fC->Type(Constant_select) == VObjectType::slConstant_select) {
          Constant_select = fC->Child(Constant_select);
        }
        if (fC->Child(Constant_select) || fC->Sibling(Constant_select)) {
          any *select = compileSelectExpression(component, fC, Constant_select,
                                                "", compileDesign, reduce,
                                                pexpr, instance, muteErrors);
          ops->push_back(select);
        } else {
          ref_obj *ref = s.MakeRef_obj();
          ops->push_back(ref);
          const std::string_view name = fC->SymName(Name);
          ref->VpiName(name);
          ref->VpiParent(op);
          fC->populateCoreMembers(Port_reference, Port_reference, ref);
          if (pexpr) {
            if (UHDM::any *var =
                    bindVariable(component, pexpr, name, compileDesign))
              ref->Actual_group(var);
            else if (component)
              component->needLateBinding(ref);
          } else if (instance) {
            if (UHDM::any *var =
                    bindVariable(component, instance, name, compileDesign))
              ref->Actual_group(var);
            else if (component)
              component->needLateBinding(ref);
          } else if (component) {
            component->needLateBinding(ref);
          }
        }
        unsupported_typespec *tps = s.MakeUnsupported_typespec();
        op->Typespec(tps);
        component->needLateTypedefBinding(op);
        Port_reference = fC->Sibling(Port_reference);
      }
      break;
    }
    default:
      break;
  }

  if ((parentType == VObjectType::slVariable_lvalue) &&
      (childType == VObjectType::slVariable_lvalue)) {
    UHDM::operation *operation = s.MakeOperation();
    UHDM::VectorOfany *operands = s.MakeAnyVec();
    operation->Attributes(attributes);
    result = operation;
    operation->VpiParent(pexpr);
    operation->Operands(operands);
    operation->VpiOpType(vpiConcatOp);
    fC->populateCoreMembers(child, child, result);
    NodeId Expression = child;
    while (Expression) {
      NodeId n = fC->Child(Expression);
      if (fC->Type(n) == VObjectType::slVariable_lvalue) {
        n = Expression;
      }
      UHDM::any *exp = compileExpression(component, fC, n, compileDesign,
                                         reduce, pexpr, instance, muteErrors);
      if (exp) {
        operands->push_back(exp);
        if (!exp->VpiParent()) exp->VpiParent(operation);
      }
      Expression = fC->Sibling(Expression);
    }
    if (m_checkForLoops) {
      m_stackLevel--;
    }
    return result;
  }

  if (result == nullptr) {
    if (child) {
      switch (childType) {
        case VObjectType::slNull_keyword: {
          UHDM::constant *c = s.MakeConstant();
          c->VpiValue("UINT:0");
          c->VpiDecompile("0");
          c->VpiSize(64);
          c->VpiConstType(vpiNullConst);
          result = c;
          break;
        }
        case VObjectType::slDollar_keyword: {
          UHDM::constant *c = s.MakeConstant();
          c->VpiConstType(vpiUnboundedConst);
          c->VpiValue("STRING:$");
          c->VpiDecompile("$");
          c->VpiSize(1);
          result = c;
          break;
        }
        case VObjectType::slThis_keyword:
        case VObjectType::slSuper_keyword:
        case VObjectType::slThis_dot_super: {
          result = compileComplexFuncCall(component, fC, parent, compileDesign,
                                          reduce, pexpr, instance, muteErrors);
          break;
        }
        case VObjectType::slArray_member_label: {
          UHDM::operation *operation = s.MakeOperation();
          UHDM::VectorOfany *operands = s.MakeAnyVec();
          operation->Attributes(attributes);
          result = operation;
          operation->VpiParent(pexpr);
          operation->Operands(operands);
          operation->VpiOpType(vpiConcatOp);
          fC->populateCoreMembers(child, child, result);
          NodeId Expression = child;
          bool odd = true;
          while (Expression) {
            NodeId the_exp = fC->Child(Expression);
            if (!the_exp) {
              ref_obj *ref = s.MakeRef_obj();
              ref->VpiName("default");
              operands->push_back(ref);
              ref->VpiParent(operation);
              ref->VpiStructMember(true);
            } else {
              UHDM::any *exp =
                  compileExpression(component, fC, the_exp, compileDesign,
                                    reduce, pexpr, instance, muteErrors);
              if (exp) {
                operands->push_back(exp);
                if (!exp->VpiParent()) exp->VpiParent(operation);
                if (odd) {
                  if (exp->UhdmType() == uhdmref_obj)
                    ((ref_obj *)exp)->VpiStructMember(true);
                }
              }
            }
            Expression = fC->Sibling(Expression);
            odd = !odd;
          }
          if (m_checkForLoops) {
            m_stackLevel--;
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
          uint32_t vopType = UhdmWriter::getVpiOpType(childType);
          if (vopType) {
            UHDM::operation *op = s.MakeOperation();
            op->VpiOpType(vopType);
            op->VpiParent(pexpr);
            op->Attributes(attributes);
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            NodeId var = fC->Sibling(child);
            if (fC->Type(var) == VObjectType::slVariable_lvalue) {
              var = fC->Child(var);
            }
            if (UHDM::any *operand =
                    compileExpression(component, fC, var, compileDesign, reduce,
                                      op, instance, muteErrors)) {
              operands->push_back(operand);
            }
            op->Operands(operands);
            fC->populateCoreMembers(parent, parent, op);
            result = op;
          }
          break;
        }
        case VObjectType::slEdge_Posedge: {
          UHDM::operation *op = s.MakeOperation();
          op->Attributes(attributes);
          op->VpiOpType(vpiPosedgeOp);
          op->VpiParent(pexpr);
          if (UHDM::any *operand = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, reduce, op,
                  instance, muteErrors)) {
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            operands->push_back(operand);
            op->Operands(operands);
            fC->populateCoreMembers(parent, parent, op);
          }
          result = op;
          break;
        }
        case VObjectType::slEdge_Edge: {
          UHDM::operation *op = s.MakeOperation();
          op->Attributes(attributes);
          op->VpiOpType(vpiAnyEdge);
          op->VpiParent(pexpr);
          if (UHDM::any *operand = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, reduce, op,
                  instance, muteErrors)) {
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            operands->push_back(operand);
            op->Operands(operands);
            fC->populateCoreMembers(parent, parent, op);
          }
          result = op;
          break;
        }
        case VObjectType::slEdge_Negedge: {
          UHDM::operation *op = s.MakeOperation();
          op->Attributes(attributes);
          op->VpiOpType(vpiNegedgeOp);
          op->VpiParent(pexpr);
          if (UHDM::any *operand = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, reduce, op,
                  instance, muteErrors)) {
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            operands->push_back(operand);
            op->Operands(operands);
            fC->populateCoreMembers(parent, parent, op);
          }
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
        case VObjectType::slConst_or_range_expression:
          result = compileExpression(component, fC, child, compileDesign,
                                     reduce, pexpr, instance, muteErrors);
          break;
        case VObjectType::slExpression_or_dist: {
          result = compileExpression(component, fC, child, compileDesign,
                                     reduce, pexpr, instance, muteErrors);
          if (NodeId dist = fC->Sibling(child)) {
            operation *op = s.MakeOperation();
            op->VpiParent(pexpr);
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            op->Operands(operands);
            operands->push_back(result);
            VObjectType distType = fC->Type(dist);
            if (distType == VObjectType::slBoolean_abbrev) {
              NodeId repetition = fC->Child(dist);
              VObjectType repetType = fC->Type(repetition);
              op->VpiOpType(UhdmWriter::getVpiOpType(repetType));
              any *rep =
                  compileExpression(component, fC, repetition, compileDesign,
                                    reduce, pexpr, instance, muteErrors);
              operands->push_back(rep);
              result = op;
            } else if (distType == VObjectType::slThroughout ||
                       distType == VObjectType::slWithin ||
                       distType == VObjectType::slIntersect) {
              NodeId repetition = fC->Sibling(dist);
              op->VpiOpType(UhdmWriter::getVpiOpType(distType));
              any *rep =
                  compileExpression(component, fC, repetition, compileDesign,
                                    reduce, pexpr, instance, muteErrors);
              operands->push_back(rep);
              result = op;
            }
          }
          break;
        }
        case VObjectType::slComplex_func_call: {
          result = compileComplexFuncCall(component, fC, fC->Child(child),
                                          compileDesign, reduce, pexpr,
                                          instance, muteErrors);
          break;
        }
        case VObjectType::slDot: {
          NodeId Identifier = fC->Sibling(child);
          ref_obj *ref = s.MakeRef_obj();
          ref->VpiName(fC->SymName(Identifier));
          ref->VpiParent(pexpr);
          fC->populateCoreMembers(Identifier, Identifier, ref);
          result = ref;
          break;
        }
        case VObjectType::slConstant_mintypmax_expression:
        case VObjectType::slMintypmax_expression: {
          NodeId Expression = fC->Child(child);
          NodeId Sibling = fC->Sibling(Expression);
          if (!Sibling) {
            NodeId Constant_primary = fC->Child(Expression);
            NodeId Constant_expression = fC->Child(Constant_primary);
            NodeId TmpSibling = fC->Sibling(Constant_expression);
            if (TmpSibling &&
                (fC->Type(TmpSibling) == VObjectType::slConstant_expression)) {
              Sibling = TmpSibling;
              Expression = Constant_primary;
            }
          }
          if (Sibling) {
            operation *op = s.MakeOperation();
            op->VpiOpType(vpiMinTypMaxOp);
            op->VpiParent(pexpr);
            fC->populateCoreMembers(parent, parent, op);
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            op->Operands(operands);
            result = op;
            expr *cExpr = (expr *)compileExpression(component, fC, Expression,
                                                    compileDesign, reduce, op,
                                                    instance, muteErrors);
            if (cExpr) operands->push_back(cExpr);
            while (Sibling) {
              expr *sExpr = (expr *)compileExpression(component, fC, Sibling,
                                                      compileDesign, reduce, op,
                                                      instance, muteErrors);
              if (sExpr) operands->push_back(sExpr);
              Sibling = fC->Sibling(Sibling);
            }
          } else {
            result = (expr *)compileExpression(component, fC, Expression,
                                               compileDesign, reduce, pexpr,
                                               instance, muteErrors);
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
            operation *op = s.MakeOperation();
            op->VpiOpType(vpiListOp);
            op->VpiParent(pexpr);
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            op->Operands(operands);
            result = op;
            expr *cExpr = (expr *)compileExpression(
                component, fC, fC->Child(child), compileDesign, reduce, op,
                instance, muteErrors);
            if (cExpr) operands->push_back(cExpr);
            while (Sibling) {
              expr *sExpr = (expr *)compileExpression(component, fC, Sibling,
                                                      compileDesign, reduce, op,
                                                      instance, muteErrors);
              if (sExpr) operands->push_back(sExpr);
              Sibling = fC->Sibling(Sibling);
            }
          } else {
            result = (expr *)compileExpression(component, fC, fC->Child(child),
                                               compileDesign, reduce, pexpr,
                                               instance, muteErrors);
          }
          break;
        }
        case VObjectType::slTagged: {
          NodeId Identifier = fC->Sibling(child);
          NodeId Expression = fC->Sibling(Identifier);
          UHDM::tagged_pattern *pattern = s.MakeTagged_pattern();
          pattern->VpiName(fC->SymName(Identifier));
          fC->populateCoreMembers(child, child, pattern);
          if (Expression)
            pattern->Pattern(compileExpression(component, fC, Expression,
                                               compileDesign, reduce, pattern,
                                               instance, muteErrors));
          result = pattern;
          break;
        }
        case VObjectType::slEvent_expression: {
          NodeId subExpr = child;
          UHDM::any *opL =
              compileExpression(component, fC, subExpr, compileDesign, reduce,
                                pexpr, instance, muteErrors);
          result = opL;
          NodeId op = fC->Sibling(subExpr);
          UHDM::operation *operation = nullptr;
          UHDM::VectorOfany *operands = nullptr;
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
              UHDM::any *opR =
                  compileExpression(component, fC, subRExpr, compileDesign,
                                    reduce, pexpr, instance, muteErrors);
              operands->push_back(opR);
              op = fC->Sibling(subRExpr);
            } else if (fC->Type(op) == VObjectType::slComma_operator) {
              operation->VpiOpType(vpiListOp);
              NodeId subRExpr = fC->Sibling(op);
              UHDM::any *opR =
                  compileExpression(component, fC, subRExpr, compileDesign,
                                    reduce, pexpr, instance, muteErrors);
              operands->push_back(opR);
              op = fC->Sibling(subRExpr);
            }
          }
          if ((operation != nullptr) && (operation->VpiLineNo() == 0)) {
            fC->populateCoreMembers(parent, parent, operation);
          }
          break;
        }
        case VObjectType::slExpression:
        case VObjectType::slConstant_expression: {
          UHDM::any *opL =
              compileExpression(component, fC, child, compileDesign, reduce,
                                pexpr, instance, muteErrors);
          NodeId op = fC->Sibling(child);
          if ((!op) || (fC->Type(op) == VObjectType::slConstant_expression)) {
            result = opL;
            break;
          }
          VObjectType opType = fC->Type(op);
          uint32_t vopType = UhdmWriter::getVpiOpType(opType);
          if (opType == VObjectType::slQmark ||
              opType == VObjectType::slConditional_operator) {  // Ternary op
            if (reduce == Reduce::Yes) {
              if (opL->UhdmType() == uhdmconstant) {
                UHDM::ExprEval eval;
                bool invalidValue = false;
                int64_t cond = eval.get_value(invalidValue, (expr *)opL);
                if (cond) {
                  NodeId rval = fC->Sibling(op);
                  result =
                      compileExpression(component, fC, rval, compileDesign,
                                        reduce, pexpr, instance, muteErrors);
                  break;
                } else {
                  NodeId rval = fC->Sibling(op);
                  rval = fC->Sibling(rval);
                  result =
                      compileExpression(component, fC, rval, compileDesign,
                                        reduce, pexpr, instance, muteErrors);
                  break;
                }
              }
            }
          }

          UHDM::operation *operation = s.MakeOperation();
          UHDM::VectorOfany *operands = s.MakeAnyVec();
          result = operation;
          operation->VpiParent(pexpr);
          operation->Attributes(attributes);
          if (opL) {
            setParentNoOverride(opL, operation);
            operands->push_back(opL);
          }
          if (vopType == 0) {
            result = nullptr;
          }
          operation->VpiOpType(vopType);

          operation->Operands(operands);
          NodeId rval = fC->Sibling(op);

          if (fC->Type(rval) == VObjectType::slAttribute_instance) {
            UHDM::VectorOfattribute *attributes =
                compileAttributes(component, fC, rval, compileDesign);
            while (fC->Type(rval) == VObjectType::slAttribute_instance)
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
              UHDM::any *exp =
                  compileExpression(component, fC, Expression, compileDesign,
                                    reduce, pexpr, instance, muteErrors);
              if (exp) operands->push_back(exp);
              Expression = fC->Sibling(Expression);
            }
            // RHS is done, skip handling below
            break;
          } else if (opType == VObjectType::slOpen_range_list) {
            NodeId Value_range = fC->Child(op);
            NodeId Expression = fC->Child(Value_range);
            while (Expression) {
              UHDM::any *exp =
                  compileExpression(component, fC, Expression, compileDesign,
                                    reduce, pexpr, instance, muteErrors);
              if (exp) operands->push_back(exp);
              Expression = fC->Sibling(Expression);
            }
            // RHS is done, skip handling below
            break;
          }

          UHDM::any *opR =
              compileExpression(component, fC, rval, compileDesign, reduce,
                                operation, instance, muteErrors);
          if (opR) {
            setParentNoOverride(opR, operation);
            operands->push_back(opR);
          }
          if (opType == VObjectType::slQmark ||
              opType == VObjectType::slConditional_operator) {  // Ternary op
            rval = fC->Sibling(rval);
            opR = compileExpression(component, fC, rval, compileDesign, reduce,
                                    operation, instance, muteErrors);
            if (opR) {
              setParentNoOverride(opR, operation);
              operands->push_back(opR);
            }
          }
          fC->populateCoreMembers(child, rval, operation);
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
          const std::string_view name = fC->SymName(n);
          if (name == "$bits") {
            NodeId List_of_arguments = fC->Sibling(child);
            result =
                compileBits(component, fC, List_of_arguments, compileDesign,
                            reduce, pexpr, instance, false, muteErrors);
          } else if (name == "$size") {
            NodeId List_of_arguments = fC->Sibling(child);
            result =
                compileBits(component, fC, List_of_arguments, compileDesign,
                            reduce, pexpr, instance, true, muteErrors);
          } else if (name == "$high" || name == "$low" || name == "$left" ||
                     name == "$right") {
            NodeId List_of_arguments = fC->Sibling(child);
            result =
                compileBound(component, fC, List_of_arguments, compileDesign,
                             reduce, pexpr, instance, muteErrors, name);
          } else if (name == "$clog2") {
            NodeId List_of_arguments = fC->Sibling(child);
            result =
                compileClog2(component, fC, List_of_arguments, compileDesign,
                             reduce, pexpr, instance, muteErrors);
          } else if (name == "$typename") {
            NodeId List_of_arguments = fC->Sibling(child);
            result = compileTypename(component, fC, List_of_arguments,
                                     compileDesign, reduce, pexpr, instance);
          } else {
            UHDM::sys_func_call *sys = s.MakeSys_func_call();
            sys->VpiName(name);
            sys->VpiParent(pexpr);
            NodeId argListNode = fC->Sibling(child);
            VectorOfany *arguments = compileTfCallArguments(
                component, fC, argListNode, compileDesign, reduce, sys,
                instance, muteErrors);
            sys->Tf_call_args(arguments);
            result = sys;
          }
          break;
        }
        case VObjectType::slVariable_lvalue: {
          UHDM::any *variable =
              compileExpression(component, fC, fC->Child(child), compileDesign,
                                reduce, pexpr, instance, muteErrors);
          NodeId op = fC->Sibling(child);
          if (op) {
            fC->populateCoreMembers(child, child, variable);

            VObjectType opType = fC->Type(op);
            uint32_t vopType = UhdmWriter::getVpiOpType(opType);
            if (vopType) {
              // Post increment/decrement
              UHDM::operation *operation = s.MakeOperation();
              UHDM::VectorOfany *operands = s.MakeAnyVec();
              operation->Attributes(attributes);
              fC->populateCoreMembers(parent, parent, operation);
              operation->VpiParent(pexpr);
              operation->VpiOpType(vopType);
              operation->Operands(operands);
              operands->push_back(variable);
              variable->VpiParent(operation);
              result = operation;
              NodeId rval = fC->Sibling(op);
              if (fC->Type(rval) == VObjectType::slAttribute_instance) {
                UHDM::VectorOfattribute *attributes =
                    compileAttributes(component, fC, rval, compileDesign);
                while (fC->Type(rval) == VObjectType::slAttribute_instance)
                  rval = fC->Sibling(rval);
                operation->Attributes(attributes);
              }

            } else if (opType == VObjectType::slExpression) {
              // Assignment
              UHDM::operation *operation = s.MakeOperation();
              UHDM::VectorOfany *operands = s.MakeAnyVec();
              operation->Attributes(attributes);
              fC->populateCoreMembers(parent, parent, operation);
              operation->VpiParent(pexpr);
              operation->VpiOpType(vpiAssignmentOp);
              operation->Operands(operands);
              operands->push_back(variable);
              result = operation;

              NodeId rval = op;
              if (fC->Type(rval) == VObjectType::slAttribute_instance) {
                UHDM::VectorOfattribute *attributes =
                    compileAttributes(component, fC, rval, compileDesign);
                while (fC->Type(rval) == VObjectType::slAttribute_instance)
                  rval = fC->Sibling(rval);
                operation->Attributes(attributes);
              }

              UHDM::any *rexp =
                  compileExpression(component, fC, rval, compileDesign, reduce,
                                    pexpr, instance, muteErrors);
              operands->push_back(rexp);
            }
          } else {
            result = variable;
          }
          break;
        }
        case VObjectType::slAssignment_pattern: {
          result = compileAssignmentPattern(component, fC, child, compileDesign,
                                            reduce, pexpr, instance);
          break;
        }
        case VObjectType::slSequence_instance: {
          NodeId Ps_or_hierarchical_sequence_identifier = fC->Child(child);
          NodeId Ps_or_hierarchical_array_identifier =
              fC->Child(Ps_or_hierarchical_sequence_identifier);
          NodeId NameId = fC->Child(Ps_or_hierarchical_array_identifier);
          const std::string_view name = fC->SymName(NameId);
          sequence_inst *seqinst = s.MakeSequence_inst();
          seqinst->VpiName(name);
          NodeId Sequence_list_of_arguments =
              fC->Sibling(Ps_or_hierarchical_sequence_identifier);
          NodeId Sequence_actual_arg = fC->Child(Sequence_list_of_arguments);
          VectorOfany *args = s.MakeAnyVec();
          seqinst->Named_event_sequence_expr_groups(args);
          while (Sequence_actual_arg) {
            NodeId arg = Sequence_actual_arg;
            if (fC->Type(Sequence_actual_arg) == VObjectType::slSequence_arg) {
              arg = fC->Child(Sequence_actual_arg);
            }
            if (arg) {
              NodeId Event_expression = fC->Child(arg);
              any *exp = compileExpression(component, fC, Event_expression,
                                           compileDesign, reduce, seqinst,
                                           instance, muteErrors);
              if (exp) {
                args->push_back(exp);
              }
            } else {
              constant *c = s.MakeConstant();
              c->VpiValue("INT:0");
              c->VpiDecompile("0");
              c->VpiSize(64);
              c->VpiConstType(vpiIntConst);
              fC->populateCoreMembers(Sequence_actual_arg, Sequence_actual_arg,
                                      c);
              args->push_back(c);
            }
            Sequence_actual_arg = fC->Sibling(Sequence_actual_arg);
          }
          result = seqinst;
          break;
        }
        case VObjectType::slSequence_expr: {
          result = compileExpression(component, fC, child, compileDesign,
                                     reduce, nullptr, instance, muteErrors);
          if (NodeId oper = fC->Sibling(child)) {
            VObjectType type = fC->Type(oper);
            operation *operation = s.MakeOperation();
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            operation->Operands(operands);
            operands->push_back(result);
            int32_t operationType = UhdmWriter::getVpiOpType(type);
            if (NodeId subOp1 = fC->Child(oper)) {
              VObjectType subOp1type = fC->Type(subOp1);
              if (subOp1type == VObjectType::slPound_pound_delay) {
                if (NodeId subOp2 = fC->Sibling(subOp1)) {
                  VObjectType subOp2type = fC->Type(subOp2);
                  if (subOp2type == VObjectType::slAssociative_dimension) {
                    operationType = vpiConsecutiveRepeatOp;
                  } else if (subOp2type ==
                             VObjectType::
                                 slCycle_delay_const_range_expression) {
                    range *r = s.MakeRange();
                    NodeId lhs = fC->Child(subOp2);
                    NodeId rhs = fC->Sibling(lhs);
                    r->Left_expr((expr *)compileExpression(
                        component, fC, lhs, compileDesign, reduce, nullptr,
                        instance, muteErrors));
                    r->Right_expr((expr *)compileExpression(
                        component, fC, rhs, compileDesign, reduce, nullptr,
                        instance, muteErrors));
                    operands->push_back(r);
                  }
                } else {
                  std::string_view val = fC->SymName(subOp1);
                  val.remove_prefix(2);
                  UHDM::constant *c = s.MakeConstant();
                  c->VpiValue(StrCat("UINT:", val));
                  c->VpiDecompile(val);
                  c->VpiSize(64);
                  c->VpiConstType(vpiUIntConst);
                  fC->populateCoreMembers(subOp1, subOp1, c);
                  operands->push_back(c);
                }
              }
            }
            operation->VpiOpType(operationType);
            any *rhs = compileExpression(component, fC, fC->Sibling(oper),
                                         compileDesign, reduce, nullptr,
                                         instance, muteErrors);
            operands->push_back(rhs);
            result = operation;
          }
          break;
        }
        case VObjectType::slConstant_cast:
        case VObjectType::slCast: {
          NodeId Casting_type = fC->Child(child);
          NodeId Simple_type = fC->Child(Casting_type);
          UHDM::any *operand = nullptr;
          if (Casting_type) {
            NodeId Expression = fC->Sibling(Casting_type);
            operand =
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, nullptr, instance, muteErrors);
          }
          if ((fC->Type(Simple_type) == VObjectType::slSigning_Unsigned) ||
              (fC->Type(Simple_type) == VObjectType::slSigning_Signed)) {
            UHDM::sys_func_call *sys = s.MakeSys_func_call();
            if (fC->Type(Simple_type) == VObjectType::slSigning_Unsigned)
              sys->VpiName("$unsigned");
            else
              sys->VpiName("$signed");
            sys->VpiParent(pexpr);
            VectorOfany *arguments = s.MakeAnyVec();
            sys->Tf_call_args(arguments);
            if (operand) {
              arguments->push_back(operand);
              operand->VpiParent(sys);
            }
            result = sys;
          } else {
            UHDM::operation *operation = s.MakeOperation();
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            operation->Attributes(attributes);
            operation->Operands(operands);
            operation->VpiOpType(vpiCastOp);
            UHDM::typespec *tps =
                compileTypespec(component, fC, Simple_type, compileDesign,
                                reduce, operation, instance, false);
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
          Value *sval = nullptr;
          if (childType == VObjectType::slPackage_scope) {
            const std::string_view packageName = fC->SymName(fC->Child(child));
            NodeId paramId = fC->Sibling(child);
            NodeId selectId = fC->Sibling(paramId);
            const std::string_view n = fC->SymName(paramId);
            name.assign(packageName).append("::").append(n);
            if (m_elabMode) {
              Package *pack =
                  compileDesign->getCompiler()->getDesign()->getPackage(
                      packageName);
              if (pack) {
                UHDM::VectorOfparam_assign *param_assigns =
                    pack->getParam_assigns();
                if (param_assigns) {
                  for (param_assign *param : *param_assigns) {
                    if (param && param->Lhs()) {
                      const std::string_view param_name =
                          param->Lhs()->VpiName();
                      if (param_name == n) {
                        if (substituteAssignedValue(param->Rhs(),
                                                    compileDesign)) {
                          ElaboratorListener listener(&s, false, true);
                          result = UHDM::clone_tree((any *)param->Rhs(), s,
                                                    &listener);
                          fC->populateCoreMembers(child, child, result);
                        }
                        break;
                      }
                    }
                  }
                }
                if (result && selectId) {
                  if (fC->Type(selectId) == VObjectType::slConstant_select) {
                    selectId = fC->Child(selectId);
                  }
                  if (fC->Child(selectId) || fC->Sibling(selectId))
                    result = compileSelectExpression(
                        component, fC, selectId, name, compileDesign, reduce,
                        pexpr, instance, muteErrors);
                }
                if (result == nullptr) sval = pack->getValue(n);
              }
            } else {
              // create ref_obj down below
            }
          } else if (childType == VObjectType::slClass_type) {
            const std::string_view packageName = fC->SymName(fC->Child(child));
            name = packageName;
            std::string n;
            if (fC->Sibling(parent)) {
              n = fC->SymName(fC->Sibling(parent));
              name += "::" + n;
            }
            Package *pack =
                compileDesign->getCompiler()->getDesign()->getPackage(
                    packageName);
            if (m_elabMode) {
              if (pack) {
                UHDM::VectorOfparam_assign *param_assigns =
                    pack->getParam_assigns();
                if (param_assigns) {
                  for (param_assign *param : *param_assigns) {
                    if (param && param->Lhs()) {
                      const std::string_view param_name =
                          param->Lhs()->VpiName();
                      if (param_name == n) {
                        if (substituteAssignedValue(param->Rhs(),
                                                    compileDesign)) {
                          ElaboratorListener listener(&s, false, true);
                          result = UHDM::clone_tree((any *)param->Rhs(), s,
                                                    &listener);
                          fC->populateCoreMembers(child, child, result);
                        }
                        break;
                      }
                    }
                  }
                }
                if (result == nullptr) sval = pack->getValue(n);
              }
            } else {
              // create ref_obj down below
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
            NodeId rhsbackup = rhs;
            while ((rhs = fC->Sibling(rhs))) {
              if (fC->Type(rhs) == VObjectType::slStringConst) {
                if (fC->Type(rhsbackup) == VObjectType::slPackage_scope) {
                  name.append("::").append(fC->SymName(rhs));
                } else {
                  name.append(".").append(fC->SymName(rhs));
                }
              } else if (fC->Type(rhs) == VObjectType::slSelect ||
                         fC->Type(rhs) == VObjectType::slConstant_select) {
                NodeId Bit_select = fC->Child(rhs);
                result = compileSelectExpression(component, fC, Bit_select,
                                                 name, compileDesign, reduce,
                                                 pexpr, instance, muteErrors);
                if (result != nullptr) {
                  fC->populateCoreMembers(rhsbackup, rhs, result);
                }
              }
              if (result) break;
            }
            if (result) break;
            if ((reduce == Reduce::Yes) && instance)
              sval = instance->getValue(name);
          }
          if (result) break;

          if (sval == nullptr || (sval && !sval->isValid())) {
            expr *complexValue = nullptr;
            if (instance) {
              ModuleInstance *inst =
                  valuedcomponenti_cast<ModuleInstance *>(instance);
              if (inst) {
                Netlist *netlist = inst->getNetlist();
                if (netlist) {
                  UHDM::VectorOfparam_assign *param_assigns =
                      netlist->param_assigns();
                  if (param_assigns) {
                    for (param_assign *param_ass : *param_assigns) {
                      if (param_ass && param_ass->Lhs()) {
                        const std::string_view param_name =
                            param_ass->Lhs()->VpiName();
                        if (param_name == name) {
                          if ((reduce == Reduce::Yes) ||
                              (param_ass->Rhs()->UhdmType() == uhdmconstant)) {
                            if (substituteAssignedValue(param_ass->Rhs(),
                                                        compileDesign)) {
                              ElaboratorListener listener(&s, false, true);
                              result = UHDM::clone_tree((any *)param_ass->Rhs(),
                                                        s, &listener);
                              fC->populateCoreMembers(child, child, result);
                              const any *lhs = param_ass->Lhs();
                              expr *res = (expr *)result;
                              const typespec *tps = nullptr;
                              if (lhs->UhdmType() == UHDM::uhdmtype_parameter) {
                                tps = ((UHDM::type_parameter *)lhs)->Typespec();
                              } else {
                                tps = ((UHDM::parameter *)lhs)->Typespec();
                              }
                              if (tps && (res->Typespec() == nullptr)) {
                                res->Typespec((UHDM::typespec *)tps);
                              }
                              break;
                            }
                          }
                        }
                      }
                    }
                  }
                }
                expr *complex = inst->getComplexValue(name);
                if (complex) {
                  complexValue = complex;
                }
              }
            }
            if (component && (result == nullptr)) {
              UHDM::VectorOfparam_assign *param_assigns =
                  component->getParam_assigns();
              if (param_assigns) {
                for (param_assign *param_ass : *param_assigns) {
                  if (param_ass && param_ass->Lhs()) {
                    const std::string_view param_name =
                        param_ass->Lhs()->VpiName();
                    bool paramFromPackage = false;
                    if ((valuedcomponenti_cast<Package *>(component)) &&
                        (reduce == Reduce::Yes)) {
                      paramFromPackage = true;
                    }
                    if (param_ass->Lhs()->UhdmType() == uhdmparameter) {
                      const parameter *tp = (parameter *)param_ass->Lhs();
                      if (!tp->VpiImported().empty()) {
                        paramFromPackage = true;
                      }
                    }
                    if (param_name == name) {
                      if ((reduce == Reduce::Yes) ||
                          (paramFromPackage &&
                           (param_ass->Rhs()->UhdmType() == uhdmconstant))) {
                        if (substituteAssignedValue(param_ass->Rhs(),
                                                    compileDesign)) {
                          if (complexValue) {
                            result = complexValue;
                          } else {
                            ElaboratorListener listener(&s, false, true);
                            result = UHDM::clone_tree((any *)param_ass->Rhs(),
                                                      s, &listener);
                            fC->populateCoreMembers(child, child, result);
                          }
                          const any *lhs = param_ass->Lhs();
                          expr *res = (expr *)result;
                          const typespec *tps = nullptr;
                          if (lhs->UhdmType() == UHDM::uhdmtype_parameter) {
                            tps = ((UHDM::type_parameter *)lhs)->Typespec();
                          } else {
                            tps = ((UHDM::parameter *)lhs)->Typespec();
                          }
                          if (tps && (res->Typespec() == nullptr)) {
                            res->Typespec((UHDM::typespec *)tps);
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
              UHDM::ref_obj *ref = s.MakeRef_obj();
              ref->VpiName(name);
              ref->VpiParent(pexpr);
              if (pexpr) {
                if (UHDM::any *var =
                        bindVariable(component, pexpr, name, compileDesign))
                  ref->Actual_group(var);
                else if (component)
                  component->needLateBinding(ref);
              } else if (instance) {
                if (UHDM::any *var =
                        bindVariable(component, instance, name, compileDesign))
                  ref->Actual_group(var);
                else if (component)
                  component->needLateBinding(ref);
              } else if (component) {
                component->needLateBinding(ref);
              }
              result = ref;
            }
          } else {
            UHDM::constant *c = s.MakeConstant();
            c->VpiValue(sval->uhdmValue());
            c->VpiDecompile(sval->decompiledValue());
            c->VpiConstType(sval->vpiValType());
            c->VpiSize(sval->getSize());
            if (sval->isSigned()) {
              int_typespec *ts = s.MakeInt_typespec();
              ts->VpiSigned(true);
              c->Typespec(ts);
            }
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
          UHDM::any *exp_slice = nullptr;
          NodeId Stream_concatenation;
          if (fC->Type(Slice_size) == VObjectType::slSlice_size) {
            NodeId Constant_expression = fC->Child(Slice_size);
            if (fC->Type(Constant_expression) == VObjectType::slSimple_type) {
              NodeId Integer_type = fC->Child(Constant_expression);
              NodeId Type = fC->Child(Integer_type);
              exp_slice =
                  compileBits(component, fC, Type, compileDesign, Reduce::Yes,
                              pexpr, instance, false, muteErrors);
            } else {
              exp_slice = compileExpression(component, fC, Constant_expression,
                                            compileDesign, reduce, pexpr,
                                            instance, muteErrors);
            }
            Stream_concatenation = fC->Sibling(Slice_size);
          } else {
            Stream_concatenation = Slice_size;
          }

          UHDM::operation *operation = s.MakeOperation();
          UHDM::VectorOfany *operands = s.MakeAnyVec();
          operation->Attributes(attributes);
          fC->populateCoreMembers(Stream_concatenation, Stream_concatenation,
                                  operation);
          result = operation;
          operation->VpiParent(pexpr);
          operation->Operands(operands);
          if (fC->Type(Stream_direction) == VObjectType::slBinOp_ShiftRight)
            operation->VpiOpType(vpiStreamLROp);
          else
            operation->VpiOpType(vpiStreamRLOp);
          if (exp_slice) operands->push_back(exp_slice);

          UHDM::operation *concat_op = s.MakeOperation();
          UHDM::VectorOfany *concat_ops = s.MakeAnyVec();
          operands->push_back(concat_op);
          concat_op->VpiParent(operation);
          concat_op->Operands(concat_ops);
          concat_op->VpiOpType(vpiConcatOp);
          fC->populateCoreMembers(parent, parent, concat_op);

          NodeId Stream_expression = fC->Child(Stream_concatenation);
          while (Stream_expression) {
            NodeId Expression = fC->Child(Stream_expression);
            UHDM::any *exp_var =
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, pexpr, instance, muteErrors);
            if (exp_var) concat_ops->push_back(exp_var);
            Stream_expression = fC->Sibling(Stream_expression);
          }
          break;
        }
        case VObjectType::slEmpty_queue: {
          UHDM::array_var *var = s.MakeArray_var();
          var->Typespec(s.MakeArray_typespec());
          var->VpiArrayType(vpiQueueArray);
          result = var;
          break;
        }
        case VObjectType::slConstant_concatenation:
        case VObjectType::slConcatenation: {
          UHDM::VectorOfany *operands = s.MakeAnyVec();
          NodeId Expression = fC->Child(child);
          UHDM::operation *operation = s.MakeOperation();
          operation->Attributes(attributes);
          result = operation;
          while (Expression) {
            UHDM::any *exp =
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, pexpr, instance, muteErrors);
            if (exp) {
              if (!exp->VpiParent()) exp->VpiParent(operation);
              operands->push_back(exp);
            }
            Expression = fC->Sibling(Expression);
          }
          operation->VpiParent(pexpr);
          operation->Operands(operands);
          operation->VpiOpType(vpiConcatOp);
          fC->populateCoreMembers(parent, parent, operation);
          break;
        }
        case VObjectType::slConstant_multiple_concatenation:
        case VObjectType::slMultiple_concatenation: {
          UHDM::operation *operation = s.MakeOperation();
          UHDM::VectorOfany *operands = s.MakeAnyVec();
          operation->Attributes(attributes);
          result = operation;
          operation->VpiParent(pexpr);
          operation->Operands(operands);
          operation->VpiOpType(vpiMultiConcatOp);
          NodeId NCopy = fC->Child(child);
          UHDM::any *exp =
              compileExpression(component, fC, NCopy, compileDesign, reduce,
                                pexpr, instance, muteErrors);
          if (exp) {
            if (!exp->VpiParent()) exp->VpiParent(operation);
            operands->push_back(exp);
          }
          NodeId Concatenation = fC->Sibling(NCopy);
          exp = compileExpression(component, fC, Concatenation, compileDesign,
                                  reduce, pexpr, instance, muteErrors);
          if (exp) {
            if (!exp->VpiParent()) exp->VpiParent(operation);
            operands->push_back(exp);
          }
          break;
        }
        case VObjectType::slSubroutine_call: {
          NodeId Dollar_keyword = fC->Child(child);
          NodeId nameId;
          if (fC->Type(Dollar_keyword) == VObjectType::slStringConst) {
            nameId = Dollar_keyword;
          } else {
            nameId = fC->Sibling(Dollar_keyword);
          }
          NodeId List_of_arguments = fC->Sibling(nameId);
          std::string name(fC->SymName(nameId));
          if (name == "bits") {
            NodeId Expression = fC->Child(List_of_arguments);
            result = compileBits(component, fC, Expression, compileDesign,
                                 reduce, pexpr, instance, false, muteErrors);
          } else if (name == "size") {
            NodeId Expression = fC->Child(List_of_arguments);
            result = compileBits(component, fC, Expression, compileDesign,
                                 reduce, pexpr, instance, true, muteErrors);
          } else if (name == "clog2") {
            result =
                compileClog2(component, fC, List_of_arguments, compileDesign,
                             reduce, pexpr, instance, muteErrors);
          } else if (name == "high" || name == "low" || name == "left" ||
                     name == "right") {
            result =
                compileBound(component, fC, List_of_arguments, compileDesign,
                             reduce, pexpr, instance, muteErrors, name);
          } else if (name == "typename") {
            result = compileTypename(component, fC, List_of_arguments,
                                     compileDesign, reduce, pexpr, instance);
          } else if (fC->Type(Dollar_keyword) == VObjectType::slStringConst ||
                     fC->Type(Dollar_keyword) == VObjectType::slClass_scope) {
            if (fC->Type(Dollar_keyword) == VObjectType::slClass_scope) {
              NodeId Class_type = fC->Child(Dollar_keyword);
              NodeId Class_type_name = fC->Child(Class_type);
              NodeId Class_scope_name = fC->Sibling(Dollar_keyword);
              name.assign(fC->SymName(Class_type_name))
                  .append("::")
                  .append(fC->SymName(Class_scope_name));
            }
            NodeId Select = fC->Sibling(Dollar_keyword);
            if (fC->Type(Select) == VObjectType::slConstant_bit_select ||
                fC->Type(Select) == VObjectType::slBit_select) {
              result = compileExpression(component, fC, Dollar_keyword,
                                         compileDesign, reduce, pexpr, instance,
                                         muteErrors);
            } else {
              bool invalidValue = false;
              UHDM::func_call *fcall = s.MakeFunc_call();
              fC->populateCoreMembers(Dollar_keyword, Dollar_keyword, fcall);
              fcall->VpiName(name);

              auto [func, actual_comp] =
                  getTaskFunc(name, component, compileDesign, instance, pexpr);
              fcall->Function(any_cast<function *>(func));
              VectorOfany *args = compileTfCallArguments(
                  component, fC, List_of_arguments, compileDesign, reduce,
                  fcall, instance, muteErrors);
              if (reduce == Reduce::Yes) {
                PathId fileId = fC->getFileId();
                uint32_t lineNumber = fC->Line(nameId);
                if (func == nullptr) {
                  ErrorContainer *errors =
                      compileDesign->getCompiler()->getErrorContainer();
                  SymbolTable *symbols =
                      compileDesign->getCompiler()->getSymbolTable();
                  Location loc(fileId, lineNumber, fC->Column(nameId),
                               symbols->registerSymbol(name));
                  Error err(ErrorDefinition::COMP_UNDEFINED_USER_FUNCTION, loc);
                  errors->addError(err);
                }
                result = EvalFunc(
                    any_cast<function *>(func), args, invalidValue,
                    (instance) ? actual_comp : component, compileDesign,
                    instance, fileId, lineNumber, pexpr);
              }
              if (result == nullptr || invalidValue == true) {
                fcall->Tf_call_args(args);
                result = fcall;
              }
            }
          } else {
            UHDM::sys_func_call *sys = s.MakeSys_func_call();
            sys->VpiName("$" + name);
            VectorOfany *arguments = compileTfCallArguments(
                component, fC, List_of_arguments, compileDesign, reduce, sys,
                instance, muteErrors);
            sys->Tf_call_args(arguments);
            result = sys;
          }
          break;
        }
        case VObjectType::slData_type:
          // When trying to evaluate type parameters
          if (m_checkForLoops) {
            m_stackLevel--;
          }
          return nullptr;
        case VObjectType::slCycle_delay_range: {
          VObjectType type = fC->Type(child);
          operation *operation = s.MakeOperation();
          UHDM::VectorOfany *operands = s.MakeAnyVec();
          operation->Operands(operands);
          int32_t operationType = UhdmWriter::getVpiOpType(type);
          if (NodeId subOp1 = fC->Child(child)) {
            VObjectType subOp1type = fC->Type(subOp1);
            if (subOp1type == VObjectType::slPound_pound_delay) {
              operationType = vpiUnaryCycleDelayOp;
              if (NodeId subOp2 = fC->Sibling(subOp1)) {
                VObjectType subOp2type = fC->Type(subOp2);
                if (subOp2type == VObjectType::slAssociative_dimension) {
                  operationType = vpiConsecutiveRepeatOp;
                } else if (subOp2type ==
                           VObjectType::slCycle_delay_const_range_expression) {
                  range *r = s.MakeRange();
                  NodeId lhs = fC->Child(subOp2);
                  NodeId rhs = fC->Sibling(lhs);
                  r->Left_expr((expr *)compileExpression(
                      component, fC, lhs, compileDesign, reduce, nullptr,
                      instance, muteErrors));
                  r->Right_expr((expr *)compileExpression(
                      component, fC, rhs, compileDesign, reduce, nullptr,
                      instance, muteErrors));
                  operands->push_back(r);
                }
              } else {
                std::string_view val = fC->SymName(subOp1);
                val.remove_prefix(2);
                UHDM::constant *c = s.MakeConstant();
                c->VpiValue(StrCat("UINT:", val));
                c->VpiDecompile(val);
                c->VpiSize(64);
                c->VpiConstType(vpiUIntConst);
                fC->populateCoreMembers(subOp1, subOp1, c);
                operands->push_back(c);
              }
            }
          }
          operation->VpiOpType(operationType);
          any *rhs = compileExpression(component, fC, fC->Sibling(child),
                                       compileDesign, reduce, nullptr, instance,
                                       muteErrors);
          operands->push_back(rhs);
          result = operation;
          break;
        }
        case VObjectType::slProperty_expr: {
          expr *subexp =
              (expr *)compileExpression(component, fC, child, compileDesign,
                                        reduce, nullptr, instance, muteErrors);
          if (NodeId sib = fC->Sibling(child)) {
            VObjectType type = fC->Type(sib);
            switch (type) {
              case VObjectType::slOR:
              case VObjectType::slAND:
              case VObjectType::slUNTIL:
              case VObjectType::slS_UNTIL:
              case VObjectType::slUNTIL_WITH:
              case VObjectType::slS_UNTIL_WITH: {
                int32_t optype = UhdmWriter::getVpiOpType(type);
                operation *oper = s.MakeOperation();
                oper->VpiOpType(optype);
                UHDM::VectorOfany *operands = s.MakeAnyVec();
                oper->Operands(operands);
                operands->push_back(subexp);
                NodeId nop = fC->Sibling(sib);
                expr *nexp = (expr *)compileExpression(
                    component, fC, nop, compileDesign, reduce, nullptr,
                    instance, muteErrors);
                operands->push_back(nexp);
                result = oper;
                break;
              }
              default:
                break;
            };
          } else {
            result = subexp;
          }
          break;
        }
        case VObjectType::slClass_scope: {
          NodeId Class_type = fC->Child(child);
          NodeId Class_type_name = fC->Child(Class_type);
          NodeId Class_scope_name = fC->Sibling(child);
          std::string name = StrCat(fC->SymName(Class_type_name),
                                    "::", fC->SymName(Class_scope_name));
          ref_obj *ref = s.MakeRef_obj();
          ref->VpiName(name);
          ref->VpiParent(pexpr);
          fC->populateCoreMembers(child, child, ref);
          result = ref;
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
          uint32_t vopType = UhdmWriter::getVpiOpType(type);
          if (vopType) {
            UHDM::operation *op = s.MakeOperation();
            op->Attributes(attributes);
            op->VpiOpType(vopType);
            op->VpiParent(pexpr);
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            if (UHDM::any *operand = compileExpression(
                    component, fC, fC->Sibling(parent), compileDesign, reduce,
                    op, instance, muteErrors)) {
              operands->push_back(operand);
            }
            op->Operands(operands);
            result = op;
          }
          break;
        }
        case VObjectType::slNull_keyword: {
          UHDM::constant *c = s.MakeConstant();
          c->VpiValue("UINT:0");
          c->VpiDecompile("0");
          c->VpiSize(64);
          c->VpiConstType(vpiNullConst);
          result = c;
          break;
        }
        case VObjectType::slDollar_keyword: {
          UHDM::constant *c = s.MakeConstant();
          c->VpiConstType(vpiUnboundedConst);
          c->VpiValue("STRING:$");
          c->VpiDecompile("$");
          c->VpiSize(1);
          result = c;
          break;
        }
        case VObjectType::slThis_keyword: {
          // TODO: To be changed to class var
          UHDM::constant *c = s.MakeConstant();
          c->VpiConstType(vpiStringConst);
          c->VpiValue("STRING:this");
          c->VpiDecompile("this");
          c->VpiSize(4);
          result = c;
          break;
        }
        case VObjectType::slSuper_keyword: {
          // TODO: To be changed to class var
          UHDM::constant *c = s.MakeConstant();
          c->VpiConstType(vpiStringConst);
          c->VpiValue("STRING:super");
          c->VpiDecompile("super");
          c->VpiSize(5);
          result = c;
          break;
        }
        case VObjectType::slThis_dot_super: {
          // TODO: To be changed to class var
          UHDM::constant *c = s.MakeConstant();
          c->VpiConstType(vpiStringConst);
          c->VpiValue("STRING:this.super");
          c->VpiDecompile("this.super");
          c->VpiSize(10);
          result = c;
          break;
        }
        case VObjectType::slConstraint_block: {
          // Empty constraint block
          UHDM::constraint *cons = s.MakeConstraint();
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
          result = compileComplexFuncCall(component, fC, parent, compileDesign,
                                          reduce, pexpr, instance, muteErrors);
          break;
        }
        case VObjectType::slArray_member_label: {
          ref_obj *ref = s.MakeRef_obj();
          ref->VpiName("default");
          ref->VpiStructMember(true);
          result = ref;
          break;
        }
        default:
          break;
      }
    }
  }

  NodeId the_node;
  if (child) {
    the_node = child;
  } else {
    the_node = parent;
  }
  if ((result == nullptr) && (muteErrors == false)) {
    VObjectType exprtype = fC->Type(the_node);
    if ((exprtype != VObjectType::slEnd)) {
      ErrorContainer *errors =
          compileDesign->getCompiler()->getErrorContainer();
      SymbolTable *symbols = compileDesign->getCompiler()->getSymbolTable();
      unsupported_expr *exp = s.MakeUnsupported_expr();
      std::string lineText;
      fileSystem->readLine(fC->getFileId(), fC->Line(the_node), lineText);
      Location loc(fC->getFileId(the_node), fC->Line(the_node),
                   fC->Column(the_node),
                   symbols->registerSymbol(
                       StrCat("<", fC->printObject(the_node), "> ", lineText)));
      Error err(ErrorDefinition::UHDM_UNSUPPORTED_EXPR, loc);
      errors->addError(err);
      exp->VpiValue(StrCat("STRING:", lineText));
      fC->populateCoreMembers(the_node, the_node, exp);
      exp->VpiParent(pexpr);
      result = exp;
    }
  }

  if ((result != nullptr) && (reduce == Reduce::Yes)) {
    // Reduce
    bool invalidValue = false;
    any *tmp = reduceExpr(result, invalidValue, component, compileDesign,
                          instance, fC->getFileId(the_node), fC->Line(the_node),
                          pexpr, muteErrors);
    if (tmp && (invalidValue == false)) {
      result = tmp;
    }
  }

  if (result && (result->VpiLineNo() == 0)) {
    if (child) {
      fC->populateCoreMembers(child, child, result);
    } else {
      fC->populateCoreMembers(parent, parent, result);
    }
  }
  if (m_checkForLoops) {
    m_stackLevel--;
  }
  return result;
}

UHDM::any *CompileHelper::compileAssignmentPattern(
    DesignComponent *component, const FileContent *fC,
    NodeId Assignment_pattern, CompileDesign *compileDesign, Reduce reduce,
    UHDM::any *pexpr, ValuedComponentI *instance) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  UHDM::operation *operation = s.MakeOperation();
  UHDM::VectorOfany *operands = s.MakeAnyVec();
  result = operation;
  operation->VpiParent(pexpr);
  operation->VpiOpType(vpiAssignmentPatternOp);
  operation->Operands(operands);

  if (component && valuedcomponenti_cast<Package *>(component)) {
    reduce = Reduce::Yes;
  } else if (instance) {
    reduce = Reduce::Yes;
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
  if (!with_key &&
      fC->Type(Structure_pattern_key) == VObjectType::slConstant_expression) {
    // '{2{1}}
    NodeId Expression = Structure_pattern_key;
    if (any *exp = compileExpression(component, fC, Expression, compileDesign,
                                     reduce, operation, instance, false)) {
      Expression = fC->Sibling(Expression);
      operands->push_back(exp);
      operation->VpiOpType(vpiMultiAssignmentPatternOp);
      UHDM::operation *concat = s.MakeOperation();
      concat->VpiOpType(vpiConcatOp);
      fC->populateCoreMembers(Expression, Expression, concat);
      operands->push_back(concat);
      concat->VpiParent(operation);
      UHDM::VectorOfany *suboperands = s.MakeAnyVec();
      concat->Operands(suboperands);
      while (Expression) {
        any *val = compileExpression(component, fC, Expression, compileDesign,
                                     reduce, operation, instance, false);
        if (val) {
          if (val->VpiParent() == nullptr) {
            val->VpiParent(concat);
          }
          suboperands->push_back(val);
        }
        Expression = fC->Sibling(Expression);
      }
    }
    return result;
  }
  while (Structure_pattern_key) {
    NodeId Expression;
    if (!with_key) {
      Expression = Structure_pattern_key;
      if (Expression) {
        // No key '{1,2,...}
        if (any *exp =
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, operation, instance, false)) {
          operands->push_back(exp);
        }
      }
    } else {
      Expression =
          fC->Sibling(Structure_pattern_key);  // With key '{a: 1, b: 2,...}

      if (Expression) {
        if (any *exp =
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, operation, instance, false)) {
          if (reduce == Reduce::Yes) {
            if (exp->UhdmType() == uhdmoperation) {
              UHDM::operation *op = (UHDM::operation *)exp;
              bool reduceMore = true;
              int32_t opType = op->VpiOpType();
              if (opType == vpiConcatOp) {
                if (op->Operands()->size() != 1) {
                  reduceMore = false;
                }
              }
              if (reduceMore) {
                bool invalidValue = false;
                any *tmp = reduceExpr(
                    exp, invalidValue, component, compileDesign, instance,
                    fileSystem->toPathId(op->VpiFile(), fC->getSymbolTable()),
                    op->VpiLineNo(), nullptr, true);
                if (invalidValue == false) {
                  exp = tmp;
                }
              }
            }
          }
          if (exp->UhdmType() == uhdmref_obj) {
            ref_obj *ref = (ref_obj *)exp;
            const std::string_view name = ref->VpiName();
            any *tmp =
                getValue(name, component, compileDesign, Reduce::Yes, instance,
                         fC->getFileId(), fC->Line(Expression), pexpr, true);
            if (tmp) {
              exp = tmp;
              if (exp->VpiLineNo() == 0) {
                fC->populateCoreMembers(Expression, Expression, exp);
              }
            }
          }
          tagged_pattern *pattern = s.MakeTagged_pattern();
          fC->populateCoreMembers(Expression, Expression, pattern);
          pattern->Pattern(exp);
          NodeId Constant_expression = fC->Child(Structure_pattern_key);
          NodeId Constant_primary = fC->Child(Constant_expression);
          if (!Constant_primary) {
            UHDM::string_typespec *tps = s.MakeString_typespec();
            if (fC->Type(Constant_expression) == VObjectType::slStringConst) {
              tps->VpiName(fC->SymName(Constant_expression));
            } else {
              tps->VpiName("default");
            }
            fC->populateCoreMembers(Constant_expression, Constant_expression,
                                    tps);
            pattern->Typespec(tps);
          } else {
            NodeId Primary_literal = Constant_primary;
            if (fC->Type(Primary_literal) != VObjectType::slPrimary_literal)
              Primary_literal = fC->Child(Constant_primary);
            pattern->Typespec(compileTypespec(component, fC, Primary_literal,
                                              compileDesign, Reduce::Yes,
                                              nullptr, instance, false));
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

bool CompileHelper::errorOnNegativeConstant(DesignComponent *component,
                                            Value *value,
                                            CompileDesign *compileDesign,
                                            ValuedComponentI *instance) {
  if (value == nullptr) return false;
  const std::string &val = value->uhdmValue();
  return errorOnNegativeConstant(component, val, compileDesign, instance,
                                 BadPathId, 0, 0);
}

bool CompileHelper::errorOnNegativeConstant(DesignComponent *component,
                                            expr *exp,
                                            CompileDesign *compileDesign,
                                            ValuedComponentI *instance) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  if (exp == nullptr) return false;
  if (exp->UhdmType() != uhdmconstant) return false;
  const std::string_view val = exp->VpiValue();
  return errorOnNegativeConstant(
      component, val, compileDesign, instance,
      fileSystem->toPathId(exp->VpiFile(),
                           compileDesign->getCompiler()->getSymbolTable()),
      exp->VpiLineNo(), exp->VpiColumnNo());
}

bool CompileHelper::errorOnNegativeConstant(DesignComponent *component,
                                            std::string_view val,
                                            CompileDesign *compileDesign,
                                            ValuedComponentI *instance,
                                            PathId fileId, uint32_t lineNo,
                                            uint16_t columnNo) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  if (val[4] == '-') {
    std::string instanceName;
    if (instance) {
      if (ModuleInstance *inst =
              valuedcomponenti_cast<ModuleInstance *>(instance)) {
        instanceName = inst->getFullPathName();
      }
    } else if (component) {
      instanceName = component->getName();
    }
    std::string message;
    StrAppend(&message, '"', instanceName, "\"\n");
    SymbolTable *symbols = compileDesign->getCompiler()->getSymbolTable();
    std::string lineText;
    fileSystem->readLine(fileId, lineNo, lineText);
    StrAppend(&message, "             text: ", lineText, "\n");
    StrAppend(&message, "             value: ", val);
    ErrorContainer *errors = compileDesign->getCompiler()->getErrorContainer();
    Location loc(fileId, lineNo, columnNo, symbols->registerSymbol(message));
    Error err(ErrorDefinition::ELAB_NEGATIVE_VALUE, loc);

    bool replay = false;
    // GDB: p replay=true
    if (replay) {
      if (instance) {
        ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(instance);
        while (inst) {
          std::cout << "Instance:" << inst->getFullPathName() << " "
                    << inst->getFileId() << "\n";
          std::cout << "Mod: " << inst->getModuleName() << " "
                    << fileSystem->toPath(
                           component->getFileContents()[0]->getFileId())
                    << "\n";

          for (const auto &ps : inst->getMappedValues()) {
            const std::string &name = ps.first;
            Value *val = ps.second.first;
            std::cout << std::string("    " + name + " = " + val->uhdmValue() +
                                     "\n");
          }
          for (const auto &ps : inst->getComplexValues()) {
            const std::string &name = ps.first;
            std::cout << std::string("    " + name + " =  complex\n");
          }
          if (inst->getNetlist() && inst->getNetlist()->param_assigns()) {
            for (auto ps : *inst->getNetlist()->param_assigns()) {
              std::cout << ps->Lhs()->VpiName() << " = "
                        << "\n";
              decompile((any *)ps->Rhs());
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

std::vector<UHDM::range *> *CompileHelper::compileRanges(
    DesignComponent *component, const FileContent *fC, NodeId Packed_dimension,
    CompileDesign *compileDesign, Reduce reduce, UHDM::any *pexpr,
    ValuedComponentI *instance, int32_t &size, bool muteErrors) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  UHDM::Serializer &s = compileDesign->getSerializer();
  VectorOfrange *ranges = nullptr;
  size = 0;
  if (Packed_dimension &&
      ((fC->Type(Packed_dimension) == VObjectType::slPacked_dimension) ||
       (fC->Type(Packed_dimension) == VObjectType::slUnpacked_dimension) ||
       (fC->Type(Packed_dimension) == VObjectType::slVariable_dimension) ||
       (fC->Type(Packed_dimension) == VObjectType::slConstant_range) ||
       (fC->Type(Packed_dimension) == VObjectType::slUnsized_dimension))) {
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
        UHDM::range *range = s.MakeRange();

        expr *lexp = any_cast<expr *>(
            compileExpression(component, fC, lexpr, compileDesign, reduce,
                              pexpr, instance, muteErrors));
        if (reduce == Reduce::Yes) {
          if (errorOnNegativeConstant(component, lexp, compileDesign,
                                      instance)) {
            bool replay = false;
            // GDB: p replay=true
            if (replay) {
              compileExpression(component, fC, lexpr, compileDesign, reduce,
                                pexpr, instance, muteErrors);
            }
          }
        }
        range->Left_expr(lexp);
        if (lexp) lexp->VpiParent(range);
        expr *rexp = any_cast<expr *>(
            compileExpression(component, fC, rexpr, compileDesign, reduce,
                              pexpr, instance, muteErrors));
        if (reduce == Reduce::Yes) {
          if (errorOnNegativeConstant(component, rexp, compileDesign,
                                      instance)) {
            bool replay = false;
            // GDB: p replay=true
            if (replay) {
              compileExpression(component, fC, rexpr, compileDesign, reduce,
                                pexpr, instance, muteErrors);
            }
          }
        }
        if (rexp) rexp->VpiParent(range);
        range->Right_expr(rexp);
        if ((lexp) && (rexp)) {
          if (reduce == Reduce::Yes) {
            UHDM::ExprEval eval;
            bool invalidValue = false;
            lexp = reduceExpr(lexp, invalidValue, component, compileDesign,
                              instance, fC->getFileId(), fC->Line(lexpr), pexpr,
                              muteErrors);
            rexp = reduceExpr(rexp, invalidValue, component, compileDesign,
                              instance, fC->getFileId(), fC->Line(rexpr), pexpr,
                              muteErrors);
            uint64_t lint = eval.get_value(invalidValue, lexp);
            uint64_t rint = eval.get_value(invalidValue, rexp);
            if (lexp) lexp->VpiParent(range);
            range->Left_expr(lexp);
            if (rexp) rexp->VpiParent(range);
            range->Right_expr(rexp);
            if (!invalidValue) {
              uint64_t tmp = (lint > rint) ? lint - rint + 1 : rint - lint + 1;
              size = size * tmp;
            }
          }
        }
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, range);
        ranges->push_back(range);
        range->VpiParent(pexpr);
      } else if (fC->Type(Constant_range) ==
                 VObjectType::slConstant_expression) {
        // Specified by size
        NodeId rexpr = Constant_range;
        UHDM::range *range = s.MakeRange();

        constant *lexpc = s.MakeConstant();
        lexpc->VpiConstType(vpiUIntConst);
        lexpc->VpiSize(64);
        lexpc->VpiValue("UINT:0");
        lexpc->VpiDecompile("0");
        fC->populateCoreMembers(rexpr, rexpr, lexpc);
        lexpc->VpiEndColumnNo(fC->Column(rexpr) + 1);
        expr *lexp = lexpc;

        range->Left_expr(lexp);
        lexp->VpiParent(range);
        if (reduce == Reduce::Yes) {
          Value *rightV = m_exprBuilder.evalExpr(fC, rexpr, instance, true);
          if (rightV->isValid()) {
            int64_t rint = rightV->getValueL();
            size = size * rint;
          }
        }

        expr *rexp = any_cast<expr *>(
            compileExpression(component, fC, rexpr, compileDesign, reduce,
                              pexpr, instance, muteErrors));
        bool associativeArray = false;
        if (rexp && rexp->UhdmType() == uhdmconstant) {
          constant *c = (constant *)rexp;
          const std::string_view val = c->VpiValue();
          if ((reduce == Reduce::Yes) &&
              ((val == "UINT:0") || (val == "INT:0") || (val[4] == '-'))) {
            ErrorContainer *errors =
                compileDesign->getCompiler()->getErrorContainer();
            SymbolTable *symbols =
                compileDesign->getCompiler()->getSymbolTable();
            std::string instanceName;
            if (instance) {
              if (ModuleInstance *inst =
                      valuedcomponenti_cast<ModuleInstance *>(instance)) {
                instanceName = inst->getFullPathName();
              }
            } else if (component) {
              instanceName = component->getName();
            }
            std::string message;
            StrAppend(&message, '"', instanceName, "\"\n");
            std::string lineText;
            fileSystem->readLine(fC->getFileId(), fC->Line(rexpr), lineText);
            StrAppend(&message, "             text: ", lineText, "\n");
            StrAppend(&message, "             value: ", val);

            Location loc(fC->getFileId(), fC->Line(rexpr), fC->Column(rexpr),
                         symbols->registerSymbol(message));
            Error err(ErrorDefinition::ELAB_ILLEGAL_ZERO_VALUE, loc);
            errors->addError(err);
          }
          if (c->VpiConstType() == vpiUnboundedConst) associativeArray = true;
        }
        if (rexp && rexp->UhdmType() == uhdmref_obj) {
          if (reduce == Reduce::Yes) {
            typespec *assoc_tps =
                compileTypespec(component, fC, rexpr, compileDesign, reduce,
                                nullptr, instance, true);
            if (assoc_tps) {
              associativeArray = true;
              UHDM::range *range = s.MakeRange();

              constant *lexpc = s.MakeConstant();
              lexpc->VpiConstType(vpiUIntConst);
              lexpc->VpiSize(64);
              lexpc->VpiValue("UINT:0");
              lexpc->VpiDecompile("0");
              fC->populateCoreMembers(Packed_dimension, Packed_dimension,
                                      lexpc);
              lexpc->VpiEndColumnNo(fC->Column(Packed_dimension) + 1);
              expr *lexp = lexpc;

              range->Left_expr(lexp);
              lexp->VpiParent(range);

              constant *rexpc = s.MakeConstant();
              rexpc->VpiConstType(vpiStringConst);
              rexpc->VpiSize(0);
              rexpc->VpiValue("STRING:associative");
              rexpc->VpiDecompile("associative");
              fC->populateCoreMembers(Packed_dimension, Packed_dimension,
                                      rexpc);
              rexpc->VpiEndColumnNo(fC->Column(Packed_dimension) + 1);

              rexpc->Typespec(assoc_tps);
              expr *rexp = rexpc;

              range->Right_expr(rexp);
              rexp->VpiParent(range);

              ranges->push_back(range);
              Packed_dimension = fC->Sibling(Packed_dimension);
              continue;
            }
          }
        }
        if (!associativeArray) {
          operation *op = s.MakeOperation();  // Decr by 1
          op->VpiOpType(vpiSubOp);
          op->Operands(s.MakeAnyVec());
          op->Operands()->push_back(rexp);
          constant *one = s.MakeConstant();
          one->VpiValue("INT:1");
          one->VpiConstType(vpiIntConst);
          one->VpiSize(64);
          op->Operands()->push_back(one);
          rexp = op;
        }

        if (rexp) rexp->VpiParent(range);
        range->Right_expr(rexp);
        fC->populateCoreMembers(Constant_range, Constant_range, range);
        ranges->push_back(range);
        range->VpiParent(pexpr);
      } else if ((fC->Type(fC->Child(Packed_dimension)) ==
                  VObjectType::slUnsized_dimension) ||
                 (fC->Type(Packed_dimension) ==
                  VObjectType::slUnsized_dimension)) {
        UHDM::range *range = s.MakeRange();
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, range);
        constant *lexpc = s.MakeConstant();
        lexpc->VpiConstType(vpiUIntConst);
        lexpc->VpiSize(64);
        lexpc->VpiValue("UINT:0");
        lexpc->VpiDecompile("0");
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, lexpc);
        lexpc->VpiEndColumnNo(fC->Column(Packed_dimension) + 1);
        expr *lexp = lexpc;

        range->Left_expr(lexp);
        lexp->VpiParent(range);

        constant *rexpc = s.MakeConstant();
        rexpc->VpiConstType(vpiStringConst);
        rexpc->VpiSize(0);
        rexpc->VpiValue("STRING:unsized");
        rexpc->VpiDecompile("unsized");
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, rexpc);
        rexpc->VpiEndColumnNo(fC->Column(Packed_dimension) + 1);
        expr *rexp = rexpc;

        range->Right_expr(rexp);
        rexp->VpiParent(range);

        ranges->push_back(range);
      } else if (fC->Type(fC->Child(Packed_dimension)) ==
                 VObjectType::slAssociative_dimension) {
        NodeId DataType = fC->Child(fC->Child(Packed_dimension));
        UHDM::range *range = s.MakeRange();

        constant *lexpc = s.MakeConstant();
        lexpc->VpiConstType(vpiUIntConst);
        lexpc->VpiSize(64);
        lexpc->VpiValue("UINT:0");
        lexpc->VpiDecompile("0");
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, lexpc);
        lexpc->VpiEndColumnNo(fC->Column(Packed_dimension) + 1);
        expr *lexp = lexpc;

        range->Left_expr(lexp);
        lexp->VpiParent(range);

        constant *rexpc = s.MakeConstant();
        rexpc->VpiConstType(vpiStringConst);
        rexpc->VpiSize(0);
        rexpc->VpiValue("STRING:associative");
        rexpc->VpiDecompile("associative");
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, rexpc);
        rexpc->VpiEndColumnNo(fC->Column(Packed_dimension) + 1);

        typespec *assoc_tps =
            compileTypespec(component, fC, DataType, compileDesign, reduce,
                            nullptr, instance, true);
        rexpc->Typespec(assoc_tps);
        expr *rexp = rexpc;

        range->Right_expr(rexp);
        rexp->VpiParent(range);

        ranges->push_back(range);
      }
      Packed_dimension = fC->Sibling(Packed_dimension);
    }
  }
  return ranges;
}

UHDM::any *CompileHelper::compilePartSelectRange(
    DesignComponent *component, const FileContent *fC, NodeId Constant_range,
    std::string_view name, CompileDesign *compileDesign, Reduce reduce,
    UHDM::any *pexpr, ValuedComponentI *instance, bool muteErrors) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  NodeId Constant_expression = fC->Child(Constant_range);
  if (fC->Type(Constant_range) == VObjectType::slConstant_range) {
    UHDM::expr *lexp =
        (expr *)compileExpression(component, fC, Constant_expression,
                                  compileDesign, Reduce::No, pexpr, instance);
    UHDM::expr *rexp = (expr *)compileExpression(
        component, fC, fC->Sibling(Constant_expression), compileDesign,
        Reduce::No, pexpr, instance);
    UHDM::part_select *part_select = s.MakePart_select();
    part_select->Left_range(lexp);
    part_select->Right_range(rexp);
    if (name == "CREATE_UNNAMED_PARENT") {
      UHDM::ref_obj *ref = s.MakeRef_obj();
      part_select->VpiParent(ref);
    } else if (!name.empty()) {
      UHDM::ref_obj *ref = s.MakeRef_obj();
      ref->VpiName(name);
      ref->VpiDefName(name);
      ref->VpiParent(pexpr);
      part_select->VpiParent(ref);
    }
    part_select->VpiConstantSelect(true);
    result = part_select;
  } else {
    // constant_indexed_range
    UHDM::expr *lexp = (expr *)compileExpression(
        component, fC, Constant_expression, compileDesign, reduce, pexpr,
        instance, muteErrors);
    NodeId op = fC->Sibling(Constant_expression);
    UHDM::expr *rexp =
        (expr *)compileExpression(component, fC, fC->Sibling(op), compileDesign,
                                  reduce, pexpr, instance, muteErrors);
    bool reduced = false;
    if ((reduce == Reduce::Yes) && (lexp->UhdmType() == uhdmconstant) &&
        (rexp->UhdmType() == uhdmconstant)) {
      if (!name.empty()) {
        any *v = getValue(name, component, compileDesign, reduce, instance,
                          fC->getFileId(), fC->Line(Constant_expression), pexpr,
                          muteErrors);
        if (v && (v->UhdmType() == uhdmconstant)) {
          constant *cv = (constant *)v;
          Value *cvv =
              m_exprBuilder.fromVpiValue(cv->VpiValue(), cv->VpiSize());
          Value *left =
              m_exprBuilder.fromVpiValue(lexp->VpiValue(), lexp->VpiSize());
          Value *range =
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
              int32_t steps = r / 4;
              l = l / 4;
              for (int32_t i = l; i < (int32_t)(l + steps); i++) {
                int32_t index = ((int32_t)val.size()) - 1 - i;
                if (index >= 0)
                  part += val[index];
                else
                  part += '0';
              }
            } else {
              int32_t steps = r / 4;
              l = l / 4;
              for (int32_t i = l; i > (int32_t)(l - steps); i--) {
                int32_t index = ((int32_t)val.size()) - 1 - i;
                if (index >= 0)
                  part += val[index];
                else
                  part += '0';
              }
            }
            if (NumUtils::parseHex(part, &res) == nullptr) {
              res = 0;
            }
          } else {
            uint64_t iv = cvv->getValueUL();
            uint64_t mask = 0;
            if (fC->Type(op) == VObjectType::slDecPartSelectOp) {
              if (l >= r) {
                for (uint64_t i = l; i > uint64_t(l - r); i--) {
                  mask |= ((uint64_t)1 << i);
                }
                res = iv & mask;
                res = res >> (l - r);
              } else {
                res = 0;
              }
            } else {
              for (uint64_t i = l; i < uint64_t(l + r); i++) {
                mask |= ((uint64_t)1 << i);
              }
              res = iv & mask;
              res = res >> l;
            }
          }

          std::string sval = "UINT:" + std::to_string(res);
          UHDM::constant *c = s.MakeConstant();
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
      UHDM::indexed_part_select *part_select = s.MakeIndexed_part_select();
      part_select->Base_expr(lexp);
      part_select->Width_expr(rexp);
      if (fC->Type(op) == VObjectType::slIncPartSelectOp)
        part_select->VpiIndexedPartSelectType(vpiPosIndexed);
      else
        part_select->VpiIndexedPartSelectType(vpiNegIndexed);
      if (name == "CREATE_UNNAMED_PARENT") {
        UHDM::ref_obj *ref = s.MakeRef_obj();
        part_select->VpiParent(ref);
      } else if (!name.empty()) {
        UHDM::ref_obj *ref = s.MakeRef_obj();
        ref->VpiName(name);
        ref->VpiDefName(name);
        ref->VpiParent(pexpr);
        part_select->VpiParent(ref);
      }
      part_select->VpiConstantSelect(true);
      result = part_select;
    }
  }
  if (result != nullptr) {
    fC->populateCoreMembers(Constant_range, Constant_range, result);
  }
  return result;
}

uint64_t CompileHelper::Bits(const UHDM::any *typespec, bool &invalidValue,
                             DesignComponent *component,
                             CompileDesign *compileDesign, Reduce reduce,
                             ValuedComponentI *instance, PathId fileId,
                             uint32_t lineNumber, bool sizeMode) {
  if (loopDetected(fileId, lineNumber, compileDesign, instance)) {
    return 0;
  }
  if (m_checkForLoops) {
    m_stackLevel++;
  }
  if (typespec) {
    const std::string_view name = typespec->VpiName();
    if (name.find("::") != std::string::npos) {
      std::vector<std::string_view> res;
      StringUtils::tokenizeMulti(name, "::", res);
      if (res.size() > 1) {
        const std::string_view packName = res[0];
        Design *design = compileDesign->getCompiler()->getDesign();
        if (Package *pack = design->getPackage(packName)) {
          component = pack;
        }
      }
    }
  }

  UHDM::GetObjectFunctor getObjectFunctor =
      [&](std::string_view name, const any *inst,
          const any *pexpr) -> UHDM::any * {
    return getObject(name, component, compileDesign, instance, pexpr);
  };
  UHDM::GetObjectFunctor getValueFunctor =
      [&](std::string_view name, const any *inst,
          const any *pexpr) -> UHDM::any * {
    return (expr *)getValue(name, component, compileDesign, Reduce::Yes,
                            instance, fileId, lineNumber, (any *)pexpr, false);
  };
  UHDM::GetTaskFuncFunctor getTaskFuncFunctor =
      [&](std::string_view name, const any *inst) -> UHDM::task_func * {
    auto ret = getTaskFunc(name, component, compileDesign, instance, nullptr);
    return ret.first;
  };
  UHDM::ExprEval eval;
  eval.setGetObjectFunctor(getObjectFunctor);
  eval.setGetValueFunctor(getValueFunctor);
  eval.setGetTaskFuncFunctor(getTaskFuncFunctor);
  if (m_exprEvalPlaceHolder == nullptr) {
    m_exprEvalPlaceHolder = compileDesign->getSerializer().MakeModule_inst();
    m_exprEvalPlaceHolder->Param_assigns(
        compileDesign->getSerializer().MakeParam_assignVec());
  } else {
    m_exprEvalPlaceHolder->Param_assigns()->erase(
        m_exprEvalPlaceHolder->Param_assigns()->begin(),
        m_exprEvalPlaceHolder->Param_assigns()->end());
  }
  uint64_t size = eval.size(typespec, invalidValue, m_exprEvalPlaceHolder,
                            nullptr, !sizeMode);
  if (m_checkForLoops) {
    m_stackLevel--;
  }
  return size;
}

const typespec *getMemberTypespec(const typespec *tpss,
                                  const std::vector<std::string> &suffixes,
                                  uint32_t index) {
  const typespec *result = nullptr;
  if (tpss == nullptr) return result;
  if (tpss->UhdmType() == uhdmstruct_typespec) {
    const struct_typespec *ts = (const struct_typespec *)tpss;
    for (typespec_member *memb : *ts->Members()) {
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

const typespec *CompileHelper::getTypespec(DesignComponent *component,
                                           const FileContent *fC, NodeId id,
                                           CompileDesign *compileDesign,
                                           Reduce reduce,
                                           ValuedComponentI *instance) {
  if (loopDetected(fC->getFileId(), fC->Line(id), compileDesign, instance)) {
    return nullptr;
  }
  UHDM::Serializer &s = compileDesign->getSerializer();
  const DataType *dtype = nullptr;
  const typespec *result = nullptr;
  std::string basename;
  std::vector<std::string> suffixnames;
  switch (fC->Type(id)) {
    case VObjectType::slIntegerAtomType_Byte: {
      result = s.MakeByte_typespec();
      break;
    }
    case VObjectType::slIntegerAtomType_Int: {
      result = s.MakeInt_typespec();
      break;
    }
    case VObjectType::slIntegerAtomType_Integer: {
      result = s.MakeInteger_typespec();
      break;
    }
    case VObjectType::slIntegerAtomType_LongInt: {
      result = s.MakeLong_int_typespec();
      break;
    }
    case VObjectType::slIntegerAtomType_Shortint: {
      result = s.MakeShort_int_typespec();
      break;
    }
    case VObjectType::slIntegerAtomType_Time: {
      result = s.MakeTime_typespec();
      break;
    }
    case VObjectType::slStringConst: {
      basename = fC->SymName(id);
      NodeId suffix = fC->Sibling(id);
      while (suffix && (fC->Type(suffix) == VObjectType::slStringConst)) {
        suffixnames.emplace_back(fC->SymName(suffix));
        suffix = fC->Sibling(suffix);
      }
      break;
    }
    case VObjectType::slComplex_func_call: {
      UHDM::any *exp =
          compileExpression(component, fC, fC->Parent(id), compileDesign,
                            reduce, nullptr, instance, false);
      if (exp) {
        if (exp->UhdmType() == uhdmhier_path) {
          bool invalidValue = false;
          result = (typespec *)decodeHierPath(
              (hier_path *)exp, invalidValue, component, compileDesign, reduce,
              instance, fC->getFileId(), fC->Line(id), nullptr, false, true);
        } else if (exp->UhdmType() == uhdmbit_select) {
          bit_select *select = (bit_select *)exp;
          basename = select->VpiName();
        } else if (exp->UhdmType() == uhdmref_obj) {
          basename = exp->VpiName();
          if (basename.find("::") != std::string::npos) {
            std::vector<std::string_view> res;
            StringUtils::tokenizeMulti(basename, "::", res);
            if (res.size() > 1) {
              const std::string_view packName = res[0];
              const std::string_view typeName = res[1];
              Package *p =
                  compileDesign->getCompiler()->getDesign()->getPackage(
                      packName);
              if (p) {
                dtype = p->getDataType(typeName);
              }
            }
          }
        } else if (exp->UhdmType() == uhdmvar_select) {
          var_select *select = (var_select *)exp;
          basename = select->VpiName();
        } else {
          basename = exp->VpiName();
        }
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
      basename.assign(fC->SymName(Class_type_name))
          .append("::")
          .append(fC->SymName(Class_scope_name));
      Package *p = compileDesign->getCompiler()->getDesign()->getPackage(
          fC->SymName(Class_type_name));
      if (p) {
        dtype = p->getDataType(fC->SymName(Class_scope_name));
      } else {
      }
      break;
    }
    case VObjectType::slPackage_scope: {
      const std::string_view packageName = fC->SymName(fC->Child(id));
      const std::string_view n = fC->SymName(fC->Sibling(id));
      basename.assign(packageName).append("::").append(n);
      Package *p =
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
    Signal *sig = nullptr;
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
                            reduce, nullptr, instance, true);
        NodeId Unpacked_dimension = sig->getUnpackedDimension();
        if (fC->Type(Unpacked_dimension) != VObjectType::sl_INVALID_) {
          array_typespec *array = s.MakeArray_typespec();
          int32_t size;
          VectorOfrange *ranges =
              compileRanges(component, fC, Unpacked_dimension, compileDesign,
                            reduce, nullptr, instance, size, false);
          array->Ranges(ranges);
          array->Elem_typespec((typespec *)result);
          result = array;
        }
      } else {
        NodeId Packed_dimension = sig->getPackedDimension();
        if (fC->Type(Packed_dimension) != VObjectType::sl_INVALID_) {
          NodeId DataType = fC->Parent(Packed_dimension);
          result = compileTypespec(component, fC, DataType, compileDesign,
                                   reduce, nullptr, instance, false);
        }
        NodeId Unpacked_dimension = sig->getUnpackedDimension();
        if (fC->Type(Unpacked_dimension) != VObjectType::sl_INVALID_) {
          array_typespec *array = s.MakeArray_typespec();
          int32_t size;
          VectorOfrange *ranges =
              compileRanges(component, fC, Unpacked_dimension, compileDesign,
                            reduce, nullptr, instance, size, false);
          array->Ranges(ranges);
          if (result == nullptr) {
            result =
                compileBuiltinTypespec(component, fC, sig->getNodeId(),
                                       sig->getType(), compileDesign, nullptr);
          }
          array->Elem_typespec((typespec *)result);
          result = array;
        }
      }
    }
  }
  while (dtype) {
    const TypeDef *typed = datatype_cast<const TypeDef *>(dtype);
    if (typed) {
      const DataType *dt = typed->getDataType();
      const Enum *en = datatype_cast<const Enum *>(dt);
      if (en) {
        result = en->getTypespec();
        break;
      }
      const Struct *st = datatype_cast<const Struct *>(dt);
      if (st) {
        result = st->getTypespec();
        if (!suffixnames.empty()) {
          result = getMemberTypespec(result, suffixnames, 0);
        }
        break;
      }
      const Union *un = datatype_cast<const Union *>(dt);
      if (un) {
        result = un->getTypespec();
        break;
      }
      const SimpleType *sit = datatype_cast<const SimpleType *>(dt);
      if (sit) {
        result = sit->getTypespec();
        break;
      }
    }
    dtype = dtype->getDefinition();
  }

  if (result == nullptr) {
    ModuleInstance *inst = valuedcomponenti_cast<ModuleInstance *>(instance);
    if (inst) {
      Netlist *netlist = inst->getNetlist();
      if (netlist) {
        if (netlist->ports()) {
          for (port *p : *netlist->ports()) {
            if (p->VpiName() == basename) {
              const typespec *tps = p->Typespec();
              if (!suffixnames.empty()) {
                result = getMemberTypespec(tps, suffixnames, 0);
              }
            }
            if (result) break;
          }
        }
        if (netlist->param_assigns()) {
          for (param_assign *pass : *netlist->param_assigns()) {
            const any *param = pass->Lhs();
            if (param->VpiName() == basename) {
              if (param->UhdmType() == uhdmparameter) {
                parameter *p = (parameter *)param;
                result = p->Typespec();
              } else {
                type_parameter *p = (type_parameter *)param;
                result = p->Typespec();
              }
              break;
            }
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

UHDM::any *CompileHelper::compileBits(
    DesignComponent *component, const FileContent *fC, NodeId List_of_arguments,
    CompileDesign *compileDesign, Reduce reduce, UHDM::any *pexpr,
    ValuedComponentI *instance, bool sizeMode, bool muteErrors) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  NodeId Expression = List_of_arguments;
  if (fC->Type(Expression) == VObjectType::slList_of_arguments) {
    Expression = fC->Child(Expression);
  } else if (fC->Type(Expression) == VObjectType::slData_type) {
    Expression = fC->Child(Expression);
  }
  NodeId typeSpecId;
  uint64_t bits = 0;
  bool invalidValue = false;
  const typespec *tps = nullptr;
  const any *exp = nullptr;
  switch (fC->Type(Expression)) {
    case VObjectType::slIntegerAtomType_Byte:
    case VObjectType::slIntegerAtomType_Int:
    case VObjectType::slIntegerAtomType_Integer:
    case VObjectType::slIntegerAtomType_LongInt:
    case VObjectType::slIntegerAtomType_Shortint:
    case VObjectType::slIntegerAtomType_Time:
    case VObjectType::slIntVec_TypeLogic:
    case VObjectType::slIntVec_TypeBit:
    case VObjectType::slIntVec_TypeReg:
      typeSpecId = Expression;
      break;
    default: {
      NodeId Primary = fC->Child(Expression);
      NodeId Primary_literal = fC->Child(Primary);
      if (fC->Type(Primary_literal) == VObjectType::slConcatenation) {
        NodeId ConcatExpression = fC->Child(Primary_literal);
        while (ConcatExpression) {
          NodeId Primary = fC->Child(ConcatExpression);
          NodeId Primary_literal = fC->Child(Primary);
          NodeId StringConst = fC->Child(Primary_literal);
          typeSpecId = StringConst;
          tps = getTypespec(component, fC, typeSpecId, compileDesign, reduce,
                            instance);
          if ((reduce == Reduce::No) && tps) {
            UHDM::ExprEval eval;
            if (eval.isFullySpecified(tps)) {
              reduce = Reduce::Yes;
            }
          }
          if ((reduce == Reduce::Yes) && tps)
            bits += Bits(tps, invalidValue, component, compileDesign, reduce,
                         instance, fC->getFileId(typeSpecId),
                         fC->Line(typeSpecId), sizeMode);
          ConcatExpression = fC->Sibling(ConcatExpression);
        }
      } else if (fC->Type(Primary_literal) ==
                 VObjectType::slComplex_func_call) {
        typeSpecId = Primary_literal;
      } else {
        NodeId StringConst = fC->Child(Primary_literal);
        typeSpecId = StringConst;
      }
    }
  }

  if (bits == 0) {
    tps =
        getTypespec(component, fC, typeSpecId, compileDesign, reduce, instance);
    if ((reduce == Reduce::No) && tps) {
      UHDM::ExprEval eval;
      if (eval.isFullySpecified(tps)) {
        reduce = Reduce::Yes;
      }
    }
    if ((reduce == Reduce::Yes) && tps)
      bits = Bits(tps, invalidValue, component, compileDesign, reduce, instance,
                  fC->getFileId(typeSpecId), fC->Line(typeSpecId), sizeMode);

    if ((reduce == Reduce::Yes) && (!tps)) {
      exp = compileExpression(component, fC, Expression, compileDesign,
                              Reduce::Yes, pexpr, instance, true);
      if (exp && typeSpecId) {
        bits =
            Bits(exp, invalidValue, component, compileDesign, reduce, instance,
                 fC->getFileId(typeSpecId), fC->Line(typeSpecId), sizeMode);
      }
    }
  }

  if ((reduce == Reduce::Yes) && tps && (!invalidValue)) {
    UHDM::constant *c = s.MakeConstant();
    c->VpiValue("UINT:" + std::to_string(bits));
    c->VpiDecompile(std::to_string(bits));
    c->VpiConstType(vpiUIntConst);
    c->VpiSize(64);
    result = c;
  } else if ((reduce == Reduce::Yes) && exp && (!invalidValue)) {
    UHDM::constant *c = s.MakeConstant();
    c->VpiValue("UINT:" + std::to_string(bits));
    c->VpiDecompile(std::to_string(bits));
    c->VpiConstType(vpiUIntConst);
    c->VpiSize(64);
    result = c;
  } else if (sizeMode) {
    UHDM::sys_func_call *sys = s.MakeSys_func_call();
    sys->VpiName("$size");
    VectorOfany *arguments =
        compileTfCallArguments(component, fC, List_of_arguments, compileDesign,
                               reduce, sys, instance, muteErrors);
    sys->Tf_call_args(arguments);
    result = sys;
  } else {
    UHDM::sys_func_call *sys = s.MakeSys_func_call();
    sys->VpiName("$bits");
    VectorOfany *arguments =
        compileTfCallArguments(component, fC, List_of_arguments, compileDesign,
                               reduce, sys, instance, muteErrors);
    sys->Tf_call_args(arguments);
    result = sys;
  }

  return result;
}

UHDM::any *CompileHelper::compileTypename(DesignComponent *component,
                                          const FileContent *fC,
                                          NodeId Expression,
                                          CompileDesign *compileDesign,
                                          Reduce reduce, UHDM::any *pexpr,
                                          ValuedComponentI *instance) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  UHDM::constant *c = s.MakeConstant();
  if (fC->Type(Expression) == VObjectType::slData_type) {
    Expression = fC->Child(Expression);
    if (fC->Type(Expression) == VObjectType::slVirtual)
      Expression = fC->Sibling(Expression);
  }
  VObjectType type = fC->Type(Expression);
  switch (type) {
    case VObjectType::slIntVec_TypeLogic:
      c->VpiValue("STRING:logic");
      c->VpiDecompile("logic");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::slIntVec_TypeBit:
      c->VpiValue("STRING:bit");
      c->VpiDecompile("bit");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::slIntVec_TypeReg:
      c->VpiValue("STRING:reg");
      c->VpiDecompile("reg");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::slIntegerAtomType_Byte:
      c->VpiValue("STRING:byte");
      c->VpiDecompile("byte");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::slIntegerAtomType_Shortint:
      c->VpiValue("STRING:shortint");
      c->VpiDecompile("shortint");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::slIntegerAtomType_Int:
      c->VpiValue("STRING:int");
      c->VpiDecompile("int");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::slIntegerAtomType_Integer:
      c->VpiValue("STRING:integer");
      c->VpiDecompile("integer");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::slIntegerAtomType_LongInt:
      c->VpiValue("STRING:longint");
      c->VpiDecompile("longint");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::slIntegerAtomType_Time:
      c->VpiValue("STRING:time");
      c->VpiDecompile("time");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::slNonIntType_ShortReal:
      c->VpiValue("STRING:shortreal");
      c->VpiDecompile("shortreal");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::slNonIntType_Real:
      c->VpiValue("STRING:real");
      c->VpiDecompile("real");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::slNonIntType_RealTime:
      c->VpiValue("STRING:realtime");
      c->VpiDecompile("realtime");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    default:
      UHDM::sys_func_call *sys = s.MakeSys_func_call();
      sys->VpiName("$typename");
      result = sys;
      const std::string_view arg = fC->SymName(Expression);
      c->VpiValue(StrCat("STRING:", arg));
      c->VpiDecompile(arg);
      c->VpiConstType(vpiStringConst);
      c->VpiParent(sys);
      break;
  }
  return result;
}

UHDM::any *CompileHelper::compileBound(
    DesignComponent *component, const FileContent *fC, NodeId List_of_arguments,
    CompileDesign *compileDesign, Reduce reduce, UHDM::any *pexpr,
    ValuedComponentI *instance, bool muteErrors, std::string_view name) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  NodeId Expression = List_of_arguments;
  if (fC->Type(Expression) == VObjectType::slList_of_arguments) {
    Expression = fC->Child(Expression);
  }
  expr *operand =
      (expr *)compileExpression(component, fC, Expression, compileDesign,
                                Reduce::No, pexpr, instance, muteErrors);
  if (operand) {
    const typespec *ts = operand->Typespec();
    VectorOfrange *ranges = nullptr;
    if (ts) {
      switch (ts->UhdmType()) {
        case uhdmbit_typespec: {
          bit_typespec *bts = (bit_typespec *)ts;
          ranges = bts->Ranges();
          break;
        }
        case uhdmint_typespec: {
          int_typespec *bts = (int_typespec *)ts;
          ranges = bts->Ranges();
          break;
        }
        case uhdmlogic_typespec: {
          logic_typespec *bts = (logic_typespec *)ts;
          ranges = bts->Ranges();
          break;
        }
        case uhdmarray_typespec: {
          array_typespec *bts = (array_typespec *)ts;
          ranges = bts->Ranges();
          break;
        }
        case uhdmpacked_array_typespec: {
          packed_array_typespec *bts = (packed_array_typespec *)ts;
          ranges = bts->Ranges();
          break;
        }
        default:
          break;
      }
    }
    if (ranges) {
      range *r = ranges->at(0);
      expr *lr = (expr *)r->Left_expr();
      expr *rr = (expr *)r->Right_expr();
      bool invalidValue = false;
      lr = reduceExpr(lr, invalidValue, component, compileDesign, instance,
                      BadPathId, 0, nullptr, true);
      UHDM::ExprEval eval;
      int64_t lrv = eval.get_value(invalidValue, lr);
      rr = reduceExpr(rr, invalidValue, component, compileDesign, instance,
                      BadPathId, 0, nullptr, true);
      int64_t rrv = eval.get_value(invalidValue, rr);
      if (name == "left") {
        return lr;
      } else if (name == "right") {
        return rr;
      } else if (name == "high") {
        if (lrv > rrv) {
          return lr;
        } else {
          return rr;
        }
      } else if (name == "low") {
        if (lrv > rrv) {
          return rr;
        } else {
          return lr;
        }
      }
    }
  }
  UHDM::sys_func_call *sys = s.MakeSys_func_call();
  sys->VpiName(StrCat("$", name));
  VectorOfany *arguments =
      compileTfCallArguments(component, fC, List_of_arguments, compileDesign,
                             reduce, sys, instance, muteErrors);
  sys->Tf_call_args(arguments);
  result = sys;
  return result;
}

UHDM::any *CompileHelper::compileClog2(
    DesignComponent *component, const FileContent *fC, NodeId List_of_arguments,
    CompileDesign *compileDesign, Reduce reduce, UHDM::any *pexpr,
    ValuedComponentI *instance, bool muteErrors) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  NodeId Expression = List_of_arguments;
  if (fC->Type(Expression) == VObjectType::slList_of_arguments) {
    Expression = fC->Child(Expression);
  }

  bool invalidValue = false;
  int64_t val = 0;
  if (reduce == Reduce::Yes) {
    expr *operand =
        (expr *)compileExpression(component, fC, Expression, compileDesign,
                                  reduce, pexpr, instance, muteErrors);
    UHDM::ExprEval eval;
    val = eval.get_value(
        invalidValue,
        reduceExpr(operand, invalidValue, component, compileDesign, instance,
                   fC->getFileId(), fC->Line(Expression), pexpr, muteErrors));
  }
  if ((reduce == Reduce::Yes) && (invalidValue == false)) {
    val = val - 1;
    uint64_t clog2 = 0;
    for (; val > 0; clog2 = clog2 + 1) {
      val = val >> 1;
    }
    UHDM::constant *c = s.MakeConstant();
    c->VpiValue("UINT:" + std::to_string(clog2));
    c->VpiDecompile(std::to_string(clog2));
    c->VpiConstType(vpiUIntConst);
    c->VpiSize(64);
    result = c;
  } else {
    UHDM::sys_func_call *sys = s.MakeSys_func_call();
    sys->VpiName("$clog2");
    VectorOfany *arguments =
        compileTfCallArguments(component, fC, List_of_arguments, compileDesign,
                               reduce, sys, instance, muteErrors);
    sys->Tf_call_args(arguments);
    result = sys;
  }
  return result;
}

UHDM::any *CompileHelper::compileComplexFuncCall(
    DesignComponent *component, const FileContent *fC, NodeId name,
    CompileDesign *compileDesign, Reduce reduce, UHDM::any *pexpr,
    ValuedComponentI *instance, bool muteErrors) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  NodeId dotedName = fC->Sibling(name);

  bool hierPath = false;
  NodeId tmp = dotedName;
  while (fC->Type(tmp) == VObjectType::slAttribute_instance) {
    tmp = fC->Sibling(tmp);
    dotedName = tmp;
  }
  NodeId List_of_arguments;
  while (tmp) {
    if (fC->Type(tmp) == VObjectType::slStringConst ||
        fC->Type(tmp) == VObjectType::slMethod_call_body ||
        fC->Type(tmp) == VObjectType::slSubroutine_call) {
      hierPath = true;
    } else if (fC->Type(tmp) == VObjectType::slList_of_arguments) {
      List_of_arguments = tmp;
    }
    tmp = fC->Sibling(tmp);
  }

  if (fC->Type(name) == VObjectType::slDollar_root_keyword) {
    hier_path *path = s.MakeHier_path();
    VectorOfany *elems = s.MakeAnyVec();
    path->Path_elems(elems);
    NodeId Dollar_root_keyword = name;
    NodeId nameId = fC->Sibling(Dollar_root_keyword);
    ref_obj *ref = s.MakeRef_obj();
    elems->push_back(ref);
    ref->VpiName("$root");
    ref->VpiFullName("$root");
    ref->VpiParent(path);
    std::string name = StrCat("$root.", fC->SymName(nameId));
    ref = s.MakeRef_obj();
    elems->push_back(ref);
    ref->VpiName(fC->SymName(nameId));
    ref->VpiFullName(fC->SymName(nameId));
    ref->VpiParent(path);
    nameId = fC->Sibling(nameId);
    while (nameId) {
      if (fC->Type(nameId) == VObjectType::slStringConst) {
        name.append(".").append(fC->SymName(nameId));
        ref = s.MakeRef_obj();
        elems->push_back(ref);
        ref->VpiName(fC->SymName(nameId));
        ref->VpiFullName(fC->SymName(nameId));
        ref->VpiParent(path);
      } else if (fC->Type(nameId) == VObjectType::slConstant_expression) {
        NodeId Constant_expresion = fC->Child(nameId);
        if (Constant_expresion) {
          name += "[";
          expr *select = (expr *)compileExpression(
              component, fC, Constant_expresion, compileDesign, reduce, pexpr,
              instance, muteErrors);
          name += select->VpiDecompile();
          name += "]";
          bit_select *sel = s.MakeBit_select();
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
    const std::string_view name = fC->SymName(nameId);
    if (name == "bits") {
      NodeId List_of_arguments = fC->Sibling(nameId);
      result = compileBits(component, fC, List_of_arguments, compileDesign,
                           reduce, pexpr, instance, false, muteErrors);
    } else if (name == "size") {
      NodeId List_of_arguments = fC->Sibling(nameId);
      result = compileBits(component, fC, List_of_arguments, compileDesign,
                           reduce, pexpr, instance, true, muteErrors);
    } else if (name == "clog2") {
      NodeId List_of_arguments = fC->Sibling(nameId);
      result = compileClog2(component, fC, List_of_arguments, compileDesign,
                            reduce, pexpr, instance, muteErrors);
    } else if (name == "high" || name == "low" || name == "left" ||
               name == "right") {
      result = compileBound(component, fC, List_of_arguments, compileDesign,
                            reduce, pexpr, instance, muteErrors, name);
    }
    if (result == nullptr) {
      NodeId List_of_arguments = fC->Sibling(nameId);
      UHDM::sys_func_call *sys = s.MakeSys_func_call();
      sys->VpiName(StrCat("$", name));
      VectorOfany *arguments = compileTfCallArguments(
          component, fC, List_of_arguments, compileDesign, reduce, sys,
          instance, muteErrors);
      sys->Tf_call_args(arguments);
      result = sys;
    }
  } else if (fC->Type(name) == VObjectType::slImplicit_class_handle) {
    NodeId Handle = fC->Child(name);
    NodeId Method = fC->Sibling(name);
    if (!Method) {
      return compileExpression(component, fC, Handle, compileDesign, reduce,
                               pexpr, instance, muteErrors);
    }
    std::string_view rootName = fC->SymName(Method);
    if (fC->Type(Handle) == VObjectType::slThis_keyword) {
      rootName = "this";
    } else if (fC->Type(Handle) == VObjectType::slSuper_keyword) {
      rootName = "super";
    } else if (fC->Type(Handle) == VObjectType::slThis_dot_super) {
      rootName = "super";
    }
    NodeId List_of_arguments = fC->Sibling(Method);
    if (fC->Type(List_of_arguments) == VObjectType::slList_of_arguments) {
      method_func_call *fcall = s.MakeMethod_func_call();
      expr *object =
          (expr *)compileExpression(component, fC, Handle, compileDesign,
                                    reduce, pexpr, instance, muteErrors);
      fcall->Prefix(object);
      const std::string_view methodName = fC->SymName(Method);
      fcall->VpiName(methodName);
      fC->populateCoreMembers(Method, Method, fcall);
      VectorOfany *arguments = compileTfCallArguments(
          component, fC, List_of_arguments, compileDesign, reduce, fcall,
          instance, muteErrors);
      fcall->Tf_call_args(arguments);
      result = fcall;
    } else if (fC->Type(List_of_arguments) ==
                   VObjectType::slConstant_expression ||
               fC->Type(List_of_arguments) == VObjectType::slSelect ||
               fC->Type(List_of_arguments) == VObjectType::slConstant_select) {
      // TODO: prefix the var_select with "this" class var
      // (this.fields[idx-1].get...)
      if (fC->Type(List_of_arguments) == VObjectType::slSelect)
        List_of_arguments = fC->Child(List_of_arguments);
      result = compileSelectExpression(component, fC, Method, rootName,
                                       compileDesign, reduce, pexpr, instance,
                                       muteErrors);
      if (result == nullptr) {
        hier_path *path = s.MakeHier_path();
        VectorOfany *elems = s.MakeAnyVec();
        path->Path_elems(elems);
        std::string fullName;
        ref_obj *r1 = s.MakeRef_obj();
        r1->VpiName(rootName);
        fullName = rootName;
        elems->push_back(r1);
        r1->VpiParent(path);
        while (Method) {
          ref_obj *r = s.MakeRef_obj();
          NodeId nameId = Method;
          if (fC->Type(nameId) ==
              VObjectType::slPs_or_hierarchical_identifier) {
            nameId = fC->Child(Method);
          }
          r->VpiName(fC->SymName(nameId));
          r->VpiParent(path);
          fullName.append(".").append(fC->SymName(nameId));
          elems->push_back(r);
          Method = fC->Sibling(Method);
          if (fC->Type(Method) != VObjectType::slStringConst) {
            break;
          }
        }
        path->VpiName(fullName);
        result = path;
      }
    } else if (fC->Type(List_of_arguments) ==
               VObjectType::slConstant_bit_select) {
      // TODO: Fill this
      method_func_call *fcall = s.MakeMethod_func_call();
      expr *object =
          (expr *)compileExpression(component, fC, Handle, compileDesign,
                                    reduce, pexpr, instance, muteErrors);
      VectorOfany *arguments = compileTfCallArguments(
          component, fC, fC->Sibling(fC->Sibling(List_of_arguments)),
          compileDesign, reduce, fcall, instance, muteErrors);
      // TODO: make name part of the prefix, get vpiName from sibling
      fcall->Prefix(object);
      fcall->VpiName(rootName);
      fC->populateCoreMembers(Method, Method, fcall);
      fcall->Tf_call_args(arguments);
      result = fcall;
    } else if (fC->Type(List_of_arguments) == VObjectType::slStringConst) {
      // TODO: this is a mockup
      constant *cvar = s.MakeConstant();
      cvar->VpiDecompile("this");
      result = cvar;
    }
  } else if (fC->Type(name) == VObjectType::slClass_scope) {
    NodeId Class_type = fC->Child(name);
    NodeId Class_type_name = fC->Child(Class_type);
    NodeId Class_scope_name = fC->Sibling(name);
    NodeId List_of_arguments = fC->Sibling(Class_scope_name);
    NodeId Bit_Select;
    if (List_of_arguments) {
      if (fC->Type(List_of_arguments) == VObjectType::slSelect) {
        Bit_Select = fC->Child(List_of_arguments);
        if (!fC->Child(Bit_Select)) {
          List_of_arguments = InvalidNodeId;
        }
      }
    }

    const std::string_view packagename = fC->SymName(Class_type_name);
    const std::string_view functionname = fC->SymName(Class_scope_name);
    std::string basename = StrCat(packagename, "::", functionname);
    tf_call *call = nullptr;
    std::pair<task_func *, DesignComponent *> ret =
        getTaskFunc(basename, component, compileDesign, instance, pexpr);
    task_func *tf = ret.first;
    if (tf) {
      if (tf->UhdmType() == uhdmfunction) {
        func_call *fcall = s.MakeFunc_call();
        fcall->Function(any_cast<function *>(tf));
        call = fcall;
      } else {
        task_call *tcall = s.MakeTask_call();
        tcall->Task(any_cast<task *>(tf));
        call = tcall;
      }
      fC->populateCoreMembers(Class_type_name, Class_type_name, call);
    }
    Design *design = compileDesign->getCompiler()->getDesign();
    Package *pack = design->getPackage(packagename);
    if (call == nullptr) {
      if (pack && !List_of_arguments) {
        Value *val = pack->getValue(functionname);
        if (val && val->isValid()) {
          if (Bit_Select) {
            if (fC->Type(Bit_Select) == VObjectType::slConstant_select) {
              Bit_Select = fC->Child(Bit_Select);
            }
            any *tmpResult = compileSelectExpression(
                component, fC, Bit_Select, basename, compileDesign, reduce,
                pexpr, instance, muteErrors);
            if (tmpResult) return tmpResult;
          }
          UHDM::constant *c = s.MakeConstant();
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
        for (UHDM::any *param : *pack->getParameters()) {
          if (param->VpiName() == functionname) {
            if ((fC->Type(List_of_arguments) == VObjectType::slSelect) &&
                (fC->Child(List_of_arguments))) {
              result = compileSelectExpression(
                  component, fC, fC->Child(List_of_arguments), "",
                  compileDesign, reduce, pexpr, instance, muteErrors);
              if (result)
                result->VpiParent(param);
              else
                result = param;
            } else if ((fC->Type(List_of_arguments) ==
                        VObjectType::slStringConst)) {
              hier_path *path = s.MakeHier_path();
              VectorOfany *elems = s.MakeAnyVec();
              path->Path_elems(elems);
              ref_obj *ref = s.MakeRef_obj();
              ref->VpiName(StrCat(packagename, "::", functionname));
              ref->VpiFullName(StrCat(packagename, "::", functionname));
              ref->Actual_group(param);
              ref->VpiParent(pexpr);
              fC->populateCoreMembers(name, name, ref);
              elems->push_back(ref);
              while (List_of_arguments) {
                if ((fC->Type(List_of_arguments) ==
                     VObjectType::slStringConst)) {
                  ref_obj *ref = s.MakeRef_obj();
                  ref->VpiName(fC->SymName(List_of_arguments));
                  ref->VpiParent(pexpr);
                  fC->populateCoreMembers(List_of_arguments, List_of_arguments,
                                          ref);
                  elems->push_back(ref);
                }
                List_of_arguments = fC->Sibling(List_of_arguments);
              }
              result = path;
            } else {
              ref_obj *ref = s.MakeRef_obj();
              ref->VpiName(StrCat(packagename, "::", functionname));
              ref->VpiFullName(StrCat(packagename, "::", functionname));
              ref->Actual_group(param);
              ref->VpiParent(pexpr);
              fC->populateCoreMembers(name, name, ref);
              result = ref;
            }
            break;
          }
        }
        if (result) return result;
      }
    }
    if (call != nullptr) {
      call->VpiName(basename);
      VectorOfany *arguments = compileTfCallArguments(
          component, fC, List_of_arguments, compileDesign, reduce, call,
          instance, muteErrors);
      call->Tf_call_args(arguments);
      result = call;
    } else {
      result = compileExpression(component, fC, name, compileDesign, reduce,
                                 pexpr, instance, muteErrors);
    }
  } else if (fC->Type(dotedName) == VObjectType::slSelect ||
             fC->Type(dotedName) == VObjectType::slConstant_select ||
             fC->Type(dotedName) == VObjectType::slConstant_expression ||
             fC->Type(dotedName) == VObjectType::slStringConst ||
             fC->Type(dotedName) == VObjectType::slConstant_bit_select ||
             fC->Type(dotedName) == VObjectType::slBit_select) {
    NodeId Bit_select = fC->Child(dotedName);
    const std::string_view sval = fC->SymName(name);
    NodeId selectName = fC->Sibling(dotedName);
    if (!selectName) {
      if (NodeId c = fC->Child(dotedName)) {
        if (NodeId s = fC->Sibling(c)) {
          selectName = s;
        }
      }
    }

    if (dotedName) {
      std::string the_name(fC->SymName(name));
      if (!hierPath) {
        VObjectType dtype = fC->Type(dotedName);
        if (Bit_select && (fC->Child(Bit_select) || fC->Sibling(Bit_select))) {
          result = compileSelectExpression(component, fC, Bit_select, sval,
                                           compileDesign, reduce, pexpr,
                                           instance, muteErrors);
          if (result && (result->UhdmType() == UHDM::uhdmpart_select)) {
            fC->populateCoreMembers(name, dotedName, result);
            if ((result->VpiParent() != nullptr) &&
                (result->VpiParent()->UhdmType() == UHDM::uhdmref_obj)) {
              ref_obj *const parent = (ref_obj *)result->VpiParent();
              fC->populateCoreMembers(name, name, parent);
            }
          }
          return result;
        } else if ((!selectName) &&
                   (dtype == VObjectType::slSelect ||
                    dtype == VObjectType::slConstant_bit_select ||
                    dtype == VObjectType::slBit_select ||
                    dtype == VObjectType::slConstant_select)) {
          std::string ind;
          NodeId Expression = fC->Child(Bit_select);
          expr *index = nullptr;
          if (Expression)
            index = (expr *)compileExpression(component, fC, Expression,
                                              compileDesign, Reduce::No, pexpr,
                                              instance);
          if (index) {
            bit_select *select = s.MakeBit_select();
            select->VpiIndex(index);
            the_name += decompileHelper(index);
            select->VpiFullName(the_name);
            select->VpiName(fC->SymName(name));
            select->VpiParent(pexpr);
            result = select;
          } else {
            ref_obj *ref = s.MakeRef_obj();
            ref->VpiName(the_name);
            ref->VpiFullName(the_name);
            ref->VpiParent(pexpr);
            result = ref;
          }
          fC->populateCoreMembers(name, name, result);
          return result;
        }
      }

      UHDM::hier_path *path = s.MakeHier_path();
      VectorOfany *elems = s.MakeAnyVec();
      if (instance && (reduce == Reduce::Yes)) {
        UHDM::any *rootValue =
            getObject(the_name, component, compileDesign, instance, pexpr);
        if (rootValue) {
          if (expr *expval = any_cast<expr *>(rootValue)) {
            path->Root_value(rootValue);
            path->Typespec((typespec *)expval->Typespec());
          } else if (UHDM::port *expval = any_cast<port *>(rootValue)) {
            path->Root_value((any *)expval->Low_conn());
          } else if (UHDM::param_assign *passign =
                         any_cast<param_assign *>(rootValue)) {
            path->Root_value((any *)passign->Rhs());
            const any *param = passign->Lhs();
            const typespec *tps = nullptr;
            if (param->UhdmType() == uhdmparameter) {
              parameter *p = (parameter *)param;
              tps = p->Typespec();
            } else {
              type_parameter *p = (type_parameter *)param;
              tps = p->Typespec();
            }
            path->Typespec((typespec *)tps);
          }
        }
      }
      std::string tmpName = the_name;
      path->Path_elems(elems);
      bool is_hierarchical = false;
      while (dotedName) {
        VObjectType dtype = fC->Type(dotedName);
        NodeId BitSelect = fC->Child(dotedName);
        if (dtype == VObjectType::slStringConst) {
          the_name.append(".").append(fC->SymName(dotedName));
          if (!tmpName.empty()) {
            ref_obj *ref = s.MakeRef_obj();
            elems->push_back(ref);
            ref->VpiName(tmpName);
            ref->VpiFullName(tmpName);
            ref->VpiParent(path);
            fC->populateCoreMembers(name, name, ref);
            tmpName.clear();
            is_hierarchical = true;
          }
          tmpName = fC->SymName(dotedName);

        } else if (dtype == VObjectType::slSelect ||
                   dtype == VObjectType::slBit_select ||
                   dtype == VObjectType::slConstant_bit_select ||
                   dtype == VObjectType::slConstant_expression) {
          std::string ind;
          while (BitSelect) {
            is_hierarchical = true;
            NodeId Expression = fC->Child(BitSelect);
            if (!Expression) {
              if (BitSelect) {
                Expression = fC->Sibling(BitSelect);
                if (Expression) {
                  BitSelect = Expression;
                  Expression = fC->Child(BitSelect);
                }
              }
            }
            if (dtype == VObjectType::slConstant_expression) {
              Expression = dotedName;
            }

            if (fC->Type(BitSelect) == VObjectType::slPart_select_range) {
              expr *select = (expr *)compilePartSelectRange(
                  component, fC, Expression, "CREATE_UNNAMED_PARENT",
                  compileDesign, reduce, nullptr, instance, muteErrors);
              // Fix start/end to include the name
              select->VpiColumnNo(fC->Column(name));
              ref_obj *parent = (ref_obj *)select->VpiParent();
              if (parent) parent->VpiName(tmpName);
              if (tmpName.empty()) {
                select->VpiParent(nullptr);
              }
              elems->push_back(select);
              the_name += decompileHelper(select);
            } else if (Expression &&
                       (fC->Type(Expression) ==
                        VObjectType::slPart_select_range) &&
                       fC->Child(Expression)) {
              expr *select = (expr *)compilePartSelectRange(
                  component, fC, fC->Child(Expression), "CREATE_UNNAMED_PARENT",
                  compileDesign, reduce, nullptr, instance, muteErrors);
              // Fix start/end to include the name
              select->VpiColumnNo(fC->Column(name));
              ref_obj *parent = (ref_obj *)select->VpiParent();
              if (parent) parent->VpiDefName(tmpName);
              elems->push_back(select);
              the_name += decompileHelper(select);
            } else if (Expression) {
              expr *index = (expr *)compileExpression(
                  component, fC, Expression, compileDesign, reduce, pexpr,
                  instance, muteErrors);
              if (index) {
                bit_select *select = s.MakeBit_select();
                elems->push_back(select);
                ref_obj *ref = s.MakeRef_obj();
                ref->VpiName(tmpName);
                ref->VpiParent(path);
                if (!tmpName.empty()) select->VpiParent(ref);
                select->VpiIndex(index);
                select->VpiName(tmpName);
                select->VpiFullName(tmpName);
                fC->populateCoreMembers(name, name, select);
                std::string indexName = decompileHelper(index);
                the_name += indexName;
                if (!tmpName.empty()) ref->VpiName(tmpName + indexName);
              }
            } else {
              ref_obj *ref = s.MakeRef_obj();
              elems->push_back(ref);
              ref->VpiName(tmpName);
              ref->VpiFullName(tmpName);
              ref->VpiParent(path);
              fC->populateCoreMembers(name, name, ref);
            }
            tmpName.clear();
            if (dtype == VObjectType::slSelect)
              BitSelect = fC->Sibling(BitSelect);
            else
              break;
          }
        }

        NodeId lookAhead = fC->Sibling(dotedName);

        if ((fC->Type(dotedName) == VObjectType::slMethod_call_body) ||
            (fC->Type(lookAhead) == VObjectType::slList_of_arguments)) {
          NodeId method_child = fC->Child(dotedName);
          method_func_call *fcall = nullptr;
          if (fC->Type(method_child) == VObjectType::slBuilt_in_method_call) {
            // vpiName: method name (Array_method_name above)
            NodeId method_name_node = fC->Child(method_child);
            if (method_name_node)
              method_name_node = fC->Child(method_name_node);
            if (method_name_node)
              method_name_node = fC->Child(method_name_node);

            std::string method_name;
            if (method_name_node) {
              method_name = fC->SymName(method_name_node);
              VObjectType calltype = fC->Type(method_name_node);
              if (calltype == VObjectType::slAnd_call) {
                method_name = "and";
              } else if (calltype == VObjectType::slOr_call) {
                method_name = "or";
              } else if (calltype == VObjectType::slXor_call) {
                method_name = "xor";
              } else if (calltype == VObjectType::slUnique_call) {
                method_name = "unique";
              }
            }

            NodeId randomize_call = fC->Child(method_child);

            if (fC->Type(randomize_call) == VObjectType::slRandomize_call) {
              fcall =
                  compileRandomizeCall(component, fC, fC->Child(randomize_call),
                                       compileDesign, pexpr);
            } else {
              fcall = s.MakeMethod_func_call();
              fcall->VpiName(method_name);
              fC->populateCoreMembers(method_name_node, method_name_node,
                                      fcall);
              NodeId list_of_arguments =
                  fC->Sibling(fC->Child(fC->Child(method_child)));
              NodeId with_conditions_node;
              if (fC->Type(list_of_arguments) ==
                  VObjectType::slList_of_arguments) {
                VectorOfany *arguments = compileTfCallArguments(
                    component, fC, list_of_arguments, compileDesign, reduce,
                    fcall, instance, muteErrors);
                fcall->Tf_call_args(arguments);
                with_conditions_node = fC->Sibling(list_of_arguments);
              } else {
                with_conditions_node = list_of_arguments;
              }
              // vpiWith: with conditions (expression in node u<62> above)
              // (not in every method, node id is 0 if missing)
              if (with_conditions_node) {
                expr *with_conditions = (expr *)compileExpression(
                    component, fC, with_conditions_node, compileDesign, reduce,
                    pexpr, instance, muteErrors);
                fcall->With(with_conditions);
              }
            }
            elems->push_back(fcall);
            tmpName.clear();
            dotedName = fC->Sibling(dotedName);
          } else {
            fcall = s.MakeMethod_func_call();
            const std::string_view methodName = fC->SymName(dotedName);
            fcall->VpiName(methodName);
            fC->populateCoreMembers(dotedName, dotedName, fcall);
            VectorOfany *arguments = compileTfCallArguments(
                component, fC, List_of_arguments, compileDesign, reduce, fcall,
                instance, muteErrors);
            fcall->Tf_call_args(arguments);
            elems->push_back(fcall);
            tmpName.clear();
            dotedName = fC->Sibling(dotedName);
          }
        }
        name = dotedName;
        if (dotedName) dotedName = fC->Sibling(dotedName);
      }
      if (is_hierarchical) {
        if (!tmpName.empty()) {
          ref_obj *ref = s.MakeRef_obj();
          elems->push_back(ref);
          ref->VpiName(tmpName);
          ref->VpiFullName(tmpName);
          ref->VpiParent(path);
          tmpName.clear();
        }
        path->VpiName(the_name);
        path->VpiFullName(the_name);
        path->VpiParent(pexpr);

        if (elems->size() == 1) {
          result = elems->at(0);
        } else {
          result = path;
        }
      } else {
        ref_obj *ref = s.MakeRef_obj();
        ref->VpiName(tmpName);
        ref->VpiParent(pexpr);
        tmpName.clear();
        result = ref;
      }
    } else if (UHDM::any *st = getValue(
                   sval, component, compileDesign, reduce, instance,
                   fC->getFileId(), fC->Line(Bit_select), pexpr, muteErrors)) {
      UHDM_OBJECT_TYPE type = st->UhdmType();
      NodeId Select = dotedName;
      if (NodeId BitSelect = fC->Child(Select)) {
        NodeId Expression = fC->Child(BitSelect);
        while (Expression) {
          expr *index = (expr *)compileExpression(component, fC, Expression,
                                                  compileDesign, reduce, pexpr,
                                                  instance, muteErrors);
          if (index && index->UhdmType() == uhdmconstant) {
            bool invalidValue = false;
            UHDM::ExprEval eval;
            uint64_t ind = (uint64_t)eval.get_value(invalidValue, index);
            if (invalidValue == false && type == uhdmoperation) {
              operation *op = (operation *)st;
              int32_t opType = op->VpiOpType();
              if (opType == vpiAssignmentPatternOp) {
                VectorOfany *operands = op->Operands();
                if (ind < operands->size()) {
                  result = operands->at(ind);
                  st = result;
                }
              } else if (opType == vpiConcatOp) {
                VectorOfany *operands = op->Operands();
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
                                         compileDesign, reduce, pexpr, instance,
                                         muteErrors);
      }
    } else {
      result = compileSelectExpression(component, fC, Bit_select, sval,
                                       compileDesign, reduce, pexpr, instance,
                                       muteErrors);
    }
    if (result == nullptr) {
      const std::string_view n = fC->SymName(name);
      ref_obj *ref = s.MakeRef_obj();
      ref->VpiName(n);
      ref->VpiParent(pexpr);
      if (pexpr) {
        if (UHDM::any *var = bindVariable(component, pexpr, n, compileDesign))
          ref->Actual_group(var);
        else if (component)
          component->needLateBinding(ref);
      } else if (instance) {
        if (UHDM::any *var =
                bindVariable(component, instance, n, compileDesign))
          ref->Actual_group(var);
        else if (component)
          component->needLateBinding(ref);
      } else if (component) {
        component->needLateBinding(ref);
      }
      result = ref;
    }
  } else if (fC->Type(dotedName) == VObjectType::slList_of_arguments) {
    result = compileTfCall(component, fC, fC->Parent(name), compileDesign);
  } else if (fC->Type(name) == VObjectType::slStringConst) {
    const std::string_view n = fC->SymName(name);
    ref_obj *ref = s.MakeRef_obj();
    ref->VpiName(n);
    ref->VpiParent(pexpr);
    if (pexpr) {
      if (UHDM::any *var = bindVariable(component, pexpr, n, compileDesign))
        ref->Actual_group(var);
      else if (component)
        component->needLateBinding(ref);
    } else if (instance) {
      if (UHDM::any *var = bindVariable(component, instance, n, compileDesign))
        ref->Actual_group(var);
      else if (component)
        component->needLateBinding(ref);
    } else if (component) {
      component->needLateBinding(ref);
    }
    result = ref;
  } else if (fC->Type(name) == VObjectType::slSubroutine_call) {
    result = compileExpression(component, fC, fC->Parent(name), compileDesign,
                               reduce, pexpr, instance, muteErrors);
  } else if (!dotedName) {
    const std::string_view the_name = fC->SymName(name);
    ref_obj *ref = s.MakeRef_obj();
    ref->VpiName(the_name);
    ref->VpiFullName(the_name);
    ref->VpiParent(pexpr);
    result = ref;
  }
  return result;
}

bool CompileHelper::parseConstant(const UHDM::constant &constant,
                                  int64_t *value) {
  std::string_view v = constant.VpiValue();
  if (v.length() <= 4) return false;  // All prefices are at least this long.

  switch (constant.VpiConstType()) {
    case vpiBinaryConst: {
      v.remove_prefix(std::string_view("BIN:").length());
      return NumUtils::parseBinary(v, value) != nullptr;
    }
    case vpiDecConst: {
      v.remove_prefix(std::string_view("DEC:").length());
      return NumUtils::parseInt64(v, value) != nullptr;
    }
    case vpiHexConst: {
      v.remove_prefix(std::string_view("HEX:").length());
      return NumUtils::parseHex(v, value) != nullptr;
    }
    case vpiOctConst: {
      v.remove_prefix(std::string_view("OCT:").length());
      return NumUtils::parseOctal(v, value) != nullptr;
    }
    case vpiIntConst: {
      v.remove_prefix(std::string_view("INT:").length());
      return NumUtils::parseInt64(v, value) != nullptr;
    }
    case vpiUIntConst: {
      v.remove_prefix(std::string_view("UINT:").length());
      return NumUtils::parseIntLenient(v, value) != nullptr;
    }
    default: {
      if (v.find("UINT:") == 0) {
        v.remove_prefix(std::string_view("UINT:").length());
        return NumUtils::parseIntLenient(v, value) != nullptr;
      } else if (v.find("INT:") == 0) {
        v.remove_prefix(std::string_view("INT:").length());
        return NumUtils::parseInt64(v, value) != nullptr;
      }
      break;
    }
  }
  return false;
}

int64_t CompileHelper::getValue(bool &validValue, DesignComponent *component,
                                const FileContent *fC, NodeId nodeId,
                                CompileDesign *compileDesign, Reduce reduce,
                                UHDM::any *pexpr, ValuedComponentI *instance,
                                bool muteErrors) {
  int64_t result = 0;
  validValue = true;
  UHDM::any *expr = compileExpression(component, fC, nodeId, compileDesign,
                                      reduce, pexpr, instance, muteErrors);
  if (expr && expr->UhdmType() == UHDM::uhdmconstant) {
    validValue = parseConstant(*(const UHDM::constant *)expr, &result);
  } else {
    validValue = false;
  }
  return result;
}

void CompileHelper::reorderAssignmentPattern(
    DesignComponent *mod, const UHDM::any *lhs, UHDM::any *rhs,
    CompileDesign *compileDesign, ValuedComponentI *instance, uint32_t level) {
  if (rhs->UhdmType() != uhdmoperation) return;
  operation *op = (operation *)rhs;
  int32_t optype = op->VpiOpType();
  if (optype == vpiConditionOp) {
    bool invalidValue = false;
    expr *tmp = reduceExpr(op, invalidValue, mod, compileDesign, instance,
                           BadPathId, 0, nullptr, true);
    if (tmp && (tmp->UhdmType() == uhdmoperation) && (invalidValue == false)) {
      op = (operation *)tmp;
      optype = op->VpiOpType();
    }
  }
  if (op->VpiReordered()) return;
  if ((optype != vpiAssignmentPatternOp) && (optype != vpiConcatOp)) return;
  VectorOfany *operands = op->Operands();
  bool ordered = true;
  for (any *operand : *operands) {
    if (operand->UhdmType() == uhdmtagged_pattern) {
      ordered = false;
      break;
    }
  }
  if (ordered) {
    if (lhs->UhdmType() == uhdmparameter) {
      parameter *p = (parameter *)lhs;
      VectorOfrange *ranges = nullptr;
      if (p->Ranges()) {
        ranges = p->Ranges();
      } else if (const typespec *tps = p->Typespec()) {
        UHDM_OBJECT_TYPE ttype = tps->UhdmType();
        if (ttype == uhdmbit_typespec) {
          ranges = ((bit_typespec *)tps)->Ranges();
        } else if (ttype == uhdmlogic_typespec) {
          ranges = ((logic_typespec *)tps)->Ranges();
        } else if (ttype == uhdmarray_typespec) {
          ranges = ((array_typespec *)tps)->Ranges();
        } else if (ttype == uhdmpacked_array_typespec) {
          ranges = ((packed_array_typespec *)tps)->Ranges();
        }
      }
      if (ranges) {
        if (level < ranges->size()) {
          range *r = ranges->at(level);
          expr *lr = (expr *)r->Left_expr();
          expr *rr = (expr *)r->Right_expr();
          bool invalidValue = false;
          UHDM::ExprEval eval;
          lr = reduceExpr(lr, invalidValue, mod, compileDesign, instance,
                          BadPathId, 0, nullptr, true);
          int64_t lrv = eval.get_value(invalidValue, lr);
          rr = reduceExpr(rr, invalidValue, mod, compileDesign, instance,
                          BadPathId, 0, nullptr, true);
          int64_t rrv = eval.get_value(invalidValue, rr);
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
  for (any *operand : *operands) {
    if (operand->UhdmType() == uhdmoperation) {
      reorderAssignmentPattern(mod, lhs, operand, compileDesign, instance,
                               level + 1);
    }
  }
}
}  // namespace SURELOG
