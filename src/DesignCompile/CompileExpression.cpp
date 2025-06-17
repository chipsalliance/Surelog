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

#include <uhdm/BaseClass.h>
#include <uhdm/expr.h>
#include <uhdm/uhdm_types.h>

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Design/DataType.h"
#include "Surelog/Design/Enum.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Netlist.h"
#include "Surelog/Design/ParamAssign.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/Design/SimpleType.h"
#include "Surelog/Design/Struct.h"
#include "Surelog/Design/TimeInfo.h"
#include "Surelog/Design/Union.h"
#include "Surelog/Design/ValuedComponentI.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/DesignCompile/UhdmWriter.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/TypeDef.h"
#include "Surelog/Utils/NumUtils.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/sv_vpi_user.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_user.h>
#include <uhdm/vpi_visitor.h>

namespace SURELOG {

bool CompileHelper::substituteAssignedValue(const uhdm::Any *oper,
                                            CompileDesign *compileDesign) {
  bool substitute = true;
  if (!oper) {
    return false;
  }
  CommandLineParser *const clp = m_session->getCommandLineParser();
  uhdm::UhdmType opType = oper->getUhdmType();
  if (opType == uhdm::UhdmType::Operation) {
    uhdm::Operation *op = (uhdm::Operation *)oper;
    int32_t opType = op->getOpType();
    if (opType == vpiAssignmentPatternOp || opType == vpiConcatOp) {
      substitute = clp->getParametersSubstitution();
    }
    for (auto operand : *op->getOperands()) {
      if (!substituteAssignedValue(operand, compileDesign)) {
        return false;
      }
    }
  }
  return substitute;
}

uhdm::Any *CompileHelper::getObject(std::string_view name,
                                    DesignComponent *component,
                                    CompileDesign *compileDesign,
                                    ValuedComponentI *instance,
                                    const uhdm::Any *pexpr) {
  Design *const design = compileDesign->getCompiler()->getDesign();
  uhdm::Any *result = nullptr;
  while (pexpr) {
    if (const uhdm::Scope *s = any_cast<uhdm::Scope>(pexpr)) {
      if ((result == nullptr) && s->getVariables()) {
        for (auto o : *s->getVariables()) {
          if (o->getName() == name) {
            result = o;
            break;
          }
        }
      }
    }
    if (const uhdm::TaskFunc *s = any_cast<uhdm::TaskFunc>(pexpr)) {
      if ((result == nullptr) && s->getIODecls()) {
        for (auto o : *s->getIODecls()) {
          if (o->getName() == name) {
            result = o;
            break;
          }
        }
      }
    }
    if (result) break;
    pexpr = pexpr->getParent();
  }
  if ((result == nullptr) && instance) {
    if (ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(instance)) {
      while (inst) {
        Netlist *netlist = inst->getNetlist();
        if (netlist) {
          if ((result == nullptr) && netlist->array_nets()) {
            for (auto o : *netlist->array_nets()) {
              if (o->getName() == name) {
                result = o;
                break;
              }
            }
          }
          if ((result == nullptr) && netlist->nets()) {
            for (auto o : *netlist->nets()) {
              if (o->getName() == name) {
                result = o;
                break;
              }
            }
          }
          if ((result == nullptr) && netlist->variables()) {
            for (auto o : *netlist->variables()) {
              if (o->getName() == name) {
                result = o;
                break;
              }
            }
          }
          if ((result == nullptr) && netlist->ports()) {
            for (auto o : *netlist->ports()) {
              if (o->getName() == name) {
                result = o;
                break;
              }
            }
          }
          if ((result == nullptr) && netlist->param_assigns()) {
            for (auto o : *netlist->param_assigns()) {
              const std::string_view pname = o->getLhs()->getName();
              if (pname == name) {
                result = o;
                break;
              }
            }
          }
        }
        if ((result == nullptr) ||
            (result && (result->getUhdmType() != uhdm::UhdmType::Constant) &&
             (result->getUhdmType() != uhdm::UhdmType::ParamAssign))) {
          if (uhdm::Expr *complex = instance->getComplexValue(name)) {
            result = complex;
          }
        }
        if (result) break;
        if (inst) {
          VObjectType insttype = inst->getType();
          if ((insttype != VObjectType::paInterface_instantiation) &&
              (insttype != VObjectType::paConditional_generate_construct) &&
              (insttype != VObjectType::paLoop_generate_construct) &&
              (insttype != VObjectType::paGenerate_item) &&
              (insttype !=
               VObjectType::paGenerate_module_conditional_statement) &&
              (insttype !=
               VObjectType::paGenerate_interface_conditional_statement) &&
              (insttype != VObjectType::paGenerate_module_loop_statement) &&
              (insttype != VObjectType::paGenerate_interface_loop_statement) &&
              (insttype != VObjectType::paGenerate_module_named_block) &&
              (insttype != VObjectType::paGenerate_interface_named_block) &&
              (insttype != VObjectType::paGenerate_module_block) &&
              (insttype != VObjectType::paGenerate_interface_block) &&
              (insttype != VObjectType::paGenerate_module_item) &&
              (insttype != VObjectType::paGenerate_interface_item) &&
              (insttype != VObjectType::paGenerate_begin_end_block)) {
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
      if (uhdm::ParamAssign *p = pass->getUhdmParamAssign()) {
        const std::string_view pname = p->getLhs()->getName();
        if (pname == name) {
          if (substituteAssignedValue(p->getRhs(), compileDesign)) {
            result = p->getRhs();
            break;
          }
        }
      }
    }
    const DataType *dtype = component->getDataType(design, name);
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
      if (sig->getTypespecId()) {
        result = compileTypespec(
            sig->getComponent(), sig->getFileContent(), sig->getTypespecId(),
            compileDesign, Reduce::No, sig->getComponent()->getUhdmModel(),
            instance, true);
      }
    }
  }

  if ((result == nullptr) && instance) {
    if (ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(instance)) {
      // Instance component
      if (DesignComponent *comp = inst->getDefinition()) {
        for (ParamAssign *pass : comp->getParamAssignVec()) {
          if (uhdm::ParamAssign *p = pass->getUhdmParamAssign()) {
            const std::string_view pname = p->getLhs()->getName();
            if (pname == name) {
              if (substituteAssignedValue(p->getRhs(), compileDesign)) {
                result = p->getRhs();
                break;
              }
            }
          }
        }

        const DataType *dtype = comp->getDataType(design, name);
        if ((result == nullptr) && dtype) {
          dtype = dtype->getActual();
          if (dtype->getTypespec()) result = dtype->getTypespec();
        }
      }
    }
  }

  if (result && (result->getUhdmType() == uhdm::UhdmType::RefObj)) {
    uhdm::RefObj *ref = (uhdm::RefObj *)result;
    const std::string_view refname = ref->getName();
    if (refname != name)
      result = getObject(refname, component, compileDesign, instance, pexpr);
    if (result) {
      if (uhdm::ParamAssign *passign = any_cast<uhdm::ParamAssign>(result)) {
        result = passign->getRhs();
      }
    }
  }
  if (result && result->getUhdmType() == uhdm::UhdmType::Constant) {
    if (instance) {
      Value *sval = instance->getValue(name);
      if (sval && sval->isValid()) {
        setRange((uhdm::Constant *)result, sval, compileDesign);
      }
    }
  }
  return result;
}

uhdm::TaskFunc *getFuncFromPackage(std::string_view name,
                                   DesignComponent *component,
                                   std::set<DesignComponent *> &visited) {
  for (Package *pack : component->getAccessPackages()) {
    if (pack->getTaskFuncs()) {
      for (uhdm::TaskFunc *tf : *pack->getTaskFuncs()) {
        if (tf->getName() == name) {
          return tf;
        }
      }
    }
    if (visited.find(pack) == visited.end()) {
      visited.insert(pack);
      uhdm::TaskFunc *res = getFuncFromPackage(name, pack, visited);
      if (res) {
        return res;
      }
    }
  }
  return nullptr;
}

std::pair<uhdm::TaskFunc *, DesignComponent *> CompileHelper::getTaskFunc(
    std::string_view name, DesignComponent *component,
    CompileDesign *compileDesign, ValuedComponentI *instance,
    uhdm::Any *pexpr) {
  Design *const design = compileDesign->getCompiler()->getDesign();
  std::pair<uhdm::TaskFunc *, DesignComponent *> result = {nullptr, nullptr};
  DesignComponent *comp = component;
  if (name.find("::") != std::string::npos) {
    std::vector<std::string_view> res;
    StringUtils::tokenizeMulti(name, "::", res);
    if (res.size() > 1) {
      const std::string_view packName = res[0];
      const std::string_view funcName = res[1];
      if (Package *pack = design->getPackage(packName)) {
        if (pack->getTaskFuncs()) {
          for (uhdm::TaskFunc *tf : *pack->getTaskFuncs()) {
            if (tf->getName() == funcName) {
              result = std::make_pair(tf, pack);
              return result;
            }
          }
        }
      }
    }
  }
  while (comp) {
    if (comp->getTaskFuncs()) {
      for (uhdm::TaskFunc *tf : *comp->getTaskFuncs()) {
        if (tf->getName() == name) {
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
      if (fC->getTaskFuncs()) {
        for (uhdm::TaskFunc *tf : *fC->getTaskFuncs()) {
          if (tf->getName() == name) {
            result = std::make_pair(tf, component);
            return result;
          }
        }
      }
    }
  }
  if (component) {
    std::set<DesignComponent *> visited;
    uhdm::TaskFunc *res = getFuncFromPackage(name, component, visited);
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
        if (def->getTaskFuncs()) {
          for (uhdm::TaskFunc *tf : *def->getTaskFuncs()) {
            if (tf->getName() == name) {
              result = std::make_pair(tf, def);
              return result;
            }
          }
        }
      }
      inst = inst->getParent();
    }
  }
  auto &all_files = design->getAllFileContents();
  for (const auto &file : all_files) {
    FileContent *fC = file.second;
    if (fC->getTaskFuncs()) {
      for (uhdm::TaskFunc *tf : *fC->getTaskFuncs()) {
        if (tf->getName() == name) {
          result = std::make_pair(tf, component);
          return result;
        }
      }
    }
  }
  return result;
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

uhdm::Constant *CompileHelper::compileConst(const FileContent *fC, NodeId child,
                                            uhdm::Serializer &s) {
  VObjectType objtype = fC->Type(child);
  uhdm::Constant *result = nullptr;
  switch (objtype) {
    case VObjectType::slIntConst: {
      // Do not evaluate the constant, keep it as in the source text:
      uhdm::Constant *c = s.make<uhdm::Constant>();
      fC->populateCoreMembers(child, child, c);
      std::string value = std::string(fC->SymName(child));
      value.erase(std::remove(value.begin(), value.end(), '_'), value.end());
      std::string v;
      c->setDecompile(value);
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
          c->setSize(-1);
        } else {
          int32_t s = 0;
          if (NumUtils::parseInt32(size, &s) == nullptr) {
            s = 0;
          }
          c->setSize(s);
        }
        if ((m_elaborate == Elaborate::Yes) && isSigned) {
          uhdm::IntTypespec *tps = s.make<uhdm::IntTypespec>();
          tps->setSigned(true);
          uhdm::RefTypespec *const rt = s.make<uhdm::RefTypespec>();
          rt->setParent(c);
          c->setTypespec(rt);
          rt->setActual(tps);
        }
        switch (base) {
          case 'h':
          case 'H': {
            v = "HEX:" + v;
            c->setConstType(vpiHexConst);
            break;
          }
          case 'b':
          case 'B': {
            v = "BIN:" + v;
            c->setConstType(vpiBinaryConst);
            break;
          }
          case 'o':
          case 'O': {
            v = "OCT:" + v;
            c->setConstType(vpiOctConst);
            break;
          }
          case 'd':
          case 'D': {
            v = "DEC:" + v;
            c->setConstType(vpiDecConst);
            break;
          }
          default: {
            v = "BIN:" + v;
            c->setConstType(vpiBinaryConst);
            break;
          }
        }
      } else {
        if (!value.empty() && value[0] == '-') {
          v.assign("INT:").append(value);
          c->setConstType(vpiIntConst);
        } else {
          v.assign("UINT:").append(value);
          c->setConstType(vpiUIntConst);
          v = StringUtils::replaceAll(v, "#", "");
        }
        c->setSize(64);
      }

      c->setValue(v);
      result = c;
      break;
    }
    case VObjectType::slRealConst: {
      uhdm::Constant *c = s.make<uhdm::Constant>();
      const std::string_view value = fC->SymName(child);
      c->setDecompile(value);
      c->setValue(StrCat("REAL:", value));
      c->setConstType(vpiRealConst);
      c->setSize(64);
      result = c;
      break;
    }
    case VObjectType::paNumber_1Tickb1:
    case VObjectType::paNumber_1TickB1:
    case VObjectType::paInitVal_1Tickb1:
    case VObjectType::paInitVal_1TickB1:
    case VObjectType::paScalar_1Tickb1:
    case VObjectType::paScalar_1TickB1:
    case VObjectType::pa1: {
      uhdm::Constant *c = s.make<uhdm::Constant>();
      std::string value = "BIN:1";
      c->setValue(value);
      c->setConstType(vpiBinaryConst);
      c->setSize(1);
      c->setDecompile("1'b1");
      fC->populateCoreMembers(child, child, c);
      result = c;
      break;
    }
    case VObjectType::paScalar_Tickb1:
    case VObjectType::paScalar_TickB1:
    case VObjectType::paNumber_Tickb1:
    case VObjectType::paNumber_TickB1: {
      uhdm::Constant *c = s.make<uhdm::Constant>();
      std::string value = "BIN:1";
      c->setValue(value);
      c->setConstType(vpiBinaryConst);
      c->setSize(0);
      c->setDecompile("'b1");
      result = c;
      break;
    }
    case VObjectType::paNumber_Tick1: {
      uhdm::Constant *c = s.make<uhdm::Constant>();
      std::string value = "BIN:1";
      c->setValue(value);
      c->setConstType(vpiBinaryConst);
      c->setSize(-1);
      c->setDecompile("'1");
      result = c;
      break;
    }
    case VObjectType::paNumber_1Tickb0:
    case VObjectType::paNumber_1TickB0:
    case VObjectType::paInitVal_1Tickb0:
    case VObjectType::paInitVal_1TickB0:
    case VObjectType::paScalar_1Tickb0:
    case VObjectType::paScalar_1TickB0:
    case VObjectType::pa0: {
      uhdm::Constant *c = s.make<uhdm::Constant>();
      std::string value = "BIN:0";
      c->setValue(value);
      c->setConstType(vpiBinaryConst);
      c->setSize(1);
      c->setDecompile("1'b0");
      fC->populateCoreMembers(child, child, c);
      result = c;
      break;
    }
    case VObjectType::paScalar_Tickb0:
    case VObjectType::paScalar_TickB0:
    case VObjectType::paNumber_Tickb0:
    case VObjectType::paNumber_TickB0: {
      uhdm::Constant *c = s.make<uhdm::Constant>();
      std::string value = "BIN:0";
      c->setValue(value);
      c->setConstType(vpiBinaryConst);
      c->setSize(0);
      c->setDecompile("'b0");
      fC->populateCoreMembers(child, child, c);
      result = c;
      break;
    }
    case VObjectType::paNumber_Tick0: {
      uhdm::Constant *c = s.make<uhdm::Constant>();
      std::string value = "BIN:0";
      c->setValue(value);
      c->setConstType(vpiBinaryConst);
      c->setSize(-1);
      c->setDecompile("'0");
      fC->populateCoreMembers(child, child, c);
      result = c;
      break;
    }
    case VObjectType::paZ: {
      uhdm::Constant *c = s.make<uhdm::Constant>();
      std::string value = "BIN:Z";
      c->setValue(value);
      c->setConstType(vpiBinaryConst);
      c->setSize(-1);
      c->setDecompile("'Z");
      result = c;
      break;
    }
    case VObjectType::paX: {
      uhdm::Constant *c = s.make<uhdm::Constant>();
      std::string value = "BIN:X";
      c->setValue(value);
      c->setConstType(vpiBinaryConst);
      c->setSize(-1);
      c->setDecompile("'X");
      result = c;
      break;
    }
    case VObjectType::paNumber_1TickBX:
    case VObjectType::paNumber_1TickbX:
    case VObjectType::paNumber_1Tickbx:
    case VObjectType::paNumber_1TickBx:
    case VObjectType::paInitVal_1Tickbx:
    case VObjectType::paInitVal_1TickbX:
    case VObjectType::paInitVal_1TickBx:
    case VObjectType::paInitVal_1TickBX: {
      uhdm::Constant *c = s.make<uhdm::Constant>();
      std::string value = "BIN:X";
      c->setValue(value);
      c->setConstType(vpiBinaryConst);
      c->setSize(1);
      c->setDecompile("1'bX");
      result = c;
      break;
    }
    case VObjectType::paTime_literal: {
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
      uhdm::Constant *c = s.make<uhdm::Constant>();
      c->setValue("UINT:" + std::to_string(val));
      c->setConstType(vpiUIntConst);
      c->setSize(64);
      result = c;
      break;
    }
    case VObjectType::slStringLiteral: {
      uhdm::Constant *c = s.make<uhdm::Constant>();
      std::string_view value = StringUtils::unquoted(fC->SymName(child));
      c->setDecompile(fC->SymName(child));
      c->setSize(value.length() * 8);
      c->setValue(StrCat("STRING:", value));
      c->setConstType(vpiStringConst);
      result = c;
      break;
    }
    default:
      break;
  }
  return result;
}

uhdm::Any *CompileHelper::decodeHierPath(
    uhdm::HierPath *path, bool &invalidValue, DesignComponent *component,
    CompileDesign *compileDesign, Reduce reduce, ValuedComponentI *instance,
    PathId fileId, uint32_t lineNumber, uhdm::Any *pexpr, bool muteErrors,
    bool returnTypespec) {
  uhdm::GetObjectFunctor getObjectFunctor =
      [&](std::string_view name, const uhdm::Any *inst,
          const uhdm::Any *pexpr) -> uhdm::Any * {
    return getObject(name, component, compileDesign, instance, pexpr);
  };
  uhdm::GetObjectFunctor getValueFunctor =
      [&](std::string_view name, const uhdm::Any *inst,
          const uhdm::Any *pexpr) -> uhdm::Any * {
    return (uhdm::Expr *)getValue(name, component, compileDesign, Reduce::Yes,
                                  instance, fileId, lineNumber,
                                  (uhdm::Any *)pexpr, false);
  };
  uhdm::GetTaskFuncFunctor getTaskFuncFunctor =
      [&](std::string_view name, const uhdm::Any *inst) -> uhdm::TaskFunc * {
    auto ret = getTaskFunc(name, component, compileDesign, instance, pexpr);
    return ret.first;
  };
  uhdm::ExprEval eval(muteErrors);
  eval.setGetObjectFunctor(getObjectFunctor);
  eval.setGetValueFunctor(getValueFunctor);
  eval.setGetTaskFuncFunctor(getTaskFuncFunctor);
  if (m_exprEvalPlaceHolder == nullptr) {
    m_exprEvalPlaceHolder = compileDesign->getSerializer().make<uhdm::Module>();
    m_exprEvalPlaceHolder->getParamAssigns(true);
  } else {
    m_exprEvalPlaceHolder->getParamAssigns()->erase(
        m_exprEvalPlaceHolder->getParamAssigns()->begin(),
        m_exprEvalPlaceHolder->getParamAssigns()->end());
  }
  uhdm::Any *res =
      eval.decodeHierPath(path, invalidValue, m_exprEvalPlaceHolder, pexpr,
                          returnTypespec, muteErrors);

  if ((res == nullptr) && (m_reduce == Reduce::Yes) &&
      (reduce == Reduce::Yes) && (!muteErrors)) {
    ErrorContainer *const errors = m_session->getErrorContainer();
    SymbolTable *const symbols = m_session->getSymbolTable();
    // std::string fileContent = FileUtils::getFileContent(fileName);
    // std::string_view lineText =
    //     StringUtils::getLineInString(fileContent, lineNumber);
    const std::string_view lineText = path->getFullName();
    Location loc(fileId, lineNumber, 0, symbols->registerSymbol(lineText));
    Error err(ErrorDefinition::UHDM_UNRESOLVED_HIER_PATH, loc);
    errors->addError(err);
  }
  return res;
}

uhdm::Expr *CompileHelper::reduceExpr(uhdm::Any *result, bool &invalidValue,
                                      DesignComponent *component,
                                      CompileDesign *compileDesign,
                                      ValuedComponentI *instance, PathId fileId,
                                      uint32_t lineNumber, uhdm::Any *pexpr,
                                      bool muteErrors) {
  if (m_reduce == Reduce::No) return any_cast<uhdm::Expr>(result);
  uhdm::GetObjectFunctor getObjectFunctor =
      [&](std::string_view name, const uhdm::Any *inst,
          const uhdm::Any *pexpr) -> uhdm::Any * {
    return getObject(name, component, compileDesign, instance, pexpr);
  };
  uhdm::GetObjectFunctor getValueFunctor =
      [&](std::string_view name, const uhdm::Any *inst,
          const uhdm::Any *pexpr) -> uhdm::Any * {
    return (uhdm::Expr *)getValue(name, component, compileDesign, Reduce::Yes,
                                  instance, fileId, lineNumber,
                                  (uhdm::Any *)pexpr, muteErrors);
  };
  uhdm::GetTaskFuncFunctor getTaskFuncFunctor =
      [&](std::string_view name, const uhdm::Any *inst) -> uhdm::TaskFunc * {
    auto ret = getTaskFunc(name, component, compileDesign, instance, pexpr);
    return ret.first;
  };
  uhdm::ExprEval eval(muteErrors);
  eval.setGetObjectFunctor(getObjectFunctor);
  eval.setGetValueFunctor(getValueFunctor);
  eval.setGetTaskFuncFunctor(getTaskFuncFunctor);
  if (m_exprEvalPlaceHolder == nullptr) {
    m_exprEvalPlaceHolder = compileDesign->getSerializer().make<uhdm::Module>();
    m_exprEvalPlaceHolder->getParamAssigns(true);
  } else {
    m_exprEvalPlaceHolder->getParamAssigns()->erase(
        m_exprEvalPlaceHolder->getParamAssigns()->begin(),
        m_exprEvalPlaceHolder->getParamAssigns()->end());
  }
  uhdm::Expr *res = eval.reduceExpr(result, invalidValue, m_exprEvalPlaceHolder,
                                    pexpr, muteErrors);
  // If loop was detected, drop the partially constructed new value!
  return m_unwind ? nullptr : res;
}

uhdm::Any *CompileHelper::getValue(std::string_view name,
                                   DesignComponent *component,
                                   CompileDesign *compileDesign, Reduce reduce,
                                   ValuedComponentI *instance, PathId fileId,
                                   uint32_t lineNumber, uhdm::Any *pexpr,
                                   bool muteErrors) {
  Design *const design = compileDesign->getCompiler()->getDesign();
  uhdm::Serializer &s = compileDesign->getSerializer();
  Value *sval = nullptr;
  uhdm::Any *result = nullptr;
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
      if (Package *pack = design->getPackage(packName)) {
        if (uhdm::Expr *val = pack->getComplexValue(varName)) {
          result = val;
          if (result && (result->getUhdmType() == uhdm::UhdmType::Operation)) {
            uhdm::Operation *op = (uhdm::Operation *)result;
            const uhdm::Typespec *opts = nullptr;
            if (uhdm::RefTypespec *rt = op->getTypespec()) {
              opts = rt->getActual();
            }
            uhdm::ExprEval eval;
            if (uhdm::Expr *res = eval.flattenPatternAssignments(
                    s, opts, (uhdm::Expr *)result)) {
              if (res->getUhdmType() == uhdm::UhdmType::Operation) {
                op->setOperands(((uhdm::Operation *)res)->getOperands());
              }
            }
          }
        }
        if (result == nullptr) {
          if (Value *sval = pack->getValue(varName)) {
            uhdm::Constant *c = s.make<uhdm::Constant>();
            c->setValue(sval->uhdmValue());
            setRange(c, sval, compileDesign);
            c->setDecompile(sval->decompiledValue());
            c->setConstType(sval->vpiValType());
            c->setSize(sval->getSize());
            result = c;
          }
        }
      }
    }
  }

  if ((result == nullptr) && instance) {
    if (uhdm::Expr *val = instance->getComplexValue(name)) {
      result = val;
      if (result->getUhdmType() == uhdm::UhdmType::Constant) {
        sval = instance->getValue(name);
        if (sval && sval->isValid()) {
          setRange((uhdm::Constant *)result, sval, compileDesign);
        }
      }
    }
    if (result == nullptr) {
      sval = instance->getValue(name);
      if (sval && sval->isValid()) {
        uhdm::Constant *c = s.make<uhdm::Constant>();
        c->setValue(sval->uhdmValue());
        setRange(c, sval, compileDesign);
        c->setDecompile(sval->decompiledValue());
        c->setConstType(sval->vpiValType());
        c->setSize(sval->getSize());
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
        uhdm::ParamAssignCollection *param_assigns = netlist->param_assigns();
        if (param_assigns) {
          for (uhdm::ParamAssign *param : *param_assigns) {
            if (param && param->getLhs()) {
              const std::string_view param_name = param->getLhs()->getName();
              if (param_name == name) {
                if (substituteAssignedValue(param->getRhs(), compileDesign)) {
                  if (param->getRhs()->getUhdmType() ==
                      uhdm::UhdmType::Operation) {
                    uhdm::Operation *op = (uhdm::Operation *)param->getRhs();
                    int32_t opType = op->getOpType();
                    if (opType == vpiAssignmentPatternOp) {
                      const uhdm::Any *lhs = param->getLhs();
                      uhdm::Any *rhs = param->getRhs();
                      const uhdm::Typespec *ts = nullptr;
                      if (lhs->getUhdmType() == uhdm::UhdmType::Parameter) {
                        if (const uhdm::RefTypespec *rt =
                                ((uhdm::Parameter *)lhs)->getTypespec()) {
                          ts = rt->getActual();
                        }
                      }
                      rhs = expandPatternAssignment(ts, (uhdm::Expr *)rhs,
                                                    component, compileDesign,
                                                    reduce, instance);
                      param->setRhs(rhs);
                      reorderAssignmentPattern(component, lhs, rhs,
                                               compileDesign, instance, 0);
                    }
                  }

                  uhdm::ElaboratorContext elaboratorContext(&s, false, true);
                  result = uhdm::clone_tree((uhdm::Any *)param->getRhs(),
                                            &elaboratorContext);
                  break;
                }
              }
            }
          }
        }
        if (auto variables = netlist->variables()) {
          for (auto var : *variables) {
            if (var->getName() == name) {
              if (const uhdm::Expr *exp = var->getExpr()) {
                uhdm::UhdmType vartype = var->getUhdmType();
                if (vartype == uhdm::UhdmType::IntVar ||
                    vartype == uhdm::UhdmType::IntegerVar ||
                    vartype == uhdm::UhdmType::RealVar ||
                    vartype == uhdm::UhdmType::ShortIntVar ||
                    vartype == uhdm::UhdmType::LongIntVar)
                  result = (uhdm::Expr *)exp;
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
      if (uhdm::Expr *val = instance->getComplexValue(name)) {
        result = val;
      }
      if (result == nullptr) {
        sval = instance->getValue(name);
        if (sval && sval->isValid()) {
          uhdm::Constant *c = s.make<uhdm::Constant>();
          c->setValue(sval->uhdmValue());
          setRange(c, sval, compileDesign);
          c->setDecompile(sval->decompiledValue());
          c->setConstType(sval->vpiValType());
          c->setSize(sval->getSize());
          result = c;
        }
      }
    }
  }

  if (component && (result == nullptr)) {
    if (uhdm::Expr *val = component->getComplexValue(name)) {
      result = val;
    }
    if (result == nullptr) {
      sval = component->getValue(name);
      if (sval && sval->isValid()) {
        uhdm::Constant *c = s.make<uhdm::Constant>();
        c->setValue(sval->uhdmValue());
        setRange(c, sval, compileDesign);
        c->setDecompile(sval->decompiledValue());
        c->setConstType(sval->vpiValType());
        c->setSize(sval->getSize());
        result = c;
      }
    }
  }

  if (component && (result == nullptr)) {
    if (uhdm::ParamAssignCollection *param_assigns =
            component->getParamAssigns()) {
      for (uhdm::ParamAssign *param : *param_assigns) {
        if (param && param->getLhs()) {
          const std::string_view param_name = param->getLhs()->getName();
          if (param_name == name) {
            if (substituteAssignedValue(param->getRhs(), compileDesign)) {
              if (param->getRhs()->getUhdmType() == uhdm::UhdmType::Operation) {
                uhdm::Operation *op = (uhdm::Operation *)param->getRhs();
                int32_t opType = op->getOpType();
                if (opType == vpiAssignmentPatternOp) {
                  const uhdm::Any *lhs = param->getLhs();
                  uhdm::Any *rhs = param->getRhs();
                  const uhdm::Typespec *ts = nullptr;
                  if (lhs->getUhdmType() == uhdm::UhdmType::Parameter) {
                    if (const uhdm::RefTypespec *rt =
                            ((uhdm::Parameter *)lhs)->getTypespec()) {
                      ts = rt->getActual();
                    }
                  }
                  rhs =
                      expandPatternAssignment(ts, (uhdm::Expr *)rhs, component,
                                              compileDesign, reduce, instance);
                  param->setRhs(rhs);
                  reorderAssignmentPattern(component, lhs, rhs, compileDesign,
                                           instance, 0);
                }
              }

              uhdm::ElaboratorContext elaboratorContext(&s, false, true);
              result = uhdm::clone_tree((uhdm::Any *)param->getRhs(),
                                        &elaboratorContext);
              if (result != nullptr) result->setParent(param);
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
      uhdm::Typespec *tps = tpd->getTypespec();
      if (tps && tps->getUhdmType() == uhdm::UhdmType::EnumTypespec) {
        uhdm::EnumTypespec *etps = (uhdm::EnumTypespec *)tps;
        for (auto n : *etps->getEnumConsts()) {
          if (n->getName() == name) {
            uhdm::Constant *c = s.make<uhdm::Constant>();
            c->setValue(n->getValue());
            setRange(c, sval, compileDesign);
            c->setSize(64);
            c->setConstType(vpiUIntConst);
            result = c;
          }
        }
      }
    }
  }

  if (result) {
    uhdm::UhdmType resultType = result->getUhdmType();
    if (resultType == uhdm::UhdmType::Constant) {
    } else if (resultType == uhdm::UhdmType::RefObj) {
      if (result->getName() != name) {
        if (uhdm::Any *tmp = getValue(result->getName(), component,
                                      compileDesign, Reduce::Yes, instance,
                                      fileId, lineNumber, pexpr, muteErrors)) {
          result = tmp;
        }
      }
    } else if (resultType == uhdm::UhdmType::Operation ||
               resultType == uhdm::UhdmType::HierPath ||
               resultType == uhdm::UhdmType::BitSelect ||
               resultType == uhdm::UhdmType::SysFuncCall) {
      if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes)) {
        bool invalidValue = false;
        if (uhdm::Any *tmp =
                reduceExpr(result, invalidValue, component, compileDesign,
                           instance, fileId, lineNumber, pexpr, muteErrors)) {
          result = tmp;
        }
      }
    }
  }
  if (m_checkForLoops) {
    m_stackLevel--;
  }
  return result;
}

uhdm::Any *CompileHelper::compileSelectExpression(
    DesignComponent *component, const FileContent *fC, NodeId Bit_select,
    std::string_view name, CompileDesign *compileDesign, Reduce reduce,
    uhdm::Any *pexpr, ValuedComponentI *instance, bool muteErrors) {
  uhdm::Serializer &s = compileDesign->getSerializer();
  uhdm::Any *result = nullptr;
  if ((fC->Type(Bit_select) == VObjectType::paConstant_bit_select) &&
      (!fC->Sibling(Bit_select))) {
    Bit_select = fC->Child(Bit_select);
  }
  if ((fC->Type(Bit_select) == VObjectType::paBit_select) &&
      (!fC->Sibling(Bit_select))) {
    Bit_select = fC->Child(Bit_select);
  }
  if (fC->Child(Bit_select) && fC->Sibling(Bit_select)) {
    // More than one
    uhdm::VarSelect *var_select = s.make<uhdm::VarSelect>();
    var_select->setName(name);
    if (name.find("::") != std::string::npos) {
      var_select->setFullName(name);
    }
    var_select->setParent(pexpr);
    result = var_select;
  }
  NodeId lastBitExp;
  while (Bit_select) {
    if (fC->Type(Bit_select) == VObjectType::paBit_select ||
        fC->Type(Bit_select) == VObjectType::paConstant_bit_select ||
        fC->Type(Bit_select) == VObjectType::paConstant_primary ||
        fC->Type(Bit_select) == VObjectType::paConstant_expression ||
        fC->Type(Bit_select) == VObjectType::paExpression) {
      NodeId bitexp = fC->Child(Bit_select);
      bool advanceBitSelect = false;
      if (fC->Type(Bit_select) == VObjectType::paConstant_expression) {
        bitexp = Bit_select;
        advanceBitSelect = true;
      }
      if (fC->Type(Bit_select) == VObjectType::paExpression) {
        bitexp = Bit_select;
        advanceBitSelect = true;
      }
      if (bitexp) {
        while (bitexp) {
          if ((fC->Type(bitexp) != VObjectType::paConstant_expression) &&
              (fC->Type(bitexp) != VObjectType::paExpression)) {
            break;
          }

          uhdm::Any *selParent = nullptr;
          if (result != nullptr) {
            selParent = result;
          } else if (fC->Child(Bit_select) && fC->Sibling(Bit_select)) {
            selParent = s.make<uhdm::VarSelect>();
          } else {
            selParent = s.make<uhdm::BitSelect>();
          }

          uhdm::Expr *sel = (uhdm::Expr *)compileExpression(
              component, fC, bitexp, compileDesign, reduce, selParent, instance,
              muteErrors);

          if (result) {
            uhdm::VarSelect *var_select = (uhdm::VarSelect *)result;
            var_select->setParent(pexpr);
            var_select->getIndexes(true)->emplace_back(sel);
            sel->setParent(var_select);
          } else if (fC->Child(Bit_select) && fC->Sibling(Bit_select)) {
            uhdm::VarSelect *var_select = (uhdm::VarSelect *)selParent;
            var_select->setName(name);
            if (name.find("::") != std::string::npos) {
              var_select->setFullName(name);
            }
            var_select->setParent(pexpr);
            sel->setParent(var_select);
            var_select->getIndexes(true)->emplace_back(sel);
            result = var_select;
          } else {
            uhdm::BitSelect *bit_select = (uhdm::BitSelect *)selParent;
            bit_select->setName(name);
            if (name.find("::") != std::string::npos) {
              bit_select->setFullName(name);
            }
            bit_select->setIndex(sel);
            bit_select->setParent(pexpr);
            sel->setParent(bit_select);
            NodeId selectId = Bit_select;
            while (selectId &&
                   (fC->Type(selectId) != VObjectType::paBit_select) &&
                   (fC->Type(selectId) != VObjectType::paConstant_select) &&
                   (fC->Type(selectId) != VObjectType::paConstant_bit_select)) {
              selectId = fC->Parent(selectId);
            }
            if (!selectId) selectId = Bit_select;
            fC->populateCoreMembers(selectId, selectId, bit_select);
            result = bit_select;
          }
          lastBitExp = bitexp;
          if (advanceBitSelect) Bit_select = bitexp;
          bitexp = fC->Sibling(bitexp);
        }
      }
    } else if (fC->Type(Bit_select) == VObjectType::paPart_select_range ||
               fC->Type(Bit_select) ==
                   VObjectType::paConstant_part_select_range) {
      NodeId Constant_range = fC->Child(Bit_select);
      uhdm::Expr *sel = (uhdm::Expr *)compilePartSelectRange(
          component, fC, Constant_range, name, compileDesign, reduce, pexpr,
          instance, muteErrors);
      if (result) {
        uhdm::VarSelect *var_select = (uhdm::VarSelect *)result;
        var_select->getIndexes(true)->emplace_back(sel);
        sel->setParent(var_select);
      } else if (fC->Child(Bit_select) && fC->Sibling(Bit_select)) {
        uhdm::VarSelect *var_select = s.make<uhdm::VarSelect>();
        var_select->setName(name);
        if (name.find("::") != std::string::npos) {
          var_select->setFullName(name);
        }
        var_select->setParent(pexpr);
        var_select->getIndexes(true)->emplace_back(sel);
        sel->setParent(var_select);
      } else {
        result = sel;
      }
    } else if ((fC->Type(Bit_select) == VObjectType::slStringConst) ||
               (fC->Type(Bit_select) ==
                VObjectType::paPs_or_hierarchical_identifier)) {
      std::string hname(name);
      uhdm::HierPath *path = s.make<uhdm::HierPath>();
      uhdm::AnyCollection *elems = path->getPathElems(true);
      uhdm::RefObj *r1 = s.make<uhdm::RefObj>();
      r1->setName(name);
      r1->setFullName(name);
      elems->emplace_back(r1);
      r1->setParent(path);
      fC->populateCoreMembers(fC->Parent(Bit_select),
                              fC->Child(fC->Parent(Bit_select)), r1);
      while (Bit_select) {
        if ((fC->Type(Bit_select) ==
             VObjectType::paPs_or_hierarchical_identifier)) {
          uhdm::RefObj *r = s.make<uhdm::RefObj>();
          NodeId nameId = fC->Child(Bit_select);
          while (fC->Type(nameId) != VObjectType::slStringConst)
            nameId = fC->Child(nameId);
          r->setName(fC->SymName(nameId));
          r->setParent(path);
          fC->populateCoreMembers(nameId, nameId, r);
          elems->emplace_back(r);
          hname.append(".").append(fC->SymName(nameId));
        } else if ((fC->Type(Bit_select) == VObjectType::paSelect)) {
          NodeId nameId = fC->Child(Bit_select);
          if (nameId && (fC->Type(nameId) == VObjectType::slStringConst)) {
            uhdm::RefObj *r = s.make<uhdm::RefObj>();
            r->setName(fC->SymName(nameId));
            r->setParent(path);
            fC->populateCoreMembers(nameId, nameId, r);
            elems->emplace_back(r);
            hname.append(".").append(fC->SymName(nameId));
          }
        } else if (fC->Type(Bit_select) == VObjectType::slStringConst) {
          NodeId tmp = fC->Sibling(Bit_select);
          if (((fC->Type(tmp) == VObjectType::paConstant_bit_select) ||
               (fC->Type(tmp) == VObjectType::paBit_select)) &&
              fC->Child(tmp)) {
            uhdm::Any *sel =
                compileExpression(component, fC, Bit_select, compileDesign,
                                  reduce, pexpr, instance, muteErrors);
            if (sel) {
              hname.append(".")
                  .append(sel->getName())
                  .append(decompileHelper(sel));
              if (sel->getUhdmType() == uhdm::UhdmType::HierPath) {
                uhdm::HierPath *p = (uhdm::HierPath *)sel;
                for (auto el : *p->getPathElems()) {
                  el->swap(p, path);
                  elems->emplace_back(el);
                }
                break;
              } else {
                sel->setParent(path, true);
                elems->emplace_back(sel);
              }
            }
          } else {
            uhdm::RefObj *r2 = s.make<uhdm::RefObj>();
            r2->setName(fC->SymName(Bit_select));
            r2->setFullName(fC->SymName(Bit_select));
            r2->setParent(path);
            fC->populateCoreMembers(Bit_select, Bit_select, r2);
            elems->emplace_back(r2);
            hname.append(".").append(fC->SymName(Bit_select));
          }
        }
        Bit_select = fC->Sibling(Bit_select);
      }
      path->setName(hname);
      path->setFullName(hname);
      if (!elems->empty()) {
        path->setStartLine(elems->front()->getStartLine());
        path->setStartColumn(elems->front()->getStartColumn());
        path->setEndLine(elems->back()->getEndLine());
        path->setEndColumn(elems->back()->getEndColumn());
      }
      path->setParent(pexpr);
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
uhdm::Any *CompileHelper::compileExpression(
    DesignComponent *component, const FileContent *fC, NodeId parent,
    CompileDesign *compileDesign, Reduce reduce, uhdm::Any *pexpr,
    ValuedComponentI *instance, bool muteErrors) {
  if (m_checkForLoops) {
    m_stackLevel++;
  }

  Design *const design = compileDesign->getCompiler()->getDesign();
  if (pexpr == nullptr) pexpr = component->getUhdmModel();
  if (pexpr == nullptr) pexpr = design->getUhdmDesign();

  FileSystem *const fileSystem = m_session->getFileSystem();
  uhdm::Serializer &s = compileDesign->getSerializer();
  uhdm::Any *result = nullptr;
  VObjectType parentType = fC->Type(parent);
  uhdm::AttributeCollection *attributes = nullptr;
  if (parentType == VObjectType::paAttribute_instance) {
    attributes =
        compileAttributes(component, fC, parent, compileDesign, nullptr);
    while (fC->Type(parent) == VObjectType::paAttribute_instance)
      parent = fC->Sibling(parent);
  }
  parentType = fC->Type(parent);
  NodeId child = fC->Child(parent);
  VObjectType childType = VObjectType::sl_INVALID_;
  if (child) {
    childType = fC->Type(child);
  }
  switch (parentType) {
    case VObjectType::paIntegerAtomType_Byte: {
      result = s.make<uhdm::ByteVar>();
      result->setParent(pexpr);
      break;
    }
    case VObjectType::paIntegerAtomType_Int: {
      result = s.make<uhdm::IntVar>();
      result->setParent(pexpr);
      break;
    }
    case VObjectType::paIntegerAtomType_Integer: {
      result = s.make<uhdm::IntegerVar>();
      result->setParent(pexpr);
      break;
    }
    case VObjectType::paIntegerAtomType_LongInt: {
      result = s.make<uhdm::LongIntVar>();
      result->setParent(pexpr);
      break;
    }
    case VObjectType::paIntegerAtomType_Shortint: {
      result = s.make<uhdm::ShortIntVar>();
      result->setParent(pexpr);
      break;
    }
    case VObjectType::paValue_range: {
      uhdm::Operation *list_op = s.make<uhdm::Operation>();
      fC->populateCoreMembers(parent, parent, list_op);
      list_op->setOpType(vpiListOp);
      list_op->setParent(pexpr);
      uhdm::AnyCollection *operands = list_op->getOperands(true);
      NodeId lexpr = child;
      NodeId rexpr = fC->Sibling(lexpr);
      if (uhdm::Expr *op = any_cast<uhdm::Expr *>(
              compileExpression(component, fC, lexpr, compileDesign, reduce,
                                list_op, instance, muteErrors))) {
        operands->emplace_back(op);
      }
      if (rexpr) {
        if (uhdm::Expr *op = any_cast<uhdm::Expr *>(
                compileExpression(component, fC, rexpr, compileDesign, reduce,
                                  list_op, instance, muteErrors))) {
          operands->emplace_back(op);
        }
      }
      if (attributes != nullptr) {
        list_op->setAttributes(attributes);
        for (auto a : *attributes) a->setParent(list_op);
      }
      result = list_op;
      fC->populateCoreMembers(parent, parent, result);
      if (m_checkForLoops) {
        m_stackLevel--;
      }
      return result;
    }
    case VObjectType::paNet_lvalue: {
      uhdm::Operation *operation = s.make<uhdm::Operation>();
      uhdm::AnyCollection *operands = operation->getOperands(true);
      if (attributes != nullptr) {
        operation->setAttributes(attributes);
        for (auto a : *attributes) a->setParent(operation);
      }
      result = operation;
      operation->setParent(pexpr);
      operation->setOpType(vpiConcatOp);
      fC->populateCoreMembers(fC->Parent(parent), fC->Parent(parent), result);
      NodeId Expression = parent;
      while (Expression) {
        if (uhdm::Any *exp = compileExpression(
                component, fC, fC->Child(Expression), compileDesign, reduce,
                operation, instance, muteErrors)) {
          operands->emplace_back(exp);
        }
        Expression = fC->Sibling(Expression);
      }
      if (m_checkForLoops) {
        m_stackLevel--;
      }
      return result;
    }
    case VObjectType::paConcatenation:
    case VObjectType::paConstant_concatenation: {
      uhdm::Operation *operation = s.make<uhdm::Operation>();
      uhdm::AnyCollection *operands = operation->getOperands(true);
      if (attributes != nullptr) {
        operation->setAttributes(attributes);
        for (auto a : *attributes) a->setParent(operation);
      }
      result = operation;
      operation->setParent(pexpr);
      operation->setOpType(vpiConcatOp);
      fC->populateCoreMembers(parent, parent, result);
      NodeId Expression = fC->Child(parent);
      while (Expression) {
        uhdm::Any *exp =
            compileExpression(component, fC, Expression, compileDesign, reduce,
                              operation, instance, muteErrors);
        if (exp) operands->emplace_back(exp);
        Expression = fC->Sibling(Expression);
      }
      child = InvalidNodeId;  // Use parent for location info computation down
                              // below!
      break;
    }
    case VObjectType::paDelay2:
    case VObjectType::paDelay3: {
      NodeId MinTypMax = child;
      if (fC->Sibling(MinTypMax)) {
        uhdm::Operation *operation = s.make<uhdm::Operation>();
        uhdm::AnyCollection *operands = operation->getOperands(true);
        operation->setOpType(vpiListOp);
        operation->setParent(pexpr);
        fC->populateCoreMembers(parent, parent, operation);
        result = operation;
        NodeId Expression = MinTypMax;
        while (Expression) {
          uhdm::Any *exp =
              compileExpression(component, fC, Expression, compileDesign,
                                reduce, operation, instance, muteErrors);
          if (exp) operands->emplace_back(exp);
          Expression = fC->Sibling(Expression);
        }
        if (m_checkForLoops) {
          m_stackLevel--;
        }
        return result;
      }
      break;
    }
    case VObjectType::paConstant_mintypmax_expression:
    case VObjectType::paMintypmax_expression: {
      NodeId Expression = child;
      uhdm::Operation *op = s.make<uhdm::Operation>();
      op->setOpType(vpiMinTypMaxOp);
      op->setParent(pexpr);
      fC->populateCoreMembers(parent, parent, op);
      uhdm::AnyCollection *operands = op->getOperands(true);
      result = op;
      while (Expression) {
        uhdm::Expr *sExpr = (uhdm::Expr *)compileExpression(
            component, fC, Expression, compileDesign, reduce, op, instance,
            muteErrors);
        if (sExpr) operands->emplace_back(sExpr);
        Expression = fC->Sibling(Expression);
      }
      if (m_checkForLoops) {
        m_stackLevel--;
      }
      return result;
    }
    case VObjectType::paExpression: {
      NodeId Iff = fC->Sibling(parent);
      if (fC->Type(Iff) == VObjectType::paIFF) {
        uhdm::Operation *op = s.make<uhdm::Operation>();
        op->setOpType(vpiIffOp);
        op->setParent(pexpr);
        uhdm::AnyCollection *operands = op->getOperands(true);
        result = op;
        uhdm::Expr *lExpr =
            (uhdm::Expr *)compileExpression(component, fC, child, compileDesign,
                                            reduce, op, instance, muteErrors);
        if (lExpr) operands->emplace_back(lExpr);
        NodeId Expr = fC->Sibling(Iff);
        uhdm::Expr *rExpr =
            (uhdm::Expr *)compileExpression(component, fC, Expr, compileDesign,
                                            reduce, op, instance, muteErrors);
        if (rExpr) operands->emplace_back(rExpr);
        fC->populateCoreMembers(parent, Expr, op);
        if (m_checkForLoops) {
          m_stackLevel--;
        }
        return result;
      }
      break;
    }
    case VObjectType::paClass_new: {
      uhdm::MethodFuncCall *sys = s.make<uhdm::MethodFuncCall>();
      sys->setName("new");
      sys->setParent(pexpr);
      fC->populateCoreMembers(parent, parent, sys);
      if (uhdm::AnyCollection *arguments =
              compileTfCallArguments(component, fC, child, compileDesign,
                                     reduce, sys, instance, muteErrors)) {
        sys->setArguments(arguments);
      }
      result = sys;
      if (m_checkForLoops) {
        m_stackLevel--;
      }
      return result;
    }
    case VObjectType::paPort_expression: {
      uhdm::Operation *op = s.make<uhdm::Operation>();
      op->setParent(pexpr);
      op->setOpType(vpiConcatOp);
      fC->populateCoreMembers(parent, parent, op);
      auto ops = op->getOperands();
      result = op;
      NodeId Port_reference = child;
      while (Port_reference) {
        NodeId Name = fC->Child(Port_reference);
        NodeId Constant_select = fC->Sibling(Name);

        if (fC->Type(Constant_select) == VObjectType::paConstant_select) {
          Constant_select = fC->Child(Constant_select);
        }
        if (fC->Child(Constant_select) || fC->Sibling(Constant_select)) {
          if (uhdm::Any *select = compileSelectExpression(
                  component, fC, Constant_select, "", compileDesign, reduce, op,
                  instance, muteErrors)) {
            ops->emplace_back(select);
          }
        } else {
          uhdm::RefObj *ref = s.make<uhdm::RefObj>();
          ops->emplace_back(ref);
          const std::string_view name = fC->SymName(Name);
          ref->setName(name);
          ref->setParent(op);
          fC->populateCoreMembers(Port_reference, Port_reference, ref);
          if (pexpr) {
            if (uhdm::Any *var =
                    bindVariable(component, pexpr, name, compileDesign))
              ref->setActual(var);
          } else if (instance) {
            if (uhdm::Any *var =
                    bindVariable(component, instance, name, compileDesign))
              ref->setActual(var);
          }
        }
        uhdm::UnsupportedTypespec *tps = s.make<uhdm::UnsupportedTypespec>();
        if (op->getTypespec() == nullptr) {
          uhdm::RefTypespec *rttps = s.make<uhdm::RefTypespec>();
          rttps->setParent(op);
          op->setTypespec(rttps);
        }
        op->getTypespec()->setActual(tps);
        Port_reference = fC->Sibling(Port_reference);
      }
      break;
    }
    default:
      break;
  }

  if ((parentType == VObjectType::paVariable_lvalue) &&
      (childType == VObjectType::paVariable_lvalue)) {
    uhdm::Operation *operation = s.make<uhdm::Operation>();
    uhdm::AnyCollection *operands = operation->getOperands(true);
    if (attributes != nullptr) {
      operation->setAttributes(attributes);
      for (auto a : *attributes) a->setParent(operation);
    }
    result = operation;
    operation->setParent(pexpr);
    operation->setOpType(vpiConcatOp);
    fC->populateCoreMembers(parent, parent, result);
    NodeId Expression = child;
    while (Expression) {
      NodeId n = fC->Child(Expression);
      if (fC->Type(n) == VObjectType::paVariable_lvalue) {
        n = Expression;
      }
      if (uhdm::Any *exp =
              compileExpression(component, fC, n, compileDesign, reduce,
                                operation, instance, muteErrors)) {
        operands->emplace_back(exp);
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
        case VObjectType::paNull_keyword: {
          uhdm::Constant *c = s.make<uhdm::Constant>();
          c->setValue("UINT:0");
          c->setDecompile("0");
          c->setSize(64);
          c->setConstType(vpiNullConst);
          c->setParent(pexpr);
          result = c;
          break;
        }
        case VObjectType::paDollar_keyword: {
          uhdm::Constant *c = s.make<uhdm::Constant>();
          c->setConstType(vpiUnboundedConst);
          c->setValue("STRING:$");
          c->setDecompile("$");
          c->setSize(1);
          c->setParent(pexpr);
          result = c;
          break;
        }
        case VObjectType::paThis_keyword:
        case VObjectType::paSuper_keyword:
        case VObjectType::paThis_dot_super: {
          result = compileComplexFuncCall(component, fC, parent, compileDesign,
                                          reduce, pexpr, instance, muteErrors);
          break;
        }
        case VObjectType::paArray_member_label: {
          uhdm::Operation *operation = s.make<uhdm::Operation>();
          uhdm::AnyCollection *operands = operation->getOperands(true);
          if (attributes != nullptr) {
            operation->setAttributes(attributes);
            for (auto a : *attributes) a->setParent(operation);
          }
          result = operation;
          operation->setParent(pexpr);
          operation->setOpType(vpiConcatOp);
          fC->populateCoreMembers(parent, parent, result);
          NodeId Expression = child;
          bool odd = true;
          while (Expression) {
            NodeId the_exp = fC->Child(Expression);
            if (!the_exp) {
              uhdm::RefObj *ref = s.make<uhdm::RefObj>();
              ref->setName("default");
              operands->emplace_back(ref);
              ref->setParent(operation);
              ref->setStructMember(true);
            } else {
              if (uhdm::Any *exp = compileExpression(
                      component, fC, the_exp, compileDesign, reduce, operation,
                      instance, muteErrors)) {
                operands->emplace_back(exp);
                if (odd && (exp->getUhdmType() == uhdm::UhdmType::RefObj)) {
                  ((uhdm::RefObj *)exp)->setStructMember(true);
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
        case VObjectType::paIncDec_PlusPlus:
        case VObjectType::paIncDec_MinusMinus:
        case VObjectType::paUnary_Minus:
        case VObjectType::paUnary_Plus:
        case VObjectType::paUnary_Tilda:
        case VObjectType::paUnary_Not:
        case VObjectType::paNOT:
        case VObjectType::paUnary_BitwOr:
        case VObjectType::paUnary_BitwAnd:
        case VObjectType::paUnary_BitwXor:
        case VObjectType::paUnary_ReductNand:
        case VObjectType::paUnary_ReductNor:
        case VObjectType::paUnary_ReductXnor1:
        case VObjectType::paUnary_ReductXnor2: {
          uint32_t vopType = UhdmWriter::getVpiOpType(childType);
          if (vopType) {
            uhdm::Operation *op = s.make<uhdm::Operation>();
            op->setOpType(vopType);
            op->setParent(pexpr);
            if (attributes != nullptr) {
              op->setAttributes(attributes);
              for (auto a : *attributes) a->setParent(op);
            }
            fC->populateCoreMembers(parent, parent, op);
            uhdm::AnyCollection *operands = op->getOperands(true);
            NodeId var = fC->Sibling(child);
            if (fC->Type(var) == VObjectType::paVariable_lvalue) {
              var = fC->Child(var);
            }
            if (uhdm::Any *operand =
                    compileExpression(component, fC, var, compileDesign, reduce,
                                      op, instance, muteErrors)) {
              operands->emplace_back(operand);
            }
            fC->populateCoreMembers(parent, parent, op);
            result = op;
          }
          break;
        }
        case VObjectType::paEdge_Posedge: {
          uhdm::Operation *op = s.make<uhdm::Operation>();
          op->setOpType(vpiPosedgeOp);
          op->setParent(pexpr);
          if (attributes != nullptr) {
            op->setAttributes(attributes);
            for (auto a : *attributes) a->setParent(op);
          }
          if (uhdm::Any *operand = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, reduce, op,
                  instance, muteErrors)) {
            op->getOperands(true)->emplace_back(operand);
            fC->populateCoreMembers(parent, parent, op);
          }
          result = op;
          break;
        }
        case VObjectType::paEdge_Edge: {
          uhdm::Operation *op = s.make<uhdm::Operation>();
          op->setOpType(vpiAnyEdge);
          op->setParent(pexpr);
          if (attributes != nullptr) {
            op->setAttributes(attributes);
            for (auto a : *attributes) a->setParent(op);
          }
          if (uhdm::Any *operand = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, reduce, op,
                  instance, muteErrors)) {
            op->getOperands(true)->emplace_back(operand);
            fC->populateCoreMembers(parent, parent, op);
          }
          result = op;
          break;
        }
        case VObjectType::paEdge_Negedge: {
          uhdm::Operation *op = s.make<uhdm::Operation>();
          op->setOpType(vpiNegedgeOp);
          op->setParent(pexpr);
          if (attributes != nullptr) {
            op->setAttributes(attributes);
            for (auto a : *attributes) a->setParent(op);
          }
          if (uhdm::Any *operand = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, reduce, op,
                  instance, muteErrors)) {
            op->getOperands(true)->emplace_back(operand);
            fC->populateCoreMembers(parent, parent, op);
          }
          result = op;
          break;
        }
        case VObjectType::paImplicit_class_handle:
        case VObjectType::paInc_or_dec_expression:
        case VObjectType::paConstant_primary:
        case VObjectType::paPrimary_literal:
        case VObjectType::paPrimary:
        case VObjectType::paSystem_task:
        case VObjectType::paParam_expression:
        case VObjectType::paExpression_or_cond_pattern:
        case VObjectType::paConstant_param_expression:
        case VObjectType::paAssignment_pattern_expression:
        case VObjectType::paConstant_assignment_pattern_expression:
        case VObjectType::paConst_or_range_expression:
          result = compileExpression(component, fC, child, compileDesign,
                                     reduce, pexpr, instance, muteErrors);
          break;
        case VObjectType::paExpression_or_dist: {
          uhdm::Any *pexpr2 = pexpr;
          uhdm::Operation *op = nullptr;
          if (NodeId dist = fC->Sibling(child)) {
            op = s.make<uhdm::Operation>();
            op->setParent(pexpr);
            op->getOperands(true);
            fC->populateCoreMembers(parent, parent, op);
            pexpr2 = op;
          }
          result = compileExpression(component, fC, child, compileDesign,
                                     reduce, pexpr2, instance, muteErrors);
          if (op != nullptr) op->getOperands()->emplace_back(result);
          if (NodeId dist = fC->Sibling(child)) {
            VObjectType distType = fC->Type(dist);
            if (distType == VObjectType::paBoolean_abbrev) {
              NodeId repetition = fC->Child(dist);
              VObjectType repetType = fC->Type(repetition);
              op->setOpType(UhdmWriter::getVpiOpType(repetType));
              if ((repetType == VObjectType::paConsecutive_repetition) &&
                  (fC->Child(repetition) == InvalidNodeId)) {
              } else if (uhdm::Any *rep = compileExpression(
                             component, fC, repetition, compileDesign, reduce,
                             op, instance, muteErrors)) {
                op->getOperands()->emplace_back(rep);
              }
              result = op;
            } else if ((distType == VObjectType::paTHROUGHOUT) ||
                       (distType == VObjectType::paWITHIN) ||
                       (distType == VObjectType::paINTERSECT)) {
              NodeId repetition = fC->Sibling(dist);
              op->setOpType(UhdmWriter::getVpiOpType(distType));
              if (uhdm::Any *rep = compileExpression(component, fC, repetition,
                                                     compileDesign, reduce, op,
                                                     instance, muteErrors)) {
                op->getOperands()->emplace_back(rep);
              }
              result = op;
            }
          }
          break;
        }
        case VObjectType::paComplex_func_call: {
          result = compileComplexFuncCall(component, fC, child, compileDesign,
                                          reduce, pexpr, instance, muteErrors);
          break;
        }
        case VObjectType::paDOT: {
          NodeId Identifier = fC->Sibling(child);
          uhdm::RefObj *ref = s.make<uhdm::RefObj>();
          ref->setName(fC->SymName(Identifier));
          ref->setParent(pexpr);
          fC->populateCoreMembers(Identifier, Identifier, ref);
          result = ref;
          break;
        }
        case VObjectType::paConstant_mintypmax_expression:
        case VObjectType::paMintypmax_expression: {
          NodeId Expression = fC->Child(child);
          NodeId Sibling = fC->Sibling(Expression);
          if (!Sibling) {
            NodeId Constant_primary = fC->Child(Expression);
            NodeId Constant_expression = fC->Child(Constant_primary);
            NodeId TmpSibling = fC->Sibling(Constant_expression);
            if (TmpSibling &&
                (fC->Type(TmpSibling) == VObjectType::paConstant_expression)) {
              Sibling = TmpSibling;
              Expression = Constant_primary;
            }
          }
          if (Sibling) {
            uhdm::Operation *op = s.make<uhdm::Operation>();
            op->setOpType(vpiMinTypMaxOp);
            op->setParent(pexpr);
            fC->populateCoreMembers(parent, parent, op);
            uhdm::AnyCollection *operands = op->getOperands(true);
            result = op;
            if (uhdm::Expr *cExpr = (uhdm::Expr *)compileExpression(
                    component, fC, Expression, compileDesign, reduce, op,
                    instance, muteErrors)) {
              operands->emplace_back(cExpr);
            }
            while (Sibling) {
              if (uhdm::Expr *sExpr = (uhdm::Expr *)compileExpression(
                      component, fC, Sibling, compileDesign, reduce, op,
                      instance, muteErrors)) {
                operands->emplace_back(sExpr);
              }
              Sibling = fC->Sibling(Sibling);
            }
          } else {
            result = (uhdm::Expr *)compileExpression(
                component, fC, Expression, compileDesign, reduce, pexpr,
                instance, muteErrors);
          }
          break;
        }
        case VObjectType::paRandomize_call: {
          result =
              compileRandomizeCall(component, fC, child, compileDesign, pexpr);
          break;
        }
        case VObjectType::paPattern: {
          NodeId Sibling = fC->Sibling(child);
          if (Sibling) {
            uhdm::Operation *op = s.make<uhdm::Operation>();
            op->setOpType(vpiListOp);
            op->setParent(pexpr);
            fC->populateCoreMembers(parent, parent, op);
            uhdm::AnyCollection *operands = op->getOperands(true);
            result = op;
            if (uhdm::Expr *cExpr = (uhdm::Expr *)compileExpression(
                    component, fC, fC->Child(child), compileDesign, reduce, op,
                    instance, muteErrors)) {
              operands->emplace_back(cExpr);
            }
            while (Sibling) {
              if (uhdm::Expr *sExpr = (uhdm::Expr *)compileExpression(
                      component, fC, Sibling, compileDesign, reduce, op,
                      instance, muteErrors)) {
                operands->emplace_back(sExpr);
              }
              Sibling = fC->Sibling(Sibling);
            }
          } else {
            result = (uhdm::Expr *)compileExpression(
                component, fC, fC->Child(child), compileDesign, reduce, pexpr,
                instance, muteErrors);
          }
          break;
        }
        case VObjectType::paTAGGED: {
          NodeId Identifier = fC->Sibling(child);
          NodeId Expression = fC->Sibling(Identifier);
          uhdm::TaggedPattern *pattern = s.make<uhdm::TaggedPattern>();
          pattern->setName(fC->SymName(Identifier));
          pattern->setParent(pexpr);
          if (Expression) {
            fC->populateCoreMembers(child, Expression, pattern);
            pattern->setPattern(
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, pattern, instance, muteErrors));
          } else {
            fC->populateCoreMembers(child, Identifier, pattern);
          }
          result = pattern;
          break;
        }
        case VObjectType::paEvent_expression: {
          uhdm::Any *pexpr2 = pexpr;
          uhdm::Operation *operation = nullptr;

          NodeId subExpr = child;
          NodeId op = fC->Sibling(subExpr);
          if (op) {
            operation = s.make<uhdm::Operation>();
            operation->getOperands(true);
            operation->setParent(pexpr);
            if (attributes != nullptr) {
              operation->setAttributes(attributes);
              for (auto a : *attributes) a->setParent(operation);
            }
            pexpr2 = operation;
          }

          if (uhdm::Any *opL =
                  compileExpression(component, fC, subExpr, compileDesign,
                                    reduce, pexpr2, instance, muteErrors)) {
            if (operation != nullptr) {
              operation->getOperands()->emplace_back(opL);
            }
            result = opL;
          }
          while (op) {
            if (fC->Type(op) == VObjectType::paOr_operator) {
              operation->setOpType(vpiEventOrOp);
              NodeId subRExpr = fC->Sibling(op);
              if (uhdm::Any *opR =
                      compileExpression(component, fC, subRExpr, compileDesign,
                                        reduce, pexpr2, instance, muteErrors)) {
                operation->getOperands()->emplace_back(opR);
              }
              op = fC->Sibling(subRExpr);
            } else if (fC->Type(op) == VObjectType::paComma_operator) {
              operation->setOpType(vpiListOp);
              NodeId subRExpr = fC->Sibling(op);
              if (uhdm::Any *opR =
                      compileExpression(component, fC, subRExpr, compileDesign,
                                        reduce, pexpr2, instance, muteErrors)) {
                operation->getOperands()->emplace_back(opR);
              }
              op = fC->Sibling(subRExpr);
            }
          }
          if (operation != nullptr) {
            result = operation;
            fC->populateCoreMembers(parent, parent, operation);
          }
          break;
        }
        case VObjectType::paExpression:
        case VObjectType::paConstant_expression: {
          uhdm::Any *opL =
              compileExpression(component, fC, child, compileDesign, reduce,
                                pexpr, instance, muteErrors);
          NodeId op = fC->Sibling(child);
          if ((!op) || (fC->Type(op) == VObjectType::paConstant_expression)) {
            result = opL;
            break;
          }
          VObjectType opType = fC->Type(op);
          uint32_t vopType = UhdmWriter::getVpiOpType(opType);
          if (opType == VObjectType::paQMARK ||
              opType == VObjectType::paConditional_operator) {  // Ternary op
            if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
                (opL->getUhdmType() == uhdm::UhdmType::Constant)) {
              uhdm::ExprEval eval;
              bool invalidValue = false;
              int64_t cond = eval.get_value(invalidValue, (uhdm::Expr *)opL);
              if (cond) {
                NodeId rval = fC->Sibling(op);
                result = compileExpression(component, fC, rval, compileDesign,
                                           reduce, pexpr, instance, muteErrors);
                break;
              } else {
                NodeId rval = fC->Sibling(op);
                rval = fC->Sibling(rval);
                result = compileExpression(component, fC, rval, compileDesign,
                                           reduce, pexpr, instance, muteErrors);
                break;
              }
            }
          }

          uhdm::Operation *operation = s.make<uhdm::Operation>();
          uhdm::AnyCollection *operands = operation->getOperands(true);
          result = operation;
          operation->setParent(pexpr);
          if (attributes != nullptr) {
            operation->setAttributes(attributes);
            for (auto a : *attributes) a->setParent(operation);
          }
          fC->populateCoreMembers(parent, parent, operation);
          if (opL) {
            opL->setParent(operation, true);
            operands->emplace_back(opL);
          }
          if (vopType == 0) {
            result = nullptr;
          }
          operation->setOpType(vopType);

          NodeId rval = fC->Sibling(op);
          NodeId attributeId;
          if (fC->Type(rval) == VObjectType::paAttribute_instance) {
            attributeId = rval;
            while (fC->Type(rval) == VObjectType::paAttribute_instance)
              rval = fC->Sibling(rval);
          }
          if (opType == VObjectType::paINSIDE) {
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
              if (uhdm::Any *exp = compileExpression(
                      component, fC, Expression, compileDesign, reduce,
                      operation, instance, muteErrors)) {
                operands->emplace_back(exp);
              }
              Expression = fC->Sibling(Expression);
            }
            // RHS is done, skip handling below
            break;
          } else if (opType == VObjectType::paOpen_range_list) {
            NodeId Value_range = fC->Child(op);
            NodeId Expression = fC->Child(Value_range);
            while (Expression) {
              if (uhdm::Expr *exp = (uhdm::Expr *)compileExpression(
                      component, fC, Expression, compileDesign, reduce,
                      operation, instance, muteErrors)) {
                operands->emplace_back(exp);

                if (attributeId) {
                  if (uhdm::AttributeCollection *attributes = compileAttributes(
                          component, fC, attributeId, compileDesign, exp)) {
                    exp->setAttributes(attributes);
                  }
                }
              }
              Expression = fC->Sibling(Expression);
            }
            // RHS is done, skip handling below
            break;
          }

          if (uhdm::Expr *opR = (uhdm::Expr *)compileExpression(
                  component, fC, rval, compileDesign, reduce, operation,
                  instance, muteErrors)) {
            opR->setParent(operation);
            operands->emplace_back(opR);

            if (attributeId) {
              if (uhdm::AttributeCollection *attributes = compileAttributes(
                      component, fC, attributeId, compileDesign, opR)) {
                opR->setAttributes(attributes);
              }
            }
          }
          if (opType == VObjectType::paQMARK ||
              opType == VObjectType::paConditional_operator) {  // Ternary op
            rval = fC->Sibling(rval);
            if (uhdm::Any *opR = compileExpression(
                    component, fC, rval, compileDesign, reduce, operation,
                    instance, muteErrors)) {
              opR->setParent(operation);
              operands->emplace_back(opR);
            }
          }
          fC->populateCoreMembers(child, rval, operation);
          break;
        }
        case VObjectType::paSystem_task_names: {
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
            uhdm::SysFuncCall *sys = s.make<uhdm::SysFuncCall>();
            sys->setName(name);
            sys->setParent(pexpr);
            NodeId argListNode = fC->Sibling(child);
            if (uhdm::AnyCollection *arguments = compileTfCallArguments(
                    component, fC, argListNode, compileDesign, reduce, sys,
                    instance, muteErrors)) {
              sys->setArguments(arguments);
            }
            result = sys;
          }
          fC->populateCoreMembers(parent, parent, result);
          break;
        }
        case VObjectType::paVariable_lvalue: {
          uhdm::Any *variable =
              compileExpression(component, fC, fC->Child(child), compileDesign,
                                reduce, pexpr, instance, muteErrors);
          if (NodeId op = fC->Sibling(child)) {
            fC->populateCoreMembers(child, child, variable);

            VObjectType opType = fC->Type(op);
            if (uint32_t vopType = UhdmWriter::getVpiOpType(opType)) {
              // Post increment/decrement
              uhdm::Operation *operation = s.make<uhdm::Operation>();
              if (attributes != nullptr) {
                operation->setAttributes(attributes);
                for (auto a : *attributes) a->setParent(operation);
              }
              fC->populateCoreMembers(parent, parent, operation);
              operation->setParent(pexpr);
              operation->setOpType(vopType);
              operation->getOperands(true)->emplace_back(variable);
              variable->setParent(operation, true);
              result = operation;
              NodeId rval = fC->Sibling(op);
              if (fC->Type(rval) == VObjectType::paAttribute_instance) {
                if (uhdm::AttributeCollection *attributes = compileAttributes(
                        component, fC, rval, compileDesign, operation)) {
                  operation->setAttributes(attributes);
                  for (auto a : *attributes) a->setParent(operation);
                }
                while (fC->Type(rval) == VObjectType::paAttribute_instance)
                  rval = fC->Sibling(rval);
              }
            } else if (opType == VObjectType::paExpression) {
              // Assignment
              uhdm::Operation *operation = s.make<uhdm::Operation>();
              if (attributes != nullptr) {
                operation->setAttributes(attributes);
                for (auto a : *attributes) a->setParent(operation);
              }
              fC->populateCoreMembers(parent, parent, operation);
              operation->setParent(pexpr);
              operation->setOpType(vpiAssignmentOp);
              operation->getOperands(true)->emplace_back(variable);
              variable->setParent(operation, true);
              result = operation;

              NodeId rval = op;
              if (fC->Type(rval) == VObjectType::paAttribute_instance) {
                if (uhdm::AttributeCollection *attributes = compileAttributes(
                        component, fC, rval, compileDesign, operation)) {
                  operation->setAttributes(attributes);
                  for (auto a : *attributes) a->setParent(operation);
                }
                while (fC->Type(rval) == VObjectType::paAttribute_instance)
                  rval = fC->Sibling(rval);
              }

              if (uhdm::Any *rexp = compileExpression(
                      component, fC, rval, compileDesign, reduce, operation,
                      instance, muteErrors)) {
                operation->getOperands()->emplace_back(rexp);
              }
            }
          } else {
            result = variable;
          }
          break;
        }
        case VObjectType::paAssignment_pattern: {
          result = compileAssignmentPattern(component, fC, child, compileDesign,
                                            reduce, pexpr, instance);
          break;
        }
        case VObjectType::paSequence_instance: {
          NodeId Ps_or_hierarchical_sequence_identifier = fC->Child(child);
          NodeId Ps_or_hierarchical_array_identifier =
              fC->Child(Ps_or_hierarchical_sequence_identifier);
          NodeId NameId = fC->Child(Ps_or_hierarchical_array_identifier);
          const std::string_view name = fC->SymName(NameId);
          uhdm::SequenceInst *seqinst = s.make<uhdm::SequenceInst>();
          fC->populateCoreMembers(child, child, seqinst);
          seqinst->setName(name);
          seqinst->setParent(pexpr);
          NodeId Sequence_list_of_arguments =
              fC->Sibling(Ps_or_hierarchical_sequence_identifier);
          NodeId Sequence_actual_arg = fC->Child(Sequence_list_of_arguments);
          uhdm::AnyCollection *args = seqinst->getArguments(true);
          while (Sequence_actual_arg) {
            NodeId arg = Sequence_actual_arg;
            if (fC->Type(Sequence_actual_arg) == VObjectType::paSequence_arg) {
              arg = fC->Child(Sequence_actual_arg);
            }
            if (arg) {
              NodeId Event_expression = fC->Child(arg);
              if (uhdm::Any *exp = compileExpression(
                      component, fC, Event_expression, compileDesign, reduce,
                      seqinst, instance, muteErrors)) {
                args->emplace_back(exp);
              }
            } else {
              uhdm::Constant *c = s.make<uhdm::Constant>();
              c->setValue("INT:0");
              c->setDecompile("0");
              c->setSize(64);
              c->setConstType(vpiIntConst);
              c->setParent(pexpr);
              fC->populateCoreMembers(Sequence_actual_arg, Sequence_actual_arg,
                                      c);
              args->emplace_back(c);
            }
            Sequence_actual_arg = fC->Sibling(Sequence_actual_arg);
          }
          result = seqinst;
          break;
        }
        case VObjectType::paSequence_expr: {
          result = compileExpression(component, fC, child, compileDesign,
                                     reduce, pexpr, instance, muteErrors);
          if (NodeId oper = fC->Sibling(child)) {
            VObjectType type = fC->Type(oper);
            uhdm::Operation *operation = s.make<uhdm::Operation>();
            operation->setParent(pexpr);
            result->setParent(operation, true);
            operation->getOperands(true)->emplace_back(result);
            fC->populateCoreMembers(parent, parent, operation);
            int32_t operationType = UhdmWriter::getVpiOpType(type);
            if (NodeId subOp1 = fC->Child(oper)) {
              VObjectType subOp1type = fC->Type(subOp1);
              if (subOp1type == VObjectType::paPound_Pound_delay) {
                if (NodeId subOp2 = fC->Sibling(subOp1)) {
                  VObjectType subOp2type = fC->Type(subOp2);
                  if (subOp2type == VObjectType::paAssociative_dimension) {
                    operationType = vpiConsecutiveRepeatOp;
                  } else if (subOp2type ==
                             VObjectType::
                                 paCycle_delay_const_range_expression) {
                    uhdm::Range *r = s.make<uhdm::Range>();
                    r->setParent(operation);
                    NodeId lhs = fC->Child(subOp2);
                    NodeId rhs = fC->Sibling(lhs);
                    r->setLeftExpr((uhdm::Expr *)compileExpression(
                        component, fC, lhs, compileDesign, reduce, r, instance,
                        muteErrors));
                    r->setRightExpr((uhdm::Expr *)compileExpression(
                        component, fC, rhs, compileDesign, reduce, r, instance,
                        muteErrors));
                    fC->populateCoreMembers(subOp2, subOp2, r);
                    operation->getOperands()->emplace_back(r);
                  }
                } else {
                  std::string_view val = fC->SymName(subOp1);
                  val.remove_prefix(2);
                  uhdm::Constant *c = s.make<uhdm::Constant>();
                  c->setValue(StrCat("UINT:", val));
                  c->setDecompile(val);
                  c->setSize(64);
                  c->setConstType(vpiUIntConst);
                  c->setParent(operation);
                  fC->populateCoreMembers(subOp1, subOp1, c);
                  operation->getOperands()->emplace_back(c);
                }
              }
            }
            operation->setOpType(operationType);
            if (uhdm::Any *rhs = compileExpression(
                    component, fC, fC->Sibling(oper), compileDesign, reduce,
                    operation, instance, muteErrors)) {
              operation->getOperands()->emplace_back(rhs);
            }
            result = operation;
          }
          break;
        }
        case VObjectType::paConstant_cast:
        case VObjectType::paCast: {
          NodeId Casting_type = fC->Child(child);
          NodeId Simple_type = fC->Child(Casting_type);
          if ((fC->Type(Simple_type) == VObjectType::paSigning_Unsigned) ||
              (fC->Type(Simple_type) == VObjectType::paSigning_Signed)) {
            uhdm::SysFuncCall *sys = s.make<uhdm::SysFuncCall>();
            if (fC->Type(Simple_type) == VObjectType::paSigning_Unsigned)
              sys->setName("$unsigned");
            else
              sys->setName("$signed");
            sys->setParent(pexpr);

            if (Casting_type) {
              if (NodeId Expression = fC->Sibling(Casting_type)) {
                if (uhdm::Any *operand = compileExpression(
                        component, fC, Expression, compileDesign, reduce, sys,
                        instance, muteErrors)) {
                  sys->getArguments(true)->emplace_back(operand);
                }
              }
            }
            result = sys;
          } else {
            uhdm::Operation *operation = s.make<uhdm::Operation>();
            if (attributes != nullptr) {
              operation->setAttributes(attributes);
              for (auto a : *attributes) a->setParent(operation);
            }
            operation->setOpType(vpiCastOp);
            operation->setParent(pexpr);
            fC->populateCoreMembers(parent, parent, operation);

            if (Casting_type) {
              if (NodeId Expression = fC->Sibling(Casting_type)) {
                if (uhdm::Any *operand = compileExpression(
                        component, fC, Expression, compileDesign, reduce,
                        operation, instance, muteErrors)) {
                  operation->getOperands(true)->emplace_back(operand);
                }
              }
            }
            if (m_elaborate == Elaborate::Yes) {
              if (uhdm::Typespec *tps =
                      compileTypespec(component, fC, Simple_type, compileDesign,
                                      reduce, operation, instance, false)) {
                if (operation->getTypespec() == nullptr) {
                  uhdm::RefTypespec *rttps = s.make<uhdm::RefTypespec>();
                  rttps->setName(fC->SymName(Simple_type));
                  fC->populateCoreMembers(Simple_type, Simple_type, rttps);
                  rttps->setParent(operation);
                  operation->setTypespec(rttps);
                }
                operation->getTypespec()->setActual(tps);
              }
            }
            result = operation;
          }
          break;
        }
        case VObjectType::paPackage_scope:
        case VObjectType::paClass_type:
        case VObjectType::paHierarchical_identifier:
        case VObjectType::slStringConst: {
          std::string name;
          Value *sval = nullptr;
          if (childType == VObjectType::paPackage_scope) {
            const std::string_view packageName = fC->SymName(fC->Child(child));
            NodeId paramId = fC->Sibling(child);
            if (fC->Type(paramId) != VObjectType::slStringConst)
              paramId = fC->Child(paramId);
            NodeId selectId = fC->Sibling(paramId);
            const std::string_view n = fC->SymName(paramId);
            name.assign(packageName).append("::").append(n);
            if (m_elaborate == Elaborate::Yes) {
              if (Package *pack = design->getPackage(packageName)) {
                if (uhdm::ParamAssignCollection *param_assigns =
                        pack->getParamAssigns()) {
                  for (uhdm::ParamAssign *param : *param_assigns) {
                    if (param && param->getLhs()) {
                      const std::string_view param_name =
                          param->getLhs()->getName();
                      if (param_name == n) {
                        if (substituteAssignedValue(param->getRhs(),
                                                    compileDesign)) {
                          uhdm::ElaboratorContext elaboratorContext(&s, false,
                                                                    true);
                          result = uhdm::clone_tree(
                              (uhdm::Any *)param->getRhs(), &elaboratorContext);
                          result->setParent(pexpr);
                          fC->populateCoreMembers(child, child, result);
                        }
                        break;
                      }
                    }
                  }
                }
                if (result && selectId) {
                  if (fC->Type(selectId) == VObjectType::paConstant_select) {
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
              // create uhdm::RefObj down below
            }
          } else if (childType == VObjectType::paClass_type) {
            const std::string_view packageName = fC->SymName(fC->Child(child));
            name = packageName;
            std::string n;
            if (fC->Sibling(parent)) {
              n = fC->SymName(fC->Sibling(parent));
              name += "::" + n;
            }
            if ((m_elaborate == Elaborate::Yes) && (m_reduce == Reduce::Yes) &&
                (reduce == Reduce::Yes)) {
              if (Package *pack = design->getPackage(packageName)) {
                if (uhdm::ParamAssignCollection *param_assigns =
                        pack->getParamAssigns()) {
                  for (uhdm::ParamAssign *param : *param_assigns) {
                    if (param && param->getLhs()) {
                      const std::string_view param_name =
                          param->getLhs()->getName();
                      if (param_name == n) {
                        if (substituteAssignedValue(param->getRhs(),
                                                    compileDesign)) {
                          uhdm::ElaboratorContext elaboratorContext(&s, false,
                                                                    true);
                          result = uhdm::clone_tree(
                              (uhdm::Any *)param->getRhs(), &elaboratorContext);
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
              // create uhdm::RefObj down below
            }
          } else {
            NodeId rhs;
            if ((parentType == VObjectType::paHierarchical_identifier) ||
                (parentType == VObjectType::paPs_or_hierarchical_identifier)) {
              rhs = parent;
            } else {
              rhs = child;
            }
            if (fC->Name(child))
              name = fC->SymName(child);
            else {
              NodeId tmp = fC->Child(child);
              if (fC->Type(tmp) == VObjectType::paDollar_root_keyword) {
                tmp = fC->Sibling(tmp);
              }
              name = fC->SymName(tmp);
            }
            NodeId rhsbackup = rhs;
            while ((rhs = fC->Sibling(rhs))) {
              VObjectType type = fC->Type(rhs);
              if (type == VObjectType::slStringConst) {
                if (fC->Type(rhsbackup) == VObjectType::paPackage_scope) {
                  name.append("::").append(fC->SymName(rhs));
                } else {
                  name.append(".").append(fC->SymName(rhs));
                }
              } else if (type == VObjectType::paSelect ||
                         type == VObjectType::paConstant_select) {
                NodeId Bit_select = fC->Child(rhs);
                result = compileSelectExpression(component, fC, Bit_select,
                                                 name, compileDesign, reduce,
                                                 pexpr, instance, muteErrors);
                if (result != nullptr) {
                  fC->populateCoreMembers(rhsbackup, rhs, result);
                }
              } else if ((type == VObjectType::paIncDec_PlusPlus) ||
                         (type == VObjectType::paIncDec_MinusMinus)) {
                uint32_t vopType = UhdmWriter::getVpiOpType(type);
                if (vopType) {
                  uhdm::Operation *op = s.make<uhdm::Operation>();
                  op->setAttributes(attributes);
                  op->setOpType(vopType);
                  op->setParent(pexpr);
                  fC->populateCoreMembers(parent, parent, op);
                  uhdm::RefObj *ref = s.make<uhdm::RefObj>();
                  fC->populateCoreMembers(child, child, ref);
                  ref->setName(name);
                  ref->setParent(op);
                  if (pexpr) {
                    if (uhdm::Any *var =
                            bindVariable(component, pexpr, name, compileDesign))
                      ref->setActual(var);
                  } else if (instance) {
                    if (uhdm::Any *var = bindVariable(component, instance, name,
                                                      compileDesign))
                      ref->setActual(var);
                  }
                  op->getOperands(true)->emplace_back(ref);
                  result = op;
                }
              }
              if (result) break;
            }
            if (result) break;
            if (instance && (m_reduce == Reduce::Yes) &&
                (reduce == Reduce::Yes))
              sval = instance->getValue(name);
          }
          if (result) break;

          if (sval == nullptr || (sval && !sval->isValid())) {
            uhdm::Expr *complexValue = nullptr;
            if (instance &&
                ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes))) {
              if (ModuleInstance *inst =
                      valuedcomponenti_cast<ModuleInstance *>(instance)) {
                if (Netlist *netlist = inst->getNetlist()) {
                  if (uhdm::ParamAssignCollection *param_assigns =
                          netlist->param_assigns()) {
                    for (uhdm::ParamAssign *param_ass : *param_assigns) {
                      if (param_ass && param_ass->getLhs()) {
                        const std::string_view param_name =
                            param_ass->getLhs()->getName();
                        if (param_name == name) {
                          if (param_ass->getRhs() &&
                              (param_ass->getRhs()->getUhdmType() ==
                               uhdm::UhdmType::Constant)) {
                            if (substituteAssignedValue(param_ass->getRhs(),
                                                        compileDesign)) {
                              uhdm::ElaboratorContext elaboratorContext(
                                  &s, false, true);
                              result = uhdm::clone_tree(
                                  (uhdm::Any *)param_ass->getRhs(),
                                  &elaboratorContext);
                              result->setParent(param_ass);
                              fC->populateCoreMembers(child, child, result);
                              uhdm::Typespec *tps = nullptr;
                              const uhdm::Any *lhs = param_ass->getLhs();
                              if (lhs->getUhdmType() ==
                                  uhdm::UhdmType::TypeParameter) {
                                if (uhdm::RefTypespec *lhs_rt =
                                        ((uhdm::TypeParameter *)lhs)
                                            ->getTypespec()) {
                                  tps = lhs_rt->getActual();
                                }
                              } else if (lhs->getUhdmType() ==
                                         uhdm::UhdmType::Parameter) {
                                if (uhdm::RefTypespec *lhs_rt =
                                        ((uhdm::Parameter *)lhs)
                                            ->getTypespec()) {
                                  tps = lhs_rt->getActual();
                                }
                              }
                              uhdm::Expr *res = (uhdm::Expr *)result;
                              if (tps && (res->getTypespec() == nullptr)) {
                                uhdm::RefTypespec *tps_rt =
                                    s.make<uhdm::RefTypespec>();
                                tps_rt->setParent(res);
                                tps_rt->setActual(tps);
                                res->setTypespec(tps_rt);
                              }
                              break;
                            }
                          }
                        }
                      }
                    }
                  }
                }
                if (uhdm::Expr *complex = inst->getComplexValue(name)) {
                  complexValue = complex;
                }
              }
            }
            if (component && (result == nullptr)) {
              if (uhdm::ParamAssignCollection *param_assigns =
                      component->getParamAssigns()) {
                for (uhdm::ParamAssign *param_ass : *param_assigns) {
                  if (param_ass && param_ass->getLhs()) {
                    const std::string_view param_name =
                        param_ass->getLhs()->getName();
                    bool paramFromPackage = false;
                    if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
                        (valuedcomponenti_cast<Package>(component))) {
                      paramFromPackage = true;
                    }
                    if (param_ass->getLhs()->getUhdmType() ==
                        uhdm::UhdmType::Parameter) {
                      const uhdm::Parameter *tp =
                          (uhdm::Parameter *)param_ass->getLhs();
                      if (!tp->getImported().empty()) {
                        paramFromPackage = true;
                      }
                    }
                    if (param_name == name) {
                      if ((m_reduce == Reduce::Yes) &&
                          (reduce == Reduce::Yes) && paramFromPackage &&
                          (param_ass->getRhs()->getUhdmType() ==
                           uhdm::UhdmType::Constant)) {
                        if (substituteAssignedValue(param_ass->getRhs(),
                                                    compileDesign)) {
                          if (complexValue) {
                            result = complexValue;
                          } else {
                            uhdm::ElaboratorContext elaboratorContext(&s, false,
                                                                      true);
                            result = uhdm::clone_tree(
                                (uhdm::Any *)param_ass->getRhs(),
                                &elaboratorContext);
                            result->setParent(param_ass);
                            fC->populateCoreMembers(child, child, result);
                          }
                          uhdm::Typespec *tps = nullptr;
                          const uhdm::Any *lhs = param_ass->getLhs();
                          if (lhs->getUhdmType() ==
                              uhdm::UhdmType::TypeParameter) {
                            if (uhdm::RefTypespec *lhs_rt =
                                    ((uhdm::TypeParameter *)lhs)
                                        ->getTypespec()) {
                              tps = lhs_rt->getActual();
                            }
                          } else if (lhs->getUhdmType() ==
                                     uhdm::UhdmType::Parameter) {
                            if (uhdm::RefTypespec *lhs_rt =
                                    ((uhdm::Parameter *)lhs)->getTypespec()) {
                              tps = lhs_rt->getActual();
                            }
                          }

                          uhdm::Expr *res = (uhdm::Expr *)result;
                          if (tps && (res->getTypespec() == nullptr)) {
                            uhdm::RefTypespec *tps_rt =
                                s.make<uhdm::RefTypespec>();
                            tps_rt->setParent(res);
                            tps_rt->setActual(tps);
                            res->setTypespec(tps_rt);
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
              uhdm::RefObj *ref = s.make<uhdm::RefObj>();
              ref->setName(name);
              ref->setParent(pexpr);
              fC->populateCoreMembers(parent, parent, ref);
              if (pexpr) {
                if (uhdm::Any *var =
                        bindVariable(component, pexpr, name, compileDesign))
                  ref->setActual(var);
              } else if (instance) {
                if (uhdm::Any *var =
                        bindVariable(component, instance, name, compileDesign))
                  ref->setActual(var);
              }
              result = ref;
            }
          } else {
            uhdm::Constant *c = s.make<uhdm::Constant>();
            c->setValue(sval->uhdmValue());
            c->setDecompile(sval->decompiledValue());
            c->setConstType(sval->vpiValType());
            c->setSize(sval->getSize());
            if (sval->isSigned()) {
              uhdm::IntTypespec *ts = s.make<uhdm::IntTypespec>();
              ts->setSigned(true);
              uhdm::RefTypespec *rt = s.make<uhdm::RefTypespec>();
              rt->setParent(c);
              rt->setActual(ts);
              c->setTypespec(rt);
            }
            result = c;
          }
          break;
        }
        case VObjectType::slIntConst:
        case VObjectType::slRealConst:
        case VObjectType::paNumber_1Tickb1:
        case VObjectType::paNumber_1TickB1:
        case VObjectType::paInitVal_1Tickb1:
        case VObjectType::paInitVal_1TickB1:
        case VObjectType::paScalar_1Tickb1:
        case VObjectType::paScalar_1TickB1:
        case VObjectType::pa1:
        case VObjectType::paScalar_Tickb1:
        case VObjectType::paScalar_TickB1:
        case VObjectType::paNumber_Tickb1:
        case VObjectType::paNumber_TickB1:
        case VObjectType::paNumber_Tick1:
        case VObjectType::paNumber_1Tickb0:
        case VObjectType::paNumber_1TickB0:
        case VObjectType::paInitVal_1Tickb0:
        case VObjectType::paInitVal_1TickB0:
        case VObjectType::paScalar_1Tickb0:
        case VObjectType::paScalar_1TickB0:
        case VObjectType::pa0:
        case VObjectType::paScalar_Tickb0:
        case VObjectType::paScalar_TickB0:
        case VObjectType::paNumber_Tickb0:
        case VObjectType::paNumber_TickB0:
        case VObjectType::paNumber_Tick0:
        case VObjectType::paNumber_1TickBX:
        case VObjectType::paNumber_1TickbX:
        case VObjectType::paNumber_1Tickbx:
        case VObjectType::paNumber_1TickBx:
        case VObjectType::paInitVal_1Tickbx:
        case VObjectType::paInitVal_1TickbX:
        case VObjectType::paInitVal_1TickBx:
        case VObjectType::paInitVal_1TickBX:
        case VObjectType::paX:
        case VObjectType::paZ:
        case VObjectType::paTime_literal:
        case VObjectType::slStringLiteral: {
          if ((result = compileConst(fC, child, s))) {
            result->setParent(pexpr);
          }
          break;
        }
        case VObjectType::paStreaming_concatenation: {
          uhdm::Operation *operation = s.make<uhdm::Operation>();
          uhdm::AnyCollection *operands = operation->getOperands(true);
          if (attributes != nullptr) {
            operation->setAttributes(attributes);
            for (auto a : *attributes) a->setParent(operation);
          }
          operation->setParent(pexpr);
          result = operation;
          NodeId Stream_operator = fC->Child(child);
          NodeId Stream_direction = fC->Child(Stream_operator);
          NodeId Slice_size = fC->Sibling(Stream_operator);
          uhdm::Any *exp_slice = nullptr;
          NodeId Stream_concatenation;
          if (fC->Type(Slice_size) == VObjectType::paSlice_size) {
            NodeId Constant_expression = fC->Child(Slice_size);
            if (fC->Type(Constant_expression) == VObjectType::paSimple_type) {
              NodeId Integer_type = fC->Child(Constant_expression);
              NodeId Type = fC->Child(Integer_type);
              exp_slice =
                  compileBits(component, fC, Type, compileDesign, Reduce::Yes,
                              operation, instance, false, muteErrors);
            } else {
              exp_slice = compileExpression(component, fC, Constant_expression,
                                            compileDesign, reduce, operation,
                                            instance, muteErrors);
            }
            Stream_concatenation = fC->Sibling(Slice_size);
          } else {
            Stream_concatenation = Slice_size;
          }

          fC->populateCoreMembers(child, child, operation);
          if (fC->Type(Stream_direction) == VObjectType::paBinOp_ShiftRight)
            operation->setOpType(vpiStreamLROp);
          else
            operation->setOpType(vpiStreamRLOp);
          if (exp_slice) operands->emplace_back(exp_slice);

          uhdm::Operation *concat_op = s.make<uhdm::Operation>();
          uhdm::AnyCollection *concat_ops = concat_op->getOperands(true);
          operands->emplace_back(concat_op);
          concat_op->setParent(operation);
          concat_op->setOpType(vpiConcatOp);
          fC->populateCoreMembers(Stream_concatenation, Stream_concatenation,
                                  concat_op);

          NodeId Stream_expression = fC->Child(Stream_concatenation);
          while (Stream_expression) {
            NodeId Expression = fC->Child(Stream_expression);
            if (uhdm::Any *exp_var = compileExpression(
                    component, fC, Expression, compileDesign, reduce, concat_op,
                    instance, muteErrors)) {
              concat_ops->emplace_back(exp_var);
            }
            Stream_expression = fC->Sibling(Stream_expression);
          }
          break;
        }
        case VObjectType::paEmpty_queue: {
          uhdm::ArrayVar *var = s.make<uhdm::ArrayVar>();
          var->setParent(pexpr);
          fC->populateCoreMembers(parent, parent, var);
          uhdm::RefTypespec *rt = s.make<uhdm::RefTypespec>();
          rt->setParent(var);
          uhdm::ArrayTypespec *at = s.make<uhdm::ArrayTypespec>();
          at->setParent(var);
          fC->populateCoreMembers(parent, parent, at);
          rt->setActual(at);
          fC->populateCoreMembers(parent, parent, rt);
          var->setTypespec(rt);
          var->setArrayType(vpiQueueArray);
          result = var;
          break;
        }
        case VObjectType::paConstant_concatenation:
        case VObjectType::paConcatenation: {
          uhdm::Operation *operation = s.make<uhdm::Operation>();
          operation->setParent(pexpr);
          operation->setOpType(vpiConcatOp);
          fC->populateCoreMembers(parent, parent, operation);

          uhdm::AnyCollection *operands = operation->getOperands(true);
          NodeId Expression = fC->Child(child);
          if (attributes != nullptr) {
            operation->setAttributes(attributes);
            for (auto a : *attributes) a->setParent(operation);
          }
          result = operation;
          while (Expression) {
            if (uhdm::Any *exp = compileExpression(
                    component, fC, Expression, compileDesign, reduce, operation,
                    instance, muteErrors)) {
              exp->setParent(operation);
              operands->emplace_back(exp);
            }
            Expression = fC->Sibling(Expression);
          }
          break;
        }
        case VObjectType::paConstant_multiple_concatenation:
        case VObjectType::paMultiple_concatenation: {
          uhdm::Operation *operation = s.make<uhdm::Operation>();
          operation->setParent(pexpr);
          operation->setOpType(vpiMultiConcatOp);
          fC->populateCoreMembers(parent, parent, operation);

          uhdm::AnyCollection *operands = operation->getOperands(true);
          if (attributes != nullptr) {
            operation->setAttributes(attributes);
            for (auto a : *attributes) a->setParent(operation);
          }
          result = operation;
          NodeId NCopy = fC->Child(child);
          if (uhdm::Any *exp =
                  compileExpression(component, fC, NCopy, compileDesign, reduce,
                                    operation, instance, muteErrors)) {
            operands->emplace_back(exp);
          }
          NodeId Concatenation = fC->Sibling(NCopy);
          if (uhdm::Any *exp =
                  compileExpression(component, fC, Concatenation, compileDesign,
                                    reduce, operation, instance, muteErrors)) {
            operands->emplace_back(exp);
          }
          break;
        }
        case VObjectType::paSubroutine_call: {
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
                     fC->Type(Dollar_keyword) == VObjectType::paClass_scope) {
            if (fC->Type(Dollar_keyword) == VObjectType::paClass_scope) {
              NodeId Class_type = fC->Child(Dollar_keyword);
              NodeId Class_type_name = fC->Child(Class_type);
              NodeId Class_scope_name = fC->Sibling(Dollar_keyword);
              name.assign(fC->SymName(Class_type_name))
                  .append("::")
                  .append(fC->SymName(Class_scope_name));
            }
            NodeId Select = fC->Sibling(Dollar_keyword);
            if (fC->Type(Select) == VObjectType::paConstant_bit_select ||
                fC->Type(Select) == VObjectType::paBit_select) {
              result = compileExpression(component, fC, Dollar_keyword,
                                         compileDesign, reduce, pexpr, instance,
                                         muteErrors);
            } else {
              bool invalidValue = false;
              uhdm::FuncCall *fcall = s.make<uhdm::FuncCall>();
              fcall->setName(name);
              fcall->setParent(pexpr);
              fC->populateCoreMembers(Dollar_keyword, List_of_arguments, fcall);

              auto [func, actual_comp] =
                  getTaskFunc(name, component, compileDesign, instance, pexpr);
              fcall->setFunction(any_cast<uhdm::Function>(func));
              uhdm::AnyCollection *args = compileTfCallArguments(
                  component, fC, List_of_arguments, compileDesign, reduce,
                  fcall, instance, muteErrors);
              if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes)) {
                PathId fileId = fC->getFileId();
                uint32_t lineNumber = fC->Line(nameId);
                if (func == nullptr) {
                  ErrorContainer *const errors = m_session->getErrorContainer();
                  SymbolTable *const symbols = m_session->getSymbolTable();
                  Location loc(fileId, lineNumber, fC->Column(nameId),
                               symbols->registerSymbol(name));
                  Error err(ErrorDefinition::COMP_UNDEFINED_USER_FUNCTION, loc);
                  errors->addError(err);
                }
                result = EvalFunc(
                    any_cast<uhdm::Function>(func), args, invalidValue,
                    (instance) ? actual_comp : component, compileDesign,
                    instance, fileId, lineNumber, pexpr);
              }
              if (result == nullptr || invalidValue == true) {
                fcall->setArguments(args);
                result = fcall;
              }
            }
          } else {
            uhdm::SysFuncCall *sys = s.make<uhdm::SysFuncCall>();
            sys->setName("$" + name);
            sys->setParent(pexpr);
            if (uhdm::AnyCollection *arguments = compileTfCallArguments(
                    component, fC, List_of_arguments, compileDesign, reduce,
                    sys, instance, muteErrors)) {
              sys->setArguments(arguments);
            }
            result = sys;
          }
          break;
        }
        case VObjectType::paData_type:
          // When trying to evaluate type parameters
          if (m_checkForLoops) {
            m_stackLevel--;
          }
          return nullptr;
        case VObjectType::paCycle_delay_const_range_expression: {
          uhdm::Range *r = s.make<uhdm::Range>();
          r->setParent(pexpr);

          NodeId lhs = fC->Child(child);
          NodeId rhs = fC->Sibling(lhs);
          r->setLeftExpr(
              (uhdm::Expr *)compileExpression(component, fC, lhs, compileDesign,
                                              reduce, r, instance, muteErrors));
          r->setRightExpr(
              (uhdm::Expr *)compileExpression(component, fC, rhs, compileDesign,
                                              reduce, r, instance, muteErrors));
          fC->populateCoreMembers(parent, parent, r);
          result = r;
          break;
        }
        case VObjectType::paCycle_delay_range: {
          VObjectType type = fC->Type(child);
          uhdm::Operation *operation = s.make<uhdm::Operation>();
          operation->setParent(pexpr);
          fC->populateCoreMembers(parent, parent, operation);

          uhdm::AnyCollection *operands = operation->getOperands(true);
          int32_t operationType = UhdmWriter::getVpiOpType(type);
          if (NodeId subOp1 = fC->Child(child)) {
            VObjectType subOp1type = fC->Type(subOp1);
            if (subOp1type == VObjectType::paPound_Pound_delay) {
              operationType = vpiUnaryCycleDelayOp;
              if (NodeId subOp2 = fC->Sibling(subOp1)) {
                VObjectType subOp2type = fC->Type(subOp2);
                if (subOp2type == VObjectType::paAssociative_dimension) {
                  operationType = vpiConsecutiveRepeatOp;
                } else if (subOp2type ==
                           VObjectType::paCycle_delay_const_range_expression) {
                  uhdm::Range *r = s.make<uhdm::Range>();
                  NodeId lhs = fC->Child(subOp2);
                  NodeId rhs = fC->Sibling(lhs);
                  r->setLeftExpr((uhdm::Expr *)compileExpression(
                      component, fC, lhs, compileDesign, reduce, r, instance,
                      muteErrors));
                  r->setRightExpr((uhdm::Expr *)compileExpression(
                      component, fC, rhs, compileDesign, reduce, r, instance,
                      muteErrors));
                  fC->populateCoreMembers(subOp2, subOp2, r);
                  operands->emplace_back(r);
                }
              } else {
                std::string_view val = fC->SymName(subOp1);
                val.remove_prefix(2);
                uhdm::Constant *c = s.make<uhdm::Constant>();
                c->setParent(operation);
                c->setValue(StrCat("UINT:", val));
                c->setDecompile(val);
                c->setSize(64);
                c->setConstType(vpiUIntConst);
                fC->populateCoreMembers(subOp1, subOp1, c);
                operands->emplace_back(c);
              }
            }
          }
          operation->setOpType(operationType);
          if (uhdm::Any *rhs = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, reduce,
                  operation, instance, muteErrors)) {
            operands->emplace_back(rhs);
          }
          result = operation;
          break;
        }
        case VObjectType::paProperty_expr: {
          uhdm::Expr *subexp = (uhdm::Expr *)compileExpression(
              component, fC, child, compileDesign, reduce, pexpr, instance,
              muteErrors);
          if (NodeId sib = fC->Sibling(child)) {
            VObjectType type = fC->Type(sib);
            switch (type) {
              case VObjectType::paOR:
              case VObjectType::paAND:
              case VObjectType::paUNTIL:
              case VObjectType::paS_UNTIL:
              case VObjectType::paUNTIL_WITH:
              case VObjectType::paS_UNTIL_WITH: {
                int32_t optype = UhdmWriter::getVpiOpType(type);
                uhdm::Operation *oper = s.make<uhdm::Operation>();
                oper->setParent(pexpr);
                oper->setOpType(optype);
                fC->populateCoreMembers(parent, parent, oper);
                uhdm::AnyCollection *operands = oper->getOperands(true);
                subexp->setParent(oper);
                operands->emplace_back(subexp);
                NodeId nop = fC->Sibling(sib);
                if (uhdm::Expr *nexp = (uhdm::Expr *)compileExpression(
                        component, fC, nop, compileDesign, reduce, oper,
                        instance, muteErrors)) {
                  operands->emplace_back(nexp);
                }
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
        case VObjectType::paClass_scope: {
          NodeId Class_type = fC->Child(child);
          NodeId Class_type_name = fC->Child(Class_type);
          NodeId Class_scope_name = fC->Sibling(child);
          std::string name = StrCat(fC->SymName(Class_type_name),
                                    "::", fC->SymName(Class_scope_name));
          uhdm::RefObj *ref = s.make<uhdm::RefObj>();
          ref->setName(name);
          ref->setParent(pexpr);
          fC->populateCoreMembers(child, child, ref);
          result = ref;
          break;
        }
        case VObjectType::paACCEPT_ON:
        case VObjectType::paREJECT_ON:
        case VObjectType::paSYNC_ACCEPT_ON:
        case VObjectType::paSYNC_REJECT_ON:
        case VObjectType::paALWAYS:
        case VObjectType::paS_ALWAYS:
        case VObjectType::paEVENTUALLY:
        case VObjectType::paS_EVENTUALLY:
        case VObjectType::paNEXTTIME:
        case VObjectType::paS_NEXTTIME: {
          VObjectType type = childType;
          uhdm::Operation *operation = s.make<uhdm::Operation>();
          operation->setParent(pexpr);
          fC->populateCoreMembers(parent, parent, operation);
          operation->setOpType(UhdmWriter::getVpiOpType(type));

          uhdm::AnyCollection *operands = operation->getOperands(true);
          if (uhdm::Any *rhs = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, reduce,
                  operation, instance, muteErrors)) {
            operands->emplace_back(rhs);
          }
          result = operation;
          break;
        }
        case VObjectType::paClocking_event: {
          if (fC->Type(fC->Sibling(child)) == VObjectType::paSequence_expr) {
            uhdm::ClockedSeq *seq = s.make<uhdm::ClockedSeq>();
            seq->setParent(pexpr);

            NodeId endLocationId = child;
            if (uhdm::Any *cev = compileExpression(
                    component, fC, fC->Child(child), compileDesign, reduce, seq,
                    instance, muteErrors)) {
              seq->setClockingEvent((uhdm::Expr *)cev);
              endLocationId = fC->Child(child);
            }
            if (uhdm::Any *ex = compileExpression(
                    component, fC, fC->Sibling(child), compileDesign, reduce,
                    seq, instance, muteErrors)) {
              seq->setSequenceExpr(ex);
              endLocationId = fC->Sibling(child);
            }
            fC->populateCoreMembers(child, endLocationId, seq);
            result = seq;
          } else {
            uhdm::ClockedProperty *prop = s.make<uhdm::ClockedProperty>();
            prop->setParent(pexpr);
            if (uhdm::Any *cev = compileExpression(
                    component, fC, fC->Child(child), compileDesign, reduce,
                    prop, instance, muteErrors)) {
              prop->setClockingEvent((uhdm::Expr *)cev);
            }
            if (uhdm::Any *ex = compileExpression(
                    component, fC, fC->Sibling(child), compileDesign, reduce,
                    prop, instance, muteErrors)) {
              prop->setPropertyExpr(ex);
            }
            result = prop;
          }
          break;
        }
        default:
          break;
      }
    } else {
      VObjectType type = fC->Type(parent);
      switch (type) {
        case VObjectType::paIncDec_PlusPlus:
        case VObjectType::paIncDec_MinusMinus:
        case VObjectType::paUnary_Minus:
        case VObjectType::paUnary_Plus:
        case VObjectType::paUnary_Tilda:
        case VObjectType::paUnary_Not:
        case VObjectType::paUnary_BitwOr:
        case VObjectType::paUnary_BitwAnd:
        case VObjectType::paUnary_BitwXor:
        case VObjectType::paUnary_ReductNand:
        case VObjectType::paUnary_ReductNor:
        case VObjectType::paUnary_ReductXnor1:
        case VObjectType::paUnary_ReductXnor2: {
          uint32_t vopType = UhdmWriter::getVpiOpType(type);
          if (vopType) {
            uhdm::Operation *op = s.make<uhdm::Operation>();
            if (attributes != nullptr) {
              op->setAttributes(attributes);
              for (auto a : *attributes) a->setParent(op);
            }
            op->setOpType(vopType);
            op->setParent(pexpr);
            fC->populateCoreMembers(parent, fC->Sibling(parent), op);
            if (uhdm::Any *operand = compileExpression(
                    component, fC, fC->Sibling(parent), compileDesign, reduce,
                    op, instance, muteErrors)) {
              op->getOperands(true)->emplace_back(operand);
            }
            result = op;
          }
          break;
        }
        case VObjectType::paNull_keyword: {
          uhdm::Constant *c = s.make<uhdm::Constant>();
          c->setValue("UINT:0");
          c->setDecompile("0");
          c->setSize(64);
          c->setConstType(vpiNullConst);
          c->setParent(pexpr);
          result = c;
          break;
        }
        case VObjectType::paDollar_keyword: {
          uhdm::Constant *c = s.make<uhdm::Constant>();
          c->setConstType(vpiUnboundedConst);
          c->setValue("STRING:$");
          c->setDecompile("$");
          c->setSize(1);
          c->setParent(pexpr);
          result = c;
          break;
        }
        case VObjectType::paThis_keyword: {
          // TODO: To be changed to class var
          uhdm::Constant *c = s.make<uhdm::Constant>();
          c->setConstType(vpiStringConst);
          c->setValue("STRING:this");
          c->setDecompile("this");
          c->setSize(4);
          c->setParent(pexpr);
          result = c;
          break;
        }
        case VObjectType::paSuper_keyword: {
          // TODO: To be changed to class var
          uhdm::Constant *c = s.make<uhdm::Constant>();
          c->setConstType(vpiStringConst);
          c->setValue("STRING:super");
          c->setDecompile("super");
          c->setSize(5);
          c->setParent(pexpr);
          result = c;
          break;
        }
        case VObjectType::paThis_dot_super: {
          // TODO: To be changed to class var
          uhdm::Constant *c = s.make<uhdm::Constant>();
          c->setConstType(vpiStringConst);
          c->setValue("STRING:this.super");
          c->setDecompile("this.super");
          c->setSize(10);
          c->setParent(pexpr);
          result = c;
          break;
        }
        case VObjectType::paConstraint_block: {
          // Empty constraint block
          uhdm::Constraint *cons = s.make<uhdm::Constraint>();
          cons->setParent(pexpr);
          result = cons;
          break;
        }
        case VObjectType::slIntConst:
        case VObjectType::slRealConst:
        case VObjectType::paNumber_1Tickb1:
        case VObjectType::paNumber_1TickB1:
        case VObjectType::paInitVal_1Tickb1:
        case VObjectType::paInitVal_1TickB1:
        case VObjectType::paScalar_1Tickb1:
        case VObjectType::paScalar_1TickB1:
        case VObjectType::pa1:
        case VObjectType::paScalar_Tickb1:
        case VObjectType::paScalar_TickB1:
        case VObjectType::paNumber_Tickb1:
        case VObjectType::paNumber_TickB1:
        case VObjectType::paNumber_Tick1:
        case VObjectType::paNumber_1Tickb0:
        case VObjectType::paNumber_1TickB0:
        case VObjectType::paInitVal_1Tickb0:
        case VObjectType::paInitVal_1TickB0:
        case VObjectType::paScalar_1Tickb0:
        case VObjectType::paScalar_1TickB0:
        case VObjectType::pa0:
        case VObjectType::paScalar_Tickb0:
        case VObjectType::paScalar_TickB0:
        case VObjectType::paNumber_Tickb0:
        case VObjectType::paNumber_TickB0:
        case VObjectType::paNumber_Tick0:
        case VObjectType::paNumber_1TickBX:
        case VObjectType::paNumber_1TickbX:
        case VObjectType::paNumber_1Tickbx:
        case VObjectType::paNumber_1TickBx:
        case VObjectType::paInitVal_1Tickbx:
        case VObjectType::paInitVal_1TickbX:
        case VObjectType::paInitVal_1TickBx:
        case VObjectType::paInitVal_1TickBX:
        case VObjectType::paX:
        case VObjectType::paZ:
        case VObjectType::paTime_literal:
        case VObjectType::slStringLiteral: {
          if ((result = compileConst(fC, parent, s))) {
            result->setParent(pexpr);
          }
          break;
        }
        case VObjectType::slStringConst:
        case VObjectType::paDollar_root_keyword: {
          result = compileComplexFuncCall(component, fC, parent, compileDesign,
                                          reduce, pexpr, instance, muteErrors);
          break;
        }
        case VObjectType::paArray_member_label: {
          uhdm::RefObj *ref = s.make<uhdm::RefObj>();
          ref->setName("default");
          ref->setParent(pexpr);
          ref->setStructMember(true);
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
    if (exprtype != VObjectType::paEND) {
      ErrorContainer *const errors = m_session->getErrorContainer();
      SymbolTable *const symbols = m_session->getSymbolTable();
      uhdm::UnsupportedExpr *exp = s.make<uhdm::UnsupportedExpr>();
      std::string lineText;
      fileSystem->readLine(fC->getFileId(), fC->Line(the_node), lineText);
      Location loc(fC->getFileId(the_node), fC->Line(the_node),
                   fC->Column(the_node),
                   symbols->registerSymbol(
                       StrCat("<", fC->printObject(the_node), "> ", lineText)));
      Error err(ErrorDefinition::UHDM_UNSUPPORTED_EXPR, loc);
      errors->addError(err);
      exp->setValue(StrCat("STRING:", lineText));
      fC->populateCoreMembers(the_node, the_node, exp);
      exp->setParent(pexpr);
      result = exp;
    }
  }

  if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
      (result != nullptr)) {
    // Reduce
    bool invalidValue = false;
    if (uhdm::Any *tmp = reduceExpr(
            result, invalidValue, component, compileDesign, instance,
            fC->getFileId(the_node), fC->Line(the_node), pexpr, muteErrors)) {
      if (!invalidValue) result = tmp;
    }
  }

  if (result) {
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

uhdm::Any *CompileHelper::compileAssignmentPattern(
    DesignComponent *component, const FileContent *fC,
    NodeId Assignment_pattern, CompileDesign *compileDesign, Reduce reduce,
    uhdm::Any *pexpr, ValuedComponentI *instance) {
  SymbolTable *const symbols = m_session->getSymbolTable();
  FileSystem *const fileSystem = m_session->getFileSystem();
  uhdm::Serializer &s = compileDesign->getSerializer();
  uhdm::Any *result = nullptr;
  uhdm::Operation *operation = s.make<uhdm::Operation>();
  uhdm::AnyCollection *operands = operation->getOperands(true);
  result = operation;
  operation->setParent(pexpr);
  operation->setOpType(vpiAssignmentPatternOp);
  fC->populateCoreMembers(Assignment_pattern, Assignment_pattern, operation);

  if (component && valuedcomponenti_cast<Package>(component)) {
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
  if (fC->Type(Structure_pattern_key) == VObjectType::paExpression ||
      fC->Type(Structure_pattern_key) == VObjectType::paConstant_expression) {
    with_key = false;
  }
  if (!with_key &&
      fC->Type(Structure_pattern_key) == VObjectType::paConstant_expression) {
    // '{2{1}}
    NodeId Expression = Structure_pattern_key;
    if (uhdm::Any *exp =
            compileExpression(component, fC, Expression, compileDesign, reduce,
                              operation, instance, false)) {
      Expression = fC->Sibling(Expression);
      operands->emplace_back(exp);
      operation->setOpType(vpiMultiAssignmentPatternOp);
      uhdm::Operation *concat = s.make<uhdm::Operation>();
      concat->setOpType(vpiConcatOp);
      operands->emplace_back(concat);
      concat->setParent(operation);
      NodeId firstExpression = Expression;
      NodeId lastExpression = Expression;
      uhdm::AnyCollection *suboperands = concat->getOperands(true);
      while (Expression) {
        if (uhdm::Any *val =
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, concat, instance, false)) {
          suboperands->emplace_back(val);
        }
        lastExpression = Expression;
        Expression = fC->Sibling(Expression);
      }
      fC->populateCoreMembers(firstExpression, lastExpression, concat);
    }
    return result;
  }
  while (Structure_pattern_key) {
    NodeId Expression;
    if (!with_key) {
      Expression = Structure_pattern_key;
      if (Expression) {
        // No key '{1,2,...}
        if (uhdm::Any *exp =
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, operation, instance, false)) {
          operands->emplace_back(exp);
        }
      }
    } else {
      Expression =
          fC->Sibling(Structure_pattern_key);  // With key '{a: 1, b: 2,...}

      if (Expression) {
        uhdm::TaggedPattern *pattern = s.make<uhdm::TaggedPattern>();
        if (uhdm::Any *exp =
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, pattern, instance, false)) {
          if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes)) {
            if (exp->getUhdmType() == uhdm::UhdmType::Operation) {
              uhdm::Operation *op = (uhdm::Operation *)exp;
              bool reduceMore = true;
              int32_t opType = op->getOpType();
              if (opType == vpiConcatOp) {
                if (op->getOperands()->size() != 1) {
                  reduceMore = false;
                }
              }
              if (reduceMore) {
                bool invalidValue = false;
                if (uhdm::Any *tmp = reduceExpr(
                        exp, invalidValue, component, compileDesign, instance,
                        fileSystem->toPathId(op->getFile(), symbols),
                        op->getStartLine(), nullptr, true)) {
                  if (!invalidValue) exp = tmp;
                }
              }
            }

            if (exp->getUhdmType() == uhdm::UhdmType::RefObj) {
              uhdm::RefObj *ref = (uhdm::RefObj *)exp;
              const std::string_view name = ref->getName();
              if (uhdm::Any *tmp = getValue(
                      name, component, compileDesign, Reduce::Yes, instance,
                      fC->getFileId(), fC->Line(Expression), pattern, true)) {
                exp = tmp;
                fC->populateCoreMembers(Expression, Expression, exp);
              }
            }
          }
          pattern->setPattern(exp);
          NodeId Constant_expression = fC->Child(Structure_pattern_key);
          NodeId Constant_primary = fC->Child(Constant_expression);
          if (!Constant_primary) {
            uhdm::StringTypespec *tps = s.make<uhdm::StringTypespec>();
            if (fC->Type(Constant_expression) == VObjectType::slStringConst) {
              tps->setName(fC->SymName(Constant_expression));
            } else {
              tps->setName("default");
            }
            fC->populateCoreMembers(Constant_expression, Constant_expression,
                                    tps);
            tps->setParent(pattern);
            if (pattern->getTypespec() == nullptr) {
              uhdm::RefTypespec *rt = s.make<uhdm::RefTypespec>();
              if (fC->Type(Constant_expression) == VObjectType::slStringConst) {
                rt->setName(fC->SymName(Constant_expression));
              }
              rt->setParent(pattern);
              fC->populateCoreMembers(Constant_expression, Constant_expression,
                                      rt);
              pattern->setTypespec(rt);
            }
            pattern->getTypespec()->setActual(tps);
            fC->populateCoreMembers(Constant_expression, Expression, pattern);
          } else {
            NodeId Primary_literal = Constant_primary;
            if (fC->Type(Primary_literal) != VObjectType::paPrimary_literal)
              Primary_literal = fC->Child(Constant_primary);
            if (uhdm::Typespec *tps = compileTypespec(
                    component, fC, Primary_literal, compileDesign, Reduce::Yes,
                    nullptr, instance, false)) {
              if (pattern->getTypespec() == nullptr) {
                uhdm::RefTypespec *rt = s.make<uhdm::RefTypespec>();
                rt->setParent(pattern);
                fC->populateCoreMembers(Primary_literal, Primary_literal, rt);
                pattern->setTypespec(rt);
              }
              pattern->getTypespec()->setActual(tps);
            }
          }
          pattern->setParent(operation);
          fC->populateCoreMembers(Constant_expression, Expression, pattern);
          operands->emplace_back(pattern);
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
                                            uhdm::Expr *exp,
                                            CompileDesign *compileDesign,
                                            ValuedComponentI *instance) {
  FileSystem *const fileSystem = m_session->getFileSystem();
  if (exp == nullptr) return false;
  if (exp->getUhdmType() != uhdm::UhdmType::Constant) return false;
  const std::string_view val = exp->getValue();
  return errorOnNegativeConstant(
      component, val, compileDesign, instance,
      fileSystem->toPathId(exp->getFile(), m_session->getSymbolTable()),
      exp->getStartLine(), exp->getStartColumn());
}

bool CompileHelper::errorOnNegativeConstant(DesignComponent *component,
                                            std::string_view val,
                                            CompileDesign *compileDesign,
                                            ValuedComponentI *instance,
                                            PathId fileId, uint32_t lineNo,
                                            uint16_t columnNo) {
  FileSystem *const fileSystem = m_session->getFileSystem();
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
    SymbolTable *symbols = m_session->getSymbolTable();
    std::string lineText;
    fileSystem->readLine(fileId, lineNo, lineText);
    StrAppend(&message, "             text: ", lineText, "\n");
    StrAppend(&message, "             value: ", val);
    ErrorContainer *errors = m_session->getErrorContainer();
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
              std::cout << ps->getLhs()->getName() << " = \n";
              decompile((uhdm::Any *)ps->getRhs());
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

uhdm::RangeCollection *CompileHelper::compileRanges(
    DesignComponent *component, const FileContent *fC, NodeId Packed_dimension,
    CompileDesign *compileDesign, Reduce reduce, uhdm::Any *pexpr,
    ValuedComponentI *instance, int32_t &size, bool muteErrors) {
  FileSystem *const fileSystem = m_session->getFileSystem();
  uhdm::Serializer &s = compileDesign->getSerializer();
  uhdm::RangeCollection *ranges = nullptr;
  size = 0;
  if (Packed_dimension &&
      ((fC->Type(Packed_dimension) == VObjectType::paPacked_dimension) ||
       (fC->Type(Packed_dimension) == VObjectType::paUnpacked_dimension) ||
       (fC->Type(Packed_dimension) == VObjectType::paVariable_dimension) ||
       (fC->Type(Packed_dimension) == VObjectType::paConstant_range) ||
       (fC->Type(Packed_dimension) == VObjectType::paUnsized_dimension))) {
    ranges = s.makeCollection<uhdm::Range>();
    size = 1;
    while (Packed_dimension) {
      NodeId Constant_range = fC->Child(Packed_dimension);
      if (fC->Type(Packed_dimension) == VObjectType::paConstant_range) {
        Constant_range = Packed_dimension;
      }
      if (fC->Type(Constant_range) == VObjectType::paUnpacked_dimension ||
          fC->Type(Constant_range) == VObjectType::paPacked_dimension) {
        Constant_range = fC->Child(Constant_range);
      }
      if (fC->Type(Constant_range) == VObjectType::paConstant_range) {
        // Specified by range
        NodeId lexpr = fC->Child(Constant_range);
        NodeId rexpr = fC->Sibling(lexpr);
        uhdm::Range *range = s.make<uhdm::Range>();

        uhdm::Expr *lexp = any_cast<uhdm::Expr *>(
            compileExpression(component, fC, lexpr, compileDesign, reduce,
                              range, instance, muteErrors));
        if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes)) {
          if (errorOnNegativeConstant(component, lexp, compileDesign,
                                      instance)) {
            bool replay = false;
            // GDB: p replay=true
            if (replay) {
              compileExpression(component, fC, lexpr, compileDesign, reduce,
                                range, instance, muteErrors);
            }
          }
        }

        if (lexp) {
          lexp->setParent(range);
          range->setLeftExpr(lexp);
        }
        uhdm::Expr *rexp = any_cast<uhdm::Expr *>(
            compileExpression(component, fC, rexpr, compileDesign, reduce,
                              range, instance, muteErrors));
        if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes)) {
          if (errorOnNegativeConstant(component, rexp, compileDesign,
                                      instance)) {
            bool replay = false;
            // GDB: p replay=true
            if (replay) {
              compileExpression(component, fC, rexpr, compileDesign, reduce,
                                range, instance, muteErrors);
            }
          }
        }
        if (rexp) {
          rexp->setParent(range);
          range->setRightExpr(rexp);
        }
        if ((lexp) && (rexp) && (m_reduce == Reduce::Yes) &&
            (reduce == Reduce::Yes)) {
          uhdm::ExprEval eval;
          bool invalidValue = false;
          lexp =
              reduceExpr(lexp, invalidValue, component, compileDesign, instance,
                         fC->getFileId(), fC->Line(lexpr), pexpr, muteErrors);
          rexp =
              reduceExpr(rexp, invalidValue, component, compileDesign, instance,
                         fC->getFileId(), fC->Line(rexpr), pexpr, muteErrors);
          uint64_t lint = eval.get_value(invalidValue, lexp);
          uint64_t rint = eval.get_value(invalidValue, rexp);
          if (lexp) {
            lexp->setParent(range);
            range->setLeftExpr(lexp);
          }
          if (rexp) {
            rexp->setParent(range);
            range->setRightExpr(rexp);
          }
          if (!invalidValue) {
            uint64_t tmp = (lint > rint) ? lint - rint + 1 : rint - lint + 1;
            size = size * tmp;
          }
        }
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, range);
        ranges->emplace_back(range);
        range->setParent(pexpr);
      } else if (fC->Type(Constant_range) ==
                 VObjectType::paConstant_expression) {
        // Specified by size
        NodeId rexpr = Constant_range;
        uhdm::Range *range = s.make<uhdm::Range>();
        range->setParent(pexpr);
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, range);

        if (m_elaborate == Elaborate::Yes) {
          uhdm::Constant *lexpc = s.make<uhdm::Constant>();
          lexpc->setConstType(vpiUIntConst);
          lexpc->setSize(64);
          lexpc->setValue("UINT:0");
          lexpc->setDecompile("0");
          range->setLeftExpr(lexpc);
          lexpc->setParent(range);
        }
        if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes)) {
          Value *rightV = m_exprBuilder.evalExpr(fC, rexpr, instance, true);
          if (rightV->isValid()) {
            int64_t rint = rightV->getValueL();
            size = size * rint;
          }
        }

        uhdm::Expr *rexp = any_cast<uhdm::Expr *>(
            compileExpression(component, fC, rexpr, compileDesign, reduce,
                              range, instance, muteErrors));
        bool associativeArray = false;
        if (rexp && (rexp->getUhdmType() == uhdm::UhdmType::Constant)) {
          uhdm::Constant *c = (uhdm::Constant *)rexp;
          const std::string_view val = c->getValue();
          if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
              ((val == "UINT:0") || (val == "INT:0") || (val[4] == '-'))) {
            ErrorContainer *errors = m_session->getErrorContainer();
            SymbolTable *symbols = m_session->getSymbolTable();
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
          if (c->getConstType() == vpiUnboundedConst) associativeArray = true;
        }
        if (rexp && (rexp->getUhdmType() == uhdm::UhdmType::RefObj) &&
            (reduce == Reduce::Yes)) {
          if (uhdm::Typespec *assoc_tps =
                  compileTypespec(component, fC, rexpr, compileDesign, reduce,
                                  nullptr, instance, true)) {
            associativeArray = true;
            uhdm::Range *range = s.make<uhdm::Range>();
            fC->populateCoreMembers(Packed_dimension, Packed_dimension, range);

            uhdm::Constant *lexpc = s.make<uhdm::Constant>();
            lexpc->setConstType(vpiUIntConst);
            lexpc->setSize(64);
            lexpc->setValue("UINT:0");
            lexpc->setDecompile("0");
            lexpc->setParent(range);
            fC->populateCoreMembers(InvalidNodeId, InvalidNodeId, lexpc);
            range->setLeftExpr(lexpc);

            uhdm::Constant *rexpc = s.make<uhdm::Constant>();
            rexpc->setConstType(vpiStringConst);
            rexpc->setSize(0);
            rexpc->setValue("STRING:associative");
            rexpc->setDecompile("associative");
            rexpc->setParent(range);
            fC->populateCoreMembers(InvalidNodeId, InvalidNodeId, rexpc);
            range->setRightExpr(rexpc);

            uhdm::RefTypespec *assoc_tps_rt = s.make<uhdm::RefTypespec>();
            assoc_tps_rt->setName(assoc_tps->getName());
            assoc_tps_rt->setParent(rexpc);
            assoc_tps_rt->setActual(assoc_tps);
            fC->populateCoreMembers(rexpr, rexpr, assoc_tps_rt);
            rexpc->setTypespec(assoc_tps_rt);

            range->setParent(pexpr);
            ranges->emplace_back(range);
            Packed_dimension = fC->Sibling(Packed_dimension);
            continue;
          }
        }
        if (!associativeArray) {
          uhdm::Operation *op = s.make<uhdm::Operation>();  // Decr by 1
          op->setOpType(vpiSubOp);
          op->getOperands(true)->emplace_back(rexp);
          fC->populateCoreMembers(Constant_range, Constant_range, op);

          if (m_elaborate == Elaborate::Yes) {
            uhdm::Constant *one = s.make<uhdm::Constant>();
            one->setValue("INT:1");
            one->setConstType(vpiIntConst);
            one->setSize(64);
            one->setParent(op);
            fC->populateCoreMembers(Constant_range, Constant_range, one);
            op->getOperands(true)->emplace_back(one);
          }

          rexp->setParent(op, true);
          op->setParent(range);
          rexp = op;
        }

        if (rexp) range->setRightExpr(rexp);
        fC->populateCoreMembers(Constant_range, Constant_range, range);
        ranges->emplace_back(range);
        range->setParent(pexpr);
      } else if ((fC->Type(fC->Child(Packed_dimension)) ==
                  VObjectType::paUnsized_dimension) ||
                 (fC->Type(Packed_dimension) ==
                  VObjectType::paUnsized_dimension)) {
        uhdm::Range *range = s.make<uhdm::Range>();

        fC->populateCoreMembers(Packed_dimension, Packed_dimension, range);
        uhdm::Constant *lexpc = s.make<uhdm::Constant>();
        lexpc->setConstType(vpiUIntConst);
        lexpc->setSize(64);
        lexpc->setValue("UINT:0");
        lexpc->setDecompile("0");
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, lexpc);
        lexpc->setEndColumn(fC->Column(Packed_dimension) + 1);
        range->setLeftExpr(lexpc);
        lexpc->setParent(range);

        uhdm::Constant *rexpc = s.make<uhdm::Constant>();
        rexpc->setConstType(vpiStringConst);
        rexpc->setSize(0);
        rexpc->setValue("STRING:unsized");
        rexpc->setDecompile("unsized");
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, rexpc);
        rexpc->setEndColumn(fC->Column(Packed_dimension) + 1);
        range->setRightExpr(rexpc);
        range->setParent(pexpr);
        rexpc->setParent(range);
        ranges->emplace_back(range);
      } else if (fC->Type(fC->Child(Packed_dimension)) ==
                 VObjectType::paAssociative_dimension) {
        NodeId DataType = fC->Child(fC->Child(Packed_dimension));
        uhdm::Range *range = s.make<uhdm::Range>();
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, range);

        uhdm::Constant *lexpc = s.make<uhdm::Constant>();
        lexpc->setConstType(vpiUIntConst);
        lexpc->setSize(64);
        lexpc->setValue("UINT:0");
        lexpc->setDecompile("0");
        lexpc->setParent(range);
        range->setLeftExpr(lexpc);
        fC->populateCoreMembers(InvalidNodeId, InvalidNodeId, lexpc);

        uhdm::Constant *rexpc = s.make<uhdm::Constant>();
        rexpc->setConstType(vpiStringConst);
        rexpc->setSize(0);
        rexpc->setValue("STRING:associative");
        rexpc->setDecompile("associative");
        rexpc->setParent(range);
        range->setRightExpr(rexpc);
        fC->populateCoreMembers(InvalidNodeId, InvalidNodeId, rexpc);

        if (uhdm::Typespec *assoc_tps =
                compileTypespec(component, fC, DataType, compileDesign, reduce,
                                nullptr, instance, true)) {
          uhdm::RefTypespec *assoc_tps_rt = s.make<uhdm::RefTypespec>();
          assoc_tps_rt->setParent(rexpc);
          assoc_tps_rt->setActual(assoc_tps);
          fC->populateCoreMembers(DataType, DataType, assoc_tps_rt);
          rexpc->setTypespec(assoc_tps_rt);
        }

        range->setParent(pexpr);
        ranges->emplace_back(range);
      }
      Packed_dimension = fC->Sibling(Packed_dimension);
    }
  }
  return ranges;
}

uhdm::Any *CompileHelper::compilePartSelectRange(
    DesignComponent *component, const FileContent *fC, NodeId Constant_range,
    std::string_view name, CompileDesign *compileDesign, Reduce reduce,
    uhdm::Any *pexpr, ValuedComponentI *instance, bool muteErrors) {
  uhdm::Serializer &s = compileDesign->getSerializer();
  uhdm::Any *result = nullptr;
  NodeId Constant_expression = fC->Child(Constant_range);
  if (fC->Type(Constant_range) == VObjectType::paConstant_range) {
    uhdm::PartSelect *part_select = s.make<uhdm::PartSelect>();
    if (name.find("::") != std::string::npos) {
      part_select->setFullName(name);
    }
    fC->populateCoreMembers(Constant_expression,
                            fC->Sibling(Constant_expression), part_select);
    if (uhdm::Expr *lexp = (uhdm::Expr *)compileExpression(
            component, fC, Constant_expression, compileDesign, Reduce::No,
            part_select, instance)) {
      lexp->setParent(part_select);
      part_select->setLeftExpr(lexp);
    }
    if (uhdm::Expr *rexp = (uhdm::Expr *)compileExpression(
            component, fC, fC->Sibling(Constant_expression), compileDesign,
            Reduce::No, part_select, instance)) {
      rexp->setParent(part_select);
      part_select->setRightExpr(rexp);
    }
    if (!name.empty() && (name != "CREATE_UNNAMED_PARENT")) {
      part_select->setName(name);
      part_select->setDefName(name);
    }
    part_select->setParent(pexpr);
    part_select->setConstantSelect(true);
    result = part_select;
  } else {
    // constant_indexed_range
    uhdm::IndexedPartSelect *part_select = s.make<uhdm::IndexedPartSelect>();
    if (uhdm::Expr *lexp = (uhdm::Expr *)compileExpression(
            component, fC, Constant_expression, compileDesign, reduce,
            part_select, instance, muteErrors)) {
      lexp->setParent(part_select);
      part_select->setBaseExpr(lexp);
    }
    NodeId op = fC->Sibling(Constant_expression);
    if (uhdm::Expr *rexp = (uhdm::Expr *)compileExpression(
            component, fC, fC->Sibling(op), compileDesign, reduce, part_select,
            instance, muteErrors)) {
      rexp->setParent(part_select);
      part_select->setWidthExpr(rexp);
    }
    if (fC->Type(op) == VObjectType::paIncPartSelectOp)
      part_select->setIndexedPartSelectType(vpiPosIndexed);
    else
      part_select->setIndexedPartSelectType(vpiNegIndexed);
    if (!name.empty() && (name != "CREATE_UNNAMED_PARENT")) {
      part_select->setName(name);
      part_select->setDefName(name);
    }
    part_select->setParent(pexpr);
    part_select->setConstantSelect(true);
    result = part_select;

    if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) &&
        (part_select->getBaseExpr()->getUhdmType() ==
         uhdm::UhdmType::Constant) &&
        (part_select->getWidthExpr()->getUhdmType() ==
         uhdm::UhdmType::Constant)) {
      bool invalidValue = false;
      result = reduceExpr(result, invalidValue, component, compileDesign,
                          instance, BadPathId, 0, pexpr, muteErrors);
    }
  }
  if (result != nullptr) {
    fC->populateCoreMembers(Constant_range, Constant_range, result);
  }
  return result;
}

uint64_t CompileHelper::Bits(const uhdm::Any *typespec, bool &invalidValue,
                             DesignComponent *component,
                             CompileDesign *compileDesign, Reduce reduce,
                             ValuedComponentI *instance, PathId fileId,
                             uint32_t lineNumber, bool sizeMode) {
  if (loopDetected(fileId, lineNumber, compileDesign, instance)) {
    return 0;
  }
  Design *const design = compileDesign->getCompiler()->getDesign();
  if (m_checkForLoops) {
    m_stackLevel++;
  }
  if (typespec) {
    const std::string_view name = typespec->getName();
    if (name.find("::") != std::string::npos) {
      std::vector<std::string_view> res;
      StringUtils::tokenizeMulti(name, "::", res);
      if (res.size() > 1) {
        const std::string_view packName = res[0];
        if (Package *pack = design->getPackage(packName)) {
          component = pack;
        }
      }
    }
  }

  uhdm::GetObjectFunctor getObjectFunctor =
      [&](std::string_view name, const uhdm::Any *inst,
          const uhdm::Any *pexpr) -> uhdm::Any * {
    return getObject(name, component, compileDesign, instance, pexpr);
  };
  uhdm::GetObjectFunctor getValueFunctor =
      [&](std::string_view name, const uhdm::Any *inst,
          const uhdm::Any *pexpr) -> uhdm::Any * {
    return (uhdm::Expr *)getValue(name, component, compileDesign, Reduce::Yes,
                                  instance, fileId, lineNumber,
                                  (uhdm::Any *)pexpr, false);
  };
  uhdm::GetTaskFuncFunctor getTaskFuncFunctor =
      [&](std::string_view name, const uhdm::Any *inst) -> uhdm::TaskFunc * {
    auto ret = getTaskFunc(name, component, compileDesign, instance, nullptr);
    return ret.first;
  };
  uhdm::ExprEval eval;
  eval.setGetObjectFunctor(getObjectFunctor);
  eval.setGetValueFunctor(getValueFunctor);
  eval.setGetTaskFuncFunctor(getTaskFuncFunctor);
  if (m_exprEvalPlaceHolder == nullptr) {
    m_exprEvalPlaceHolder = compileDesign->getSerializer().make<uhdm::Module>();
    m_exprEvalPlaceHolder->getParamAssigns(true);
  } else {
    m_exprEvalPlaceHolder->getParamAssigns()->erase(
        m_exprEvalPlaceHolder->getParamAssigns()->begin(),
        m_exprEvalPlaceHolder->getParamAssigns()->end());
  }
  uint64_t size = eval.size(typespec, invalidValue, m_exprEvalPlaceHolder,
                            nullptr, !sizeMode);
  if (m_checkForLoops) {
    m_stackLevel--;
  }
  return size;
}

const uhdm::Typespec *getMemberTypespec(
    const uhdm::Typespec *tpss, const std::vector<std::string> &suffixes,
    uint32_t index) {
  const uhdm::Typespec *result = nullptr;
  if (tpss == nullptr) return result;
  if (tpss->getUhdmType() == uhdm::UhdmType::StructTypespec) {
    const uhdm::StructTypespec *ts = (const uhdm::StructTypespec *)tpss;
    for (uhdm::TypespecMember *memb : *ts->getMembers()) {
      if (memb->getName() == suffixes[index]) {
        if (const uhdm::RefTypespec *rt = memb->getTypespec()) {
          result = rt->getActual();
        }
        if (result && (index < (suffixes.size() - 1))) {
          if (result->getUhdmType() == uhdm::UhdmType::StructTypespec) {
            result = getMemberTypespec(result, suffixes, index + 1);
          }
        }
        break;
      }
    }
  }
  return result;
}

const uhdm::Typespec *CompileHelper::getTypespec(
    DesignComponent *component, const FileContent *fC, NodeId id,
    CompileDesign *compileDesign, Reduce reduce, ValuedComponentI *instance) {
  if (loopDetected(fC->getFileId(), fC->Line(id), compileDesign, instance)) {
    return nullptr;
  }
  uhdm::Serializer &s = compileDesign->getSerializer();
  Design *const design = compileDesign->getCompiler()->getDesign();
  const DataType *dtype = nullptr;
  const uhdm::Typespec *result = nullptr;
  std::string basename;
  std::vector<std::string> suffixnames;
  switch (fC->Type(id)) {
    case VObjectType::paIntegerAtomType_Byte: {
      result = s.make<uhdm::ByteTypespec>();
      break;
    }
    case VObjectType::paIntegerAtomType_Int: {
      result = s.make<uhdm::IntTypespec>();
      break;
    }
    case VObjectType::paIntegerAtomType_Integer: {
      result = s.make<uhdm::IntegerTypespec>();
      break;
    }
    case VObjectType::paIntegerAtomType_LongInt: {
      result = s.make<uhdm::LongIntTypespec>();
      break;
    }
    case VObjectType::paIntegerAtomType_Shortint: {
      result = s.make<uhdm::ShortIntTypespec>();
      break;
    }
    case VObjectType::paIntegerAtomType_Time: {
      result = s.make<uhdm::TimeTypespec>();
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
    case VObjectType::paComplex_func_call: {
      if (uhdm::Any *exp =
              compileExpression(component, fC, fC->Parent(id), compileDesign,
                                reduce, nullptr, instance, false)) {
        if (exp->getUhdmType() == uhdm::UhdmType::HierPath) {
          bool invalidValue = false;
          result = (uhdm::Typespec *)decodeHierPath(
              (uhdm::HierPath *)exp, invalidValue, component, compileDesign,
              reduce, instance, fC->getFileId(), fC->Line(id), nullptr, false,
              true);
        } else if (exp->getUhdmType() == uhdm::UhdmType::BitSelect) {
          uhdm::BitSelect *select = (uhdm::BitSelect *)exp;
          basename = select->getName();
        } else if (exp->getUhdmType() == uhdm::UhdmType::RefObj) {
          basename = exp->getName();
          if (basename.find("::") != std::string::npos) {
            std::vector<std::string_view> res;
            StringUtils::tokenizeMulti(basename, "::", res);
            if (res.size() > 1) {
              const std::string_view packName = res[0];
              const std::string_view typeName = res[1];
              if (Package *p = design->getPackage(packName)) {
                dtype = p->getDataType(design, typeName);
              }
            }
          }
        } else if (exp->getUhdmType() == uhdm::UhdmType::VarSelect) {
          uhdm::VarSelect *select = (uhdm::VarSelect *)exp;
          basename = select->getName();
        } else {
          basename = exp->getName();
        }
      }
      break;
    }
    case VObjectType::paIntVec_TypeLogic: {
      result = s.make<uhdm::LogicTypespec>();
      break;
    }
    case VObjectType::paIntVec_TypeBit: {
      result = s.make<uhdm::BitTypespec>();
      break;
    }
    case VObjectType::paIntVec_TypeReg: {
      result = s.make<uhdm::LogicTypespec>();
      break;
    }
    case VObjectType::paClass_scope: {
      NodeId Class_type = fC->Child(id);
      NodeId Class_type_name = fC->Child(Class_type);
      NodeId Class_scope_name = fC->Sibling(id);
      basename.assign(fC->SymName(Class_type_name))
          .append("::")
          .append(fC->SymName(Class_scope_name));
      if (Package *p = design->getPackage(fC->SymName(Class_type_name)))
        dtype = p->getDataType(design, fC->SymName(Class_scope_name));
      break;
    }
    case VObjectType::paPackage_scope: {
      const std::string_view packageName = fC->SymName(fC->Child(id));
      const std::string_view n = fC->SymName(fC->Sibling(id));
      basename.assign(packageName).append("::").append(n);
      if (Package *p = design->getPackage(packageName))
        dtype = p->getDataType(design, n);
      break;
    }
    default:
      break;
  }

  if (dtype == nullptr) {
    if (component) dtype = component->getDataType(design, basename);
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
      if (NodeId sigTypeId = sig->getTypespecId()) {
        result = compileTypespec(
            sig->getComponent(), fC, sigTypeId, compileDesign, reduce,
            sig->getComponent()->getUhdmModel(), instance, true);
        NodeId Unpacked_dimension = sig->getUnpackedDimension();
        if (fC->Type(Unpacked_dimension) != VObjectType::sl_INVALID_) {
          uhdm::ArrayTypespec *array = s.make<uhdm::ArrayTypespec>();
          int32_t size;
          if (uhdm::RangeCollection *ranges = compileRanges(
                  component, fC, Unpacked_dimension, compileDesign, reduce,
                  array, instance, size, false)) {
            array->setRanges(ranges);
          }
          uhdm::RefTypespec *rt = s.make<uhdm::RefTypespec>();
          rt->setParent(array);
          rt->setActual(const_cast<uhdm::Typespec *>(result));
          array->setElemTypespec(rt);
          fC->populateCoreMembers(
              sigTypeId, Unpacked_dimension ? Unpacked_dimension : sigTypeId,
              array);
          result = array;
        }
      } else {
        NodeId Packed_dimension = sig->getPackedDimension();
        if (fC->Type(Packed_dimension) != VObjectType::sl_INVALID_) {
          NodeId DataType = fC->Parent(Packed_dimension);
          result = compileTypespec(
              sig->getComponent(), fC, DataType, compileDesign, reduce,
              sig->getComponent()->getUhdmModel(), instance, false);
        }
        NodeId Unpacked_dimension = sig->getUnpackedDimension();
        if (fC->Type(Unpacked_dimension) != VObjectType::sl_INVALID_) {
          uhdm::ArrayTypespec *array = s.make<uhdm::ArrayTypespec>();
          int32_t size;
          if (uhdm::RangeCollection *ranges = compileRanges(
                  component, fC, Unpacked_dimension, compileDesign, reduce,
                  array, instance, size, false)) {
            array->setRanges(ranges);
          }
          if (result == nullptr) {
            result = compileBuiltinTypespec(
                sig->getComponent(), fC, sig->getNodeId(), sig->getType(),
                compileDesign, nullptr, sig->getComponent()->getUhdmModel());
          }
          uhdm::RefTypespec *rt = s.make<uhdm::RefTypespec>();
          rt->setParent(array);
          rt->setActual(const_cast<uhdm::Typespec *>(result));
          array->setElemTypespec(rt);
          result = array;
        }
      }
    }
  }
  while (dtype) {
    if (const TypeDef *typed = datatype_cast<const TypeDef *>(dtype)) {
      const DataType *dt = typed->getDataType();
      if (const Enum *en = datatype_cast<const Enum *>(dt)) {
        result = en->getTypespec();
        break;
      }
      if (const Struct *st = datatype_cast<const Struct *>(dt)) {
        result = st->getTypespec();
        if (!suffixnames.empty()) {
          result = getMemberTypespec(result, suffixnames, 0);
        }
        break;
      }
      if (const Union *un = datatype_cast<const Union *>(dt)) {
        result = un->getTypespec();
        break;
      }
      if (const SimpleType *sit = datatype_cast<const SimpleType *>(dt)) {
        result = sit->getTypespec();
        break;
      }
    }
    dtype = dtype->getDefinition();
  }

  if (result == nullptr) {
    if (ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(instance)) {
      if (Netlist *netlist = inst->getNetlist()) {
        if (netlist->ports()) {
          for (uhdm::Port *p : *netlist->ports()) {
            if (p->getName() == basename) {
              const uhdm::Typespec *tps = nullptr;
              if (const uhdm::RefTypespec *rt = p->getTypespec()) {
                tps = rt->getActual();
              }
              if (!suffixnames.empty()) {
                result = getMemberTypespec(tps, suffixnames, 0);
              }
            }
            if (result) break;
          }
        }
        if (netlist->param_assigns()) {
          for (uhdm::ParamAssign *pass : *netlist->param_assigns()) {
            const uhdm::Any *param = pass->getLhs();
            if (param->getName() == basename) {
              if (param->getUhdmType() == uhdm::UhdmType::Parameter) {
                uhdm::Parameter *p = (uhdm::Parameter *)param;
                if (const uhdm::RefTypespec *rt = p->getTypespec()) {
                  result = rt->getActual();
                }
              } else {
                uhdm::TypeParameter *p = (uhdm::TypeParameter *)param;
                if (const uhdm::RefTypespec *rt = p->getTypespec()) {
                  result = rt->getActual();
                }
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

uhdm::Any *CompileHelper::compileBits(
    DesignComponent *component, const FileContent *fC, NodeId List_of_arguments,
    CompileDesign *compileDesign, Reduce reduce, uhdm::Any *pexpr,
    ValuedComponentI *instance, bool sizeMode, bool muteErrors) {
  uhdm::Serializer &s = compileDesign->getSerializer();
  uhdm::Any *result = nullptr;
  NodeId callId = List_of_arguments;
  VObjectType callType = VObjectType::paSubroutine_call;
  if (NodeId id = fC->sl_parent(List_of_arguments, {callType}, callType)) {
    callId = id;
  }
  NodeId Expression = List_of_arguments;
  if (fC->Type(Expression) == VObjectType::paList_of_arguments) {
    Expression = fC->Child(Expression);
  } else if (fC->Type(Expression) == VObjectType::paData_type) {
    Expression = fC->Child(Expression);
  }
  NodeId typeSpecId;
  uint64_t bits = 0;
  bool invalidValue = false;
  const uhdm::Typespec *tps = nullptr;
  const uhdm::Any *exp = nullptr;
  switch (fC->Type(Expression)) {
    case VObjectType::paIntegerAtomType_Byte:
    case VObjectType::paIntegerAtomType_Int:
    case VObjectType::paIntegerAtomType_Integer:
    case VObjectType::paIntegerAtomType_LongInt:
    case VObjectType::paIntegerAtomType_Shortint:
    case VObjectType::paIntegerAtomType_Time:
    case VObjectType::paIntVec_TypeLogic:
    case VObjectType::paIntVec_TypeBit:
    case VObjectType::paIntVec_TypeReg:
      typeSpecId = Expression;
      break;
    default: {
      NodeId Primary = fC->Child(Expression);
      NodeId Primary_literal = fC->Child(Primary);
      if (fC->Type(Primary_literal) == VObjectType::paConcatenation) {
        NodeId ConcatExpression = fC->Child(Primary_literal);
        while (ConcatExpression) {
          NodeId Primary = fC->Child(ConcatExpression);
          NodeId Primary_literal = fC->Child(Primary);
          NodeId StringConst = fC->Child(Primary_literal);
          typeSpecId = StringConst;
          tps = getTypespec(component, fC, typeSpecId, compileDesign, reduce,
                            instance);
          if ((m_elaborate == Elaborate::Yes) && (reduce == Reduce::No) &&
              tps) {
            uhdm::ExprEval eval;
            if (eval.isFullySpecified(tps)) {
              reduce = Reduce::Yes;
            }
          }
          if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) && tps) {
            bits += Bits(tps, invalidValue, component, compileDesign, reduce,
                         instance, fC->getFileId(typeSpecId),
                         fC->Line(typeSpecId), sizeMode);
          }
          ConcatExpression = fC->Sibling(ConcatExpression);
        }
      } else if (fC->Type(Primary_literal) ==
                 VObjectType::paComplex_func_call) {
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
    if ((m_elaborate == Elaborate::Yes) && (reduce == Reduce::No) && tps) {
      uhdm::ExprEval eval;
      if (eval.isFullySpecified(tps)) {
        reduce = Reduce::Yes;
      }
    }
    if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) && tps) {
      bits = Bits(tps, invalidValue, component, compileDesign, reduce, instance,
                  fC->getFileId(typeSpecId), fC->Line(typeSpecId), sizeMode);
    }

    if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) && (!tps)) {
      exp = compileExpression(component, fC, Expression, compileDesign,
                              Reduce::Yes, pexpr, instance, true);
      if (exp && typeSpecId) {
        bits =
            Bits(exp, invalidValue, component, compileDesign, reduce, instance,
                 fC->getFileId(typeSpecId), fC->Line(typeSpecId), sizeMode);
      }
    }
  }

  if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) && tps &&
      (!invalidValue)) {
    uhdm::Constant *c = s.make<uhdm::Constant>();
    c->setValue("UINT:" + std::to_string(bits));
    c->setDecompile(std::to_string(bits));
    c->setConstType(vpiUIntConst);
    c->setSize(64);
    c->setParent(pexpr);
    result = c;
  } else if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) && exp &&
             (!invalidValue)) {
    uhdm::Constant *c = s.make<uhdm::Constant>();
    c->setValue("UINT:" + std::to_string(bits));
    c->setDecompile(std::to_string(bits));
    c->setConstType(vpiUIntConst);
    c->setSize(64);
    c->setParent(pexpr);
    result = c;
  } else if (sizeMode) {
    uhdm::SysFuncCall *sys = s.make<uhdm::SysFuncCall>();
    sys->setName("$size");
    sys->setParent(pexpr);
    fC->populateCoreMembers(callId, callId, sys);
    if (uhdm::AnyCollection *arguments = compileTfCallArguments(
            component, fC, List_of_arguments, compileDesign, reduce, sys,
            instance, muteErrors)) {
      sys->setArguments(arguments);
    }
    result = sys;
  } else {
    uhdm::SysFuncCall *sys = s.make<uhdm::SysFuncCall>();
    sys->setName("$bits");
    sys->setParent(pexpr);
    fC->populateCoreMembers(callId, callId, sys);
    if (uhdm::AnyCollection *arguments = compileTfCallArguments(
            component, fC, List_of_arguments, compileDesign, reduce, sys,
            instance, muteErrors)) {
      sys->setArguments(arguments);
    }
    result = sys;
  }

  return result;
}

uhdm::Any *CompileHelper::compileTypename(DesignComponent *component,
                                          const FileContent *fC,
                                          NodeId Expression,
                                          CompileDesign *compileDesign,
                                          Reduce reduce, uhdm::Any *pexpr,
                                          ValuedComponentI *instance) {
  uhdm::Serializer &s = compileDesign->getSerializer();
  uhdm::Any *result = nullptr;
  uhdm::Constant *c = s.make<uhdm::Constant>();
  if (fC->Type(Expression) == VObjectType::paData_type) {
    Expression = fC->Child(Expression);
    if (fC->Type(Expression) == VObjectType::paVIRTUAL)
      Expression = fC->Sibling(Expression);
  }
  VObjectType type = fC->Type(Expression);
  switch (type) {
    case VObjectType::paIntVec_TypeLogic:
      c->setValue("STRING:logic");
      c->setDecompile("logic");
      c->setConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntVec_TypeBit:
      c->setValue("STRING:bit");
      c->setDecompile("bit");
      c->setConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntVec_TypeReg:
      c->setValue("STRING:reg");
      c->setDecompile("reg");
      c->setConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntegerAtomType_Byte:
      c->setValue("STRING:byte");
      c->setDecompile("byte");
      c->setConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntegerAtomType_Shortint:
      c->setValue("STRING:shortint");
      c->setDecompile("shortint");
      c->setConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntegerAtomType_Int:
      c->setValue("STRING:int");
      c->setDecompile("int");
      c->setConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntegerAtomType_Integer:
      c->setValue("STRING:integer");
      c->setDecompile("integer");
      c->setConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntegerAtomType_LongInt:
      c->setValue("STRING:longint");
      c->setDecompile("longint");
      c->setConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntegerAtomType_Time:
      c->setValue("STRING:time");
      c->setDecompile("time");
      c->setConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paNonIntType_ShortReal:
      c->setValue("STRING:shortreal");
      c->setDecompile("shortreal");
      c->setConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paNonIntType_Real:
      c->setValue("STRING:real");
      c->setDecompile("real");
      c->setConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paNonIntType_RealTime:
      c->setValue("STRING:realtime");
      c->setDecompile("realtime");
      c->setConstType(vpiStringConst);
      result = c;
      break;
    default:
      uhdm::SysFuncCall *sys = s.make<uhdm::SysFuncCall>();
      sys->setName("$typename");
      sys->setParent(pexpr);
      result = sys;
      const std::string_view arg = fC->SymName(Expression);
      c->setValue(StrCat("STRING:", arg));
      c->setDecompile(arg);
      c->setConstType(vpiStringConst);
      c->setParent(sys);
      break;
  }
  return result;
}

uhdm::Any *CompileHelper::compileBound(
    DesignComponent *component, const FileContent *fC, NodeId List_of_arguments,
    CompileDesign *compileDesign, Reduce reduce, uhdm::Any *pexpr,
    ValuedComponentI *instance, bool muteErrors, std::string_view name) {
  uhdm::Serializer &s = compileDesign->getSerializer();
  uhdm::Any *result = nullptr;
  NodeId Expression = List_of_arguments;
  if (fC->Type(Expression) == VObjectType::paList_of_arguments) {
    Expression = fC->Child(Expression);
  }
  if (uhdm::Expr *operand = (uhdm::Expr *)compileExpression(
          component, fC, Expression, compileDesign, Reduce::No, pexpr, instance,
          muteErrors)) {
    const uhdm::Typespec *ts = nullptr;
    if (const uhdm::RefTypespec *rt = operand->getTypespec()) {
      ts = rt->getActual();
    }
    uhdm::RangeCollection *ranges = nullptr;
    if (ts) {
      switch (ts->getUhdmType()) {
        case uhdm::UhdmType::BitTypespec: {
          uhdm::BitTypespec *bts = (uhdm::BitTypespec *)ts;
          ranges = bts->getRanges();
          break;
        }
        case uhdm::UhdmType::IntTypespec: {
          uhdm::IntTypespec *bts = (uhdm::IntTypespec *)ts;
          ranges = bts->getRanges();
          break;
        }
        case uhdm::UhdmType::LogicTypespec: {
          uhdm::LogicTypespec *bts = (uhdm::LogicTypespec *)ts;
          ranges = bts->getRanges();
          break;
        }
        case uhdm::UhdmType::ArrayTypespec: {
          uhdm::ArrayTypespec *bts = (uhdm::ArrayTypespec *)ts;
          ranges = bts->getRanges();
          break;
        }
        case uhdm::UhdmType::PackedArrayTypespec: {
          uhdm::PackedArrayTypespec *bts = (uhdm::PackedArrayTypespec *)ts;
          ranges = bts->getRanges();
          break;
        }
        default:
          break;
      }
    }
    if (ranges) {
      uhdm::Range *r = ranges->at(0);
      uhdm::Expr *lr = r->getLeftExpr();
      uhdm::Expr *rr = r->getRightExpr();
      bool invalidValue = false;
      lr = reduceExpr(lr, invalidValue, component, compileDesign, instance,
                      BadPathId, 0, nullptr, true);
      uhdm::ExprEval eval;
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
  uhdm::SysFuncCall *sys = s.make<uhdm::SysFuncCall>();
  sys->setName(StrCat("$", name));
  sys->setParent(pexpr);
  if (uhdm::AnyCollection *arguments = compileTfCallArguments(
          component, fC, List_of_arguments, compileDesign, reduce, sys,
          instance, muteErrors)) {
    sys->setArguments(arguments);
  }
  result = sys;
  return result;
}

uhdm::Any *CompileHelper::compileClog2(
    DesignComponent *component, const FileContent *fC, NodeId List_of_arguments,
    CompileDesign *compileDesign, Reduce reduce, uhdm::Any *pexpr,
    ValuedComponentI *instance, bool muteErrors) {
  uhdm::Serializer &s = compileDesign->getSerializer();
  uhdm::Any *result = nullptr;
  NodeId Expression = List_of_arguments;
  if (fC->Type(Expression) == VObjectType::paList_of_arguments) {
    Expression = fC->Child(Expression);
  }

  bool invalidValue = false;
  int64_t val = 0;
  if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes)) {
    uhdm::Expr *operand = (uhdm::Expr *)compileExpression(
        component, fC, Expression, compileDesign, reduce, pexpr, instance,
        muteErrors);
    uhdm::ExprEval eval;
    val = eval.get_value(
        invalidValue,
        reduceExpr(operand, invalidValue, component, compileDesign, instance,
                   fC->getFileId(), fC->Line(Expression), pexpr, muteErrors));
  }
  if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) && !invalidValue) {
    val = val - 1;
    uint64_t clog2 = 0;
    for (; val > 0; clog2 = clog2 + 1) {
      val = val >> 1;
    }
    uhdm::Constant *c = s.make<uhdm::Constant>();
    c->setValue("UINT:" + std::to_string(clog2));
    c->setDecompile(std::to_string(clog2));
    c->setConstType(vpiUIntConst);
    c->setSize(64);
    result = c;
  } else {
    uhdm::SysFuncCall *sys = s.make<uhdm::SysFuncCall>();
    sys->setName("$clog2");
    sys->setParent(pexpr);
    NodeId sysTaskId = List_of_arguments;
    while (sysTaskId && (fC->Type(sysTaskId) != VObjectType::paSystem_task) &&
           (fC->Type(sysTaskId) != VObjectType::paSubroutine_call) &&
           (fC->Type(sysTaskId) != VObjectType::paComplex_func_call)) {
      sysTaskId = fC->Parent(sysTaskId);
    }
    if (sysTaskId) fC->populateCoreMembers(sysTaskId, sysTaskId, sys);
    if (uhdm::AnyCollection *arguments = compileTfCallArguments(
            component, fC, List_of_arguments, compileDesign, reduce, sys,
            instance, muteErrors)) {
      sys->setArguments(arguments);
    }
    result = sys;
  }
  return result;
}

uhdm::Any *CompileHelper::compileComplexFuncCall(
    DesignComponent *component, const FileContent *fC, NodeId id,
    CompileDesign *compileDesign, Reduce reduce, uhdm::Any *pexpr,
    ValuedComponentI *instance, bool muteErrors) {
  Design *const design = compileDesign->getCompiler()->getDesign();
  NodeId name =
      (fC->Type(id) == VObjectType::paComplex_func_call) ? fC->Child(id) : id;
  uhdm::Serializer &s = compileDesign->getSerializer();
  uhdm::Any *result = nullptr;
  NodeId dotedName = fC->Sibling(name);

  bool hierPath = false;
  NodeId tmp = dotedName;
  while (fC->Type(tmp) == VObjectType::paAttribute_instance) {
    tmp = fC->Sibling(tmp);
    dotedName = tmp;
  }
  NodeId List_of_arguments;
  while (tmp) {
    if (fC->Type(tmp) == VObjectType::slStringConst ||
        fC->Type(tmp) == VObjectType::paMethod_call_body ||
        fC->Type(tmp) == VObjectType::paSubroutine_call) {
      hierPath = true;
    } else if (fC->Type(tmp) == VObjectType::paList_of_arguments) {
      List_of_arguments = tmp;
    }
    tmp = fC->Sibling(tmp);
  }

  if (fC->Type(name) == VObjectType::paDollar_root_keyword) {
    uhdm::HierPath *path = s.make<uhdm::HierPath>();
    path->setParent(pexpr);
    uhdm::AnyCollection *elems = path->getPathElems(true);
    NodeId Dollar_root_keyword = name;
    uhdm::RefObj *ref = s.make<uhdm::RefObj>();
    elems->emplace_back(ref);
    ref->setName("$root");
    ref->setFullName("$root");
    ref->setParent(path);
    fC->populateCoreMembers(Dollar_root_keyword, Dollar_root_keyword, ref);

    std::string name = "$root";
    NodeId nameId = fC->Sibling(Dollar_root_keyword);
    while (nameId) {
      if (fC->Type(nameId) == VObjectType::slStringConst) {
        name.append(".").append(fC->SymName(nameId));
        ref = s.make<uhdm::RefObj>();
        ref->setName(fC->SymName(nameId));
        ref->setFullName(fC->SymName(nameId));
        ref->setParent(path);
        fC->populateCoreMembers(nameId, nameId, ref);
        elems->emplace_back(ref);
      } else if (fC->Type(nameId) == VObjectType::paConstant_expression) {
        if (NodeId Constant_expresion = fC->Child(nameId)) {
          uhdm::BitSelect *sel = s.make<uhdm::BitSelect>();
          sel->setParent(path);
          fC->populateCoreMembers(Constant_expresion, Constant_expresion, sel);
          if (uhdm::Expr *select = (uhdm::Expr *)compileExpression(
                  component, fC, Constant_expresion, compileDesign, reduce, sel,
                  instance, muteErrors)) {
            std::string bsname = decompileHelper(select);
            name += "." + bsname;
            sel->setName(bsname);
            sel->setIndex(select);
          }
          elems->emplace_back(sel);
        }
      } else {
        break;
      }
      nameId = fC->Sibling(nameId);
    }
    path->setName(name);
    path->setParent(pexpr);
    if (!elems->empty()) {
      path->setStartLine(elems->front()->getStartLine());
      path->setStartColumn(elems->front()->getStartColumn());
      path->setEndLine(elems->back()->getEndLine());
      path->setEndColumn(elems->back()->getEndColumn());
    }
    result = path;
  } else if (fC->Type(name) == VObjectType::paDollar_keyword) {
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
      uhdm::SysFuncCall *sys = s.make<uhdm::SysFuncCall>();
      sys->setName(StrCat("$", name));
      sys->setParent(pexpr);
      if (uhdm::AnyCollection *arguments = compileTfCallArguments(
              component, fC, List_of_arguments, compileDesign, reduce, sys,
              instance, muteErrors)) {
        sys->setArguments(arguments);
      }
      result = sys;
    }
  } else if (fC->Type(name) == VObjectType::paImplicit_class_handle) {
    NodeId Handle = fC->Child(name);
    NodeId Method = fC->Sibling(name);
    if (!Method) {
      return compileExpression(component, fC, Handle, compileDesign, reduce,
                               pexpr, instance, muteErrors);
    }
    std::string_view rootName = fC->SymName(Method);
    if (fC->Type(Handle) == VObjectType::paThis_keyword) {
      rootName = "this";
    } else if (fC->Type(Handle) == VObjectType::paSuper_keyword) {
      rootName = "super";
    } else if (fC->Type(Handle) == VObjectType::paThis_dot_super) {
      rootName = "super";
    }
    NodeId List_of_arguments = fC->Sibling(Method);
    if (fC->Type(List_of_arguments) == VObjectType::paList_of_arguments) {
      uhdm::MethodFuncCall *fcall = s.make<uhdm::MethodFuncCall>();
      if (uhdm::Expr *object = (uhdm::Expr *)compileExpression(
              component, fC, Handle, compileDesign, reduce, fcall, instance,
              muteErrors)) {
        fcall->setPrefix(object);
      }
      fcall->setParent(pexpr);
      const std::string_view methodName = fC->SymName(Method);
      fcall->setName(methodName);
      if ((rootName == "super") || (rootName == "this"))
        fC->populateCoreMembers(name, List_of_arguments, fcall);
      else
        fC->populateCoreMembers(Method, Method, fcall);
      if (uhdm::AnyCollection *arguments = compileTfCallArguments(
              component, fC, List_of_arguments, compileDesign, reduce, fcall,
              instance, muteErrors)) {
        fcall->setArguments(arguments);
      }
      result = fcall;
    } else if (fC->Type(List_of_arguments) ==
                   VObjectType::paConstant_expression ||
               fC->Type(List_of_arguments) == VObjectType::paSelect ||
               fC->Type(List_of_arguments) == VObjectType::paConstant_select) {
      // TODO: prefix the var_select with "this" class var
      // (this.fields[idx-1].get...)
      if (fC->Type(List_of_arguments) == VObjectType::paSelect)
        List_of_arguments = fC->Child(List_of_arguments);
      result = compileSelectExpression(component, fC, Method, rootName,
                                       compileDesign, reduce, pexpr, instance,
                                       muteErrors);
      if (result == nullptr) {
        uhdm::HierPath *path = s.make<uhdm::HierPath>();
        uhdm::AnyCollection *elems = path->getPathElems(true);
        std::string fullName;
        uhdm::RefObj *r1 = s.make<uhdm::RefObj>();
        r1->setName(rootName);
        fullName = rootName;
        elems->emplace_back(r1);
        r1->setParent(path);
        fC->populateCoreMembers(Method, Method, r1);
        fC->populateCoreMembers(Handle, InvalidNodeId, path);
        while (Method) {
          uhdm::RefObj *r = s.make<uhdm::RefObj>();
          NodeId nameId = Method;
          if (fC->Type(nameId) ==
              VObjectType::paPs_or_hierarchical_identifier) {
            nameId = fC->Child(Method);
          }
          r->setName(fC->SymName(nameId));
          r->setParent(path);
          fullName.append(".").append(fC->SymName(nameId));
          elems->emplace_back(r);
          fC->populateCoreMembers(nameId, nameId, r);
          fC->populateCoreMembers(InvalidNodeId, Method, path);
          Method = fC->Sibling(Method);
          if (fC->Type(Method) != VObjectType::slStringConst) {
            break;
          }
        }
        path->setName(fullName);
        if (!elems->empty()) {
          path->setStartLine(elems->front()->getStartLine());
          path->setStartColumn(elems->front()->getStartColumn());
          path->setEndLine(elems->back()->getEndLine());
          path->setEndColumn(elems->back()->getEndColumn());
        }
        result = path;
      }
    } else if (fC->Type(List_of_arguments) ==
               VObjectType::paConstant_bit_select) {
      // TODO: Fill this
      uhdm::MethodFuncCall *fcall = s.make<uhdm::MethodFuncCall>();
      if (uhdm::Expr *object = (uhdm::Expr *)compileExpression(
              component, fC, Handle, compileDesign, reduce, fcall, instance,
              muteErrors)) {
        // TODO: make name part of the prefix, get vpiName from sibling
        fcall->setPrefix(object);
      }
      if (uhdm::AnyCollection *arguments = compileTfCallArguments(
              component, fC, fC->Sibling(fC->Sibling(List_of_arguments)),
              compileDesign, reduce, fcall, instance, muteErrors)) {
        fcall->setArguments(arguments);
      }
      fcall->setName(rootName);
      fC->populateCoreMembers(fC->Parent(Method), fC->Parent(Method), fcall);
      result = fcall;
    } else if (fC->Type(List_of_arguments) == VObjectType::slStringConst) {
      // TODO: this is a mockup
      uhdm::Constant *cvar = s.make<uhdm::Constant>();
      cvar->setDecompile("this");
      cvar->setParent(pexpr);
      result = cvar;
    }
  } else if (fC->Type(name) == VObjectType::paClass_scope) {
    NodeId Class_type = fC->Child(name);
    NodeId Class_type_name = fC->Child(Class_type);
    NodeId Class_scope_name = fC->Sibling(name);
    NodeId List_of_arguments = fC->Sibling(Class_scope_name);
    NodeId Bit_Select;
    if (List_of_arguments) {
      if (fC->Type(List_of_arguments) == VObjectType::paSelect) {
        Bit_Select = fC->Child(List_of_arguments);
        if (!fC->Child(Bit_Select)) {
          List_of_arguments = InvalidNodeId;
        }
      }
    }

    const std::string_view packagename = fC->SymName(Class_type_name);
    const std::string_view functionname = fC->SymName(Class_scope_name);
    std::string basename = StrCat(packagename, "::", functionname);
    uhdm::TFCall *call = nullptr;
    std::pair<uhdm::TaskFunc *, DesignComponent *> ret =
        getTaskFunc(basename, component, compileDesign, instance, pexpr);
    uhdm::TaskFunc *tf = ret.first;
    if (tf) {
      if (tf->getUhdmType() == uhdm::UhdmType::Function) {
        uhdm::FuncCall *fcall = s.make<uhdm::FuncCall>();
        fcall->setFunction(any_cast<uhdm::Function *>(tf));
        call = fcall;
      } else {
        uhdm::TaskCall *tcall = s.make<uhdm::TaskCall>();
        tcall->setTask(any_cast<uhdm::Task>(tf));
        call = tcall;
      }
      tf->setParent(call);
      call->setParent(pexpr);
      NodeId fid = id;
      if ((fC->Type(fid) == VObjectType::paClass_scope) ||
          (fC->Type(fid) == VObjectType::paPackage_scope))
        fid = fC->Parent(fid);
      fC->populateCoreMembers(fid, fid, call);
    }
    Package *pack = design->getPackage(packagename);
    if (call == nullptr) {
      if (pack && !List_of_arguments) {
        Value *val = pack->getValue(functionname);
        if (val && val->isValid()) {
          if (Bit_Select) {
            if (fC->Type(Bit_Select) == VObjectType::paConstant_select) {
              Bit_Select = fC->Child(Bit_Select);
            }
            if (uhdm::Any *tmpResult = compileSelectExpression(
                    component, fC, Bit_Select, basename, compileDesign, reduce,
                    pexpr, instance, muteErrors)) {
              return tmpResult;
            }
          }
          uhdm::Constant *c = s.make<uhdm::Constant>();
          c->setValue(val->uhdmValue());
          c->setDecompile(val->decompiledValue());
          c->setSize(val->getSize());
          c->setConstType(val->vpiValType());
          c->setParent(pexpr);
          fC->populateCoreMembers(Class_scope_name, Class_scope_name, c);
          result = c;
          return result;
        }
      }
    }
    if (call == nullptr) {
      if (pack && pack->getParameters()) {
        for (uhdm::Any *param : *pack->getParameters()) {
          if (param->getName() == functionname) {
            if ((fC->Type(List_of_arguments) == VObjectType::paSelect) &&
                (fC->Child(List_of_arguments))) {
              result = compileSelectExpression(
                  component, fC, fC->Child(List_of_arguments),
                  StrCat(packagename, "::", functionname), compileDesign,
                  reduce, pexpr, instance, muteErrors);
              if (result)
                result->setParent(param);
              else
                result = param;
            } else if ((fC->Type(List_of_arguments) ==
                        VObjectType::slStringConst)) {
              uhdm::HierPath *path = s.make<uhdm::HierPath>();
              uhdm::AnyCollection *elems = path->getPathElems(true);
              uhdm::RefObj *ref = s.make<uhdm::RefObj>();
              ref->setName(StrCat(packagename, "::", functionname));
              ref->setFullName(StrCat(packagename, "::", functionname));
              ref->setActual(param);
              ref->setParent(path);
              fC->populateCoreMembers(name, name, ref);
              elems->emplace_back(ref);
              while (List_of_arguments) {
                if ((fC->Type(List_of_arguments) ==
                     VObjectType::slStringConst)) {
                  uhdm::RefObj *ref = s.make<uhdm::RefObj>();
                  ref->setName(fC->SymName(List_of_arguments));
                  ref->setParent(path);
                  fC->populateCoreMembers(List_of_arguments, List_of_arguments,
                                          ref);
                  elems->emplace_back(ref);
                }
                List_of_arguments = fC->Sibling(List_of_arguments);
              }
              if (!elems->empty()) {
                path->setStartLine(elems->front()->getStartLine());
                path->setStartColumn(elems->front()->getStartColumn());
                path->setEndLine(elems->back()->getEndLine());
                path->setEndColumn(elems->back()->getEndColumn());
              }
              result = path;
            } else {
              uhdm::RefObj *ref = s.make<uhdm::RefObj>();
              ref->setName(StrCat(packagename, "::", functionname));
              ref->setFullName(StrCat(packagename, "::", functionname));
              ref->setActual(param);
              ref->setParent(pexpr);
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
      call->setName(basename);
      if (uhdm::AnyCollection *arguments = compileTfCallArguments(
              component, fC, List_of_arguments, compileDesign, reduce, call,
              instance, muteErrors)) {
        call->setArguments(arguments);
      }
      result = call;
    } else {
      result = compileExpression(component, fC, name, compileDesign, reduce,
                                 pexpr, instance, muteErrors);
    }
  } else if (fC->Type(dotedName) == VObjectType::paSelect ||
             fC->Type(dotedName) == VObjectType::paConstant_select ||
             fC->Type(dotedName) == VObjectType::paConstant_expression ||
             fC->Type(dotedName) == VObjectType::slStringConst ||
             fC->Type(dotedName) == VObjectType::paConstant_bit_select ||
             fC->Type(dotedName) == VObjectType::paBit_select) {
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
        VObjectType selectType = fC->Type(selectName);
        if (selectName &&
            (selectType == VObjectType::paConstant_part_select_range)) {
          result = compileSelectExpression(component, fC, dotedName, "",
                                           compileDesign, reduce, pexpr,
                                           instance, muteErrors);
          if (result && (result->getUhdmType() == uhdm::UhdmType::VarSelect)) {
            fC->populateCoreMembers(name, dotedName, result);
            ((uhdm::VarSelect *)result)->setName(sval);
          }
          return result;
        } else if (Bit_select &&
                   (fC->Child(Bit_select) || fC->Sibling(Bit_select))) {
          result = compileSelectExpression(component, fC, Bit_select, sval,
                                           compileDesign, reduce, pexpr,
                                           instance, muteErrors);
          if (result && (result->getUhdmType() == uhdm::UhdmType::PartSelect)) {
            fC->populateCoreMembers(name, dotedName, result, true);
          }
          return result;
        } else if ((!selectName) &&
                   (dtype == VObjectType::paSelect ||
                    dtype == VObjectType::paConstant_bit_select ||
                    dtype == VObjectType::paBit_select ||
                    dtype == VObjectType::paConstant_select)) {
          std::string ind;
          uhdm::Expr *index = nullptr;
          if (NodeId Expression = fC->Child(Bit_select)) {
            index = (uhdm::Expr *)compileExpression(component, fC, Expression,
                                                    compileDesign, Reduce::No,
                                                    pexpr, instance);
          }
          if (index) {
            uhdm::BitSelect *select = s.make<uhdm::BitSelect>();
            index->setParent(select);
            select->setIndex(index);
            the_name += "[" + decompileHelper(index) + "]";
            select->setFullName(the_name);
            select->setName(fC->SymName(name));
            result = select;
          } else {
            uhdm::RefObj *ref = s.make<uhdm::RefObj>();
            ref->setName(the_name);
            ref->setFullName(the_name);
            result = ref;
            fC->populateCoreMembers(name, name, ref);
          }
          result->setParent(pexpr);
          fC->populateCoreMembers(name, name, result);
          return result;
        }
      }

      uhdm::HierPath *path = s.make<uhdm::HierPath>();
      uhdm::AnyCollection *elems = path->getPathElems(true);
      if ((m_reduce == Reduce::Yes) && (reduce == Reduce::Yes) && instance) {
        uhdm::Any *rootValue =
            getObject(the_name, component, compileDesign, instance, pexpr);
        if (rootValue) {
          if (uhdm::Expr *expval = any_cast<uhdm::Expr *>(rootValue)) {
            path->setExpr(rootValue);
            if (uhdm::RefTypespec *expval_rt = expval->getTypespec()) {
              if (path->getTypespec() == nullptr) {
                uhdm::RefTypespec *path_rt = s.make<uhdm::RefTypespec>();
                path_rt->setParent(path);
                path->setTypespec(path_rt);
              }
              path->getTypespec()->setActual(expval_rt->getActual());
            }
          } else if (uhdm::Port *expval = any_cast<uhdm::Port>(rootValue)) {
            path->setExpr(expval->getLowConn());
          } else if (uhdm::ParamAssign *passign =
                         any_cast<uhdm::ParamAssign>(rootValue)) {
            path->setExpr((uhdm::Any *)passign->getRhs());
            const uhdm::Any *param = passign->getLhs();
            uhdm::Typespec *tps = nullptr;
            if (param->getUhdmType() == uhdm::UhdmType::Parameter) {
              uhdm::Parameter *p = (uhdm::Parameter *)param;
              if (uhdm::RefTypespec *rt = p->getTypespec()) {
                tps = rt->getActual();
              }
            } else {
              uhdm::TypeParameter *p = (uhdm::TypeParameter *)param;
              if (uhdm::RefTypespec *rt = p->getTypespec()) {
                tps = rt->getActual();
              }
            }
            if (path->getTypespec() == nullptr) {
              uhdm::RefTypespec *rt = s.make<uhdm::RefTypespec>();
              rt->setParent(path);
              path->setTypespec(rt);
            }
            path->getTypespec()->setActual(tps);
          }
        }
      }
      std::string tmpName = the_name;
      bool is_hierarchical = false;
      while (dotedName) {
        VObjectType dtype = fC->Type(dotedName);
        NodeId BitSelect = fC->Child(dotedName);
        if (dtype == VObjectType::slStringConst) {
          the_name.append(".").append(fC->SymName(dotedName));
          if (!tmpName.empty()) {
            uhdm::RefObj *ref = s.make<uhdm::RefObj>();
            elems->emplace_back(ref);
            ref->setName(tmpName);
            ref->setFullName(tmpName);
            ref->setParent(path);
            fC->populateCoreMembers(name, name, ref);
            tmpName.clear();
            is_hierarchical = true;
          }
          tmpName = fC->SymName(dotedName);
        } else if (dtype == VObjectType::paSelect ||
                   dtype == VObjectType::paBit_select ||
                   dtype == VObjectType::paConstant_bit_select ||
                   dtype == VObjectType::paConstant_expression) {
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
            if (dtype == VObjectType::paConstant_expression) {
              Expression = dotedName;
            }
            if ((fC->Type(BitSelect) == VObjectType::paBit_select) &&
                fC->Child(BitSelect)) {
              if (uhdm::Expr *select = (uhdm::Expr *)compileSelectExpression(
                      component, fC, BitSelect, tmpName, compileDesign, reduce,
                      path, instance, muteErrors)) {
                if ((select->getUhdmType() == uhdm::UhdmType::PartSelect) ||
                    (select->getUhdmType() == uhdm::UhdmType::VarSelect)) {
                  fC->populateCoreMembers(name, dotedName, select);
                }
                elems->emplace_back(select);
                the_name += decompileHelper(select);
                tmpName.clear();
              }
              break;
            } else if (fC->Type(BitSelect) ==
                       VObjectType::paPart_select_range) {
              if (uhdm::Expr *select = (uhdm::Expr *)compilePartSelectRange(
                      component, fC, Expression, "CREATE_UNNAMED_PARENT",
                      compileDesign, reduce, path, instance, muteErrors)) {
                the_name += decompileHelper(select);
                // Fix start/end to include the name
                select->setStartColumn(fC->Column(name));
                if (uhdm::RefObj *ro = any_cast<uhdm::RefObj *>(select)) {
                  ro->setName(tmpName);
                  ro->setFullName(the_name);
                }
                elems->emplace_back(select);
              }
            } else if (Expression &&
                       (fC->Type(Expression) ==
                        VObjectType::paPart_select_range) &&
                       fC->Child(Expression)) {
              if (uhdm::Expr *select = (uhdm::Expr *)compilePartSelectRange(
                      component, fC, fC->Child(Expression),
                      "CREATE_UNNAMED_PARENT", compileDesign, reduce, path,
                      instance, muteErrors)) {
                the_name += decompileHelper(select);
                // Fix start/end to include the name
                select->setStartColumn(fC->Column(name));
                if (uhdm::RefObj *ro = any_cast<uhdm::RefObj *>(select)) {
                  ro->setName(tmpName);
                  ro->setFullName(the_name);
                }
                elems->emplace_back(select);
              }
            } else if (Expression) {
              uhdm::BitSelect *select = s.make<uhdm::BitSelect>();
              select->setParent(path);
              fC->populateCoreMembers(name, name, select);
              if (uhdm::Expr *index = (uhdm::Expr *)compileExpression(
                      component, fC, Expression, compileDesign, reduce, select,
                      instance, muteErrors)) {
                tmpName = the_name;
                the_name += "[" + decompileHelper(index) + "]";
                select->setName(tmpName);
                select->setFullName(the_name);
                select->setIndex(index);
              }
              elems->emplace_back(select);
            } else {
              uhdm::RefObj *ref = s.make<uhdm::RefObj>();
              ref->setName(tmpName);
              ref->setParent(path);
              fC->populateCoreMembers(name, name, ref);
              elems->emplace_back(ref);
            }
            tmpName.clear();
            if (dtype == VObjectType::paSelect)
              BitSelect = fC->Sibling(BitSelect);
            else
              break;
          }
        }

        NodeId lookAhead = fC->Sibling(dotedName);

        if ((fC->Type(dotedName) == VObjectType::paMethod_call_body) ||
            (fC->Type(lookAhead) == VObjectType::paList_of_arguments)) {
          NodeId method_child = fC->Child(dotedName);
          uhdm::MethodFuncCall *fcall = nullptr;
          if (fC->Type(method_child) == VObjectType::paBuilt_in_method_call) {
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
              if (calltype == VObjectType::paAnd_call) {
                method_name = "and";
              } else if (calltype == VObjectType::paOr_call) {
                method_name = "or";
              } else if (calltype == VObjectType::paXor_call) {
                method_name = "xor";
              } else if (calltype == VObjectType::paUnique_call) {
                method_name = "unique";
              }
            }

            NodeId randomize_call = fC->Child(method_child);

            if (fC->Type(randomize_call) == VObjectType::paRandomize_call) {
              fcall = compileRandomizeCall(component, fC, randomize_call,
                                           compileDesign, pexpr);
            } else {
              fcall = s.make<uhdm::MethodFuncCall>();
              fcall->setName(method_name);
              fC->populateCoreMembers(method_name_node, id, fcall);
              NodeId list_of_arguments =
                  fC->Sibling(fC->Child(fC->Child(method_child)));
              NodeId with_conditions_node;
              if (fC->Type(list_of_arguments) ==
                  VObjectType::paList_of_arguments) {
                if (uhdm::AnyCollection *arguments = compileTfCallArguments(
                        component, fC, list_of_arguments, compileDesign, reduce,
                        fcall, instance, muteErrors)) {
                  fcall->setArguments(arguments);
                }
                with_conditions_node = fC->Sibling(list_of_arguments);
              } else {
                with_conditions_node = list_of_arguments;
              }
              // vpiWith: with conditions (expression in node u<62> above)
              // (not in every method, node id is 0 if missing)
              if (with_conditions_node) {
                if (uhdm::Expr *with_conditions =
                        (uhdm::Expr *)compileExpression(
                            component, fC, with_conditions_node, compileDesign,
                            reduce, fcall, instance, muteErrors)) {
                  fcall->setWith(with_conditions);
                }
              }
            }
            elems->emplace_back(fcall);
            tmpName.clear();
            dotedName = fC->Sibling(dotedName);
          } else {
            fcall = s.make<uhdm::MethodFuncCall>();
            const std::string_view methodName = fC->SymName(dotedName);
            fcall->setName(methodName);
            fC->populateCoreMembers(dotedName, id, fcall);
            if (uhdm::AnyCollection *arguments = compileTfCallArguments(
                    component, fC, List_of_arguments, compileDesign, reduce,
                    fcall, instance, muteErrors)) {
              fcall->setArguments(arguments);
            }
            elems->emplace_back(fcall);
            tmpName.clear();
            dotedName = fC->Sibling(dotedName);
          }
          if (fcall != nullptr) fcall->setParent(path);
        }
        name = dotedName;
        if (dotedName) dotedName = fC->Sibling(dotedName);
      }
      if (is_hierarchical) {
        if (!tmpName.empty()) {
          uhdm::RefObj *ref = s.make<uhdm::RefObj>();
          elems->emplace_back(ref);
          ref->setName(tmpName);
          ref->setFullName(the_name);
          ref->setParent(path);
          fC->populateCoreMembers(name, name, ref);
          tmpName.clear();
        }

        if (elems->size() == 1) {
          result = elems->at(0);
          result->setParent(pexpr, true);
        } else {
          if (elems->empty()) {
            fC->populateCoreMembers(id, id, path);
          } else {
            path->setStartLine(elems->front()->getStartLine());
            path->setStartColumn(elems->front()->getStartColumn());
            path->setEndLine(elems->back()->getEndLine());
            path->setEndColumn(elems->back()->getEndColumn());
          }
          path->setName(the_name);
          path->setFullName(the_name);
          path->setParent(pexpr);
          result = path;
        }
      } else {
        uhdm::RefObj *ref = s.make<uhdm::RefObj>();
        ref->setName(tmpName);
        ref->setParent(pexpr);
        fC->populateCoreMembers(name, name, ref);
        tmpName.clear();
        result = ref;
      }
    } else if (uhdm::Any *st = getValue(
                   sval, component, compileDesign, reduce, instance,
                   fC->getFileId(), fC->Line(Bit_select), pexpr, muteErrors)) {
      uhdm::UhdmType type = st->getUhdmType();
      NodeId Select = dotedName;
      if (NodeId BitSelect = fC->Child(Select)) {
        NodeId Expression = fC->Child(BitSelect);
        while (Expression) {
          uhdm::Expr *index = (uhdm::Expr *)compileExpression(
              component, fC, Expression, compileDesign, reduce, pexpr, instance,
              muteErrors);
          if (index && index->getUhdmType() == uhdm::UhdmType::Constant) {
            bool invalidValue = false;
            uhdm::ExprEval eval;
            uint64_t ind = (uint64_t)eval.get_value(invalidValue, index);
            if (invalidValue == false && type == uhdm::UhdmType::Operation) {
              uhdm::Operation *op = (uhdm::Operation *)st;
              int32_t opType = op->getOpType();
              if (opType == vpiAssignmentPatternOp) {
                uhdm::AnyCollection *operands = op->getOperands();
                if (ind < operands->size()) {
                  result = operands->at(ind);
                  st = result;
                }
              } else if (opType == vpiConcatOp) {
                uhdm::AnyCollection *operands = op->getOperands();
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
      uhdm::RefObj *ref = s.make<uhdm::RefObj>();
      ref->setName(n);
      ref->setParent(pexpr);
      if (pexpr) {
        if (uhdm::Any *var = bindVariable(component, pexpr, n, compileDesign))
          ref->setActual(var);
      } else if (instance) {
        if (uhdm::Any *var =
                bindVariable(component, instance, n, compileDesign))
          ref->setActual(var);
      }
      result = ref;
    }
  } else if (fC->Type(dotedName) == VObjectType::paList_of_arguments) {
    result =
        compileTfCall(component, fC, fC->Parent(name), compileDesign, pexpr);
  } else if (fC->Type(name) == VObjectType::slStringConst) {
    const std::string_view n = fC->SymName(name);
    uhdm::RefObj *ref = s.make<uhdm::RefObj>();
    ref->setName(n);
    ref->setParent(pexpr);
    if (pexpr) {
      if (uhdm::Any *var = bindVariable(component, pexpr, n, compileDesign))
        ref->setActual(var);
    } else if (instance) {
      if (uhdm::Any *var = bindVariable(component, instance, n, compileDesign))
        ref->setActual(var);
    }
    result = ref;
  } else if (fC->Type(name) == VObjectType::paSubroutine_call) {
    result = compileExpression(component, fC, fC->Parent(name), compileDesign,
                               reduce, pexpr, instance, muteErrors);
  } else if (!dotedName) {
    const std::string_view the_name = fC->SymName(name);
    uhdm::RefObj *ref = s.make<uhdm::RefObj>();
    ref->setName(the_name);
    ref->setFullName(the_name);
    ref->setParent(pexpr);
    fC->populateCoreMembers(name, name, ref);
    result = ref;
  }
  return result;
}

bool CompileHelper::parseConstant(const uhdm::Constant &constant,
                                  int64_t *value) {
  std::string_view v = constant.getValue();
  if (v.length() <= 4) return false;  // All prefices are at least this long.

  switch (constant.getConstType()) {
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
                                uhdm::Any *pexpr, ValuedComponentI *instance,
                                bool muteErrors) {
  int64_t result = 0;
  validValue = true;
  uhdm::Any *expr = compileExpression(component, fC, nodeId, compileDesign,
                                      reduce, pexpr, instance, muteErrors);
  if (expr && expr->getUhdmType() == uhdm::UhdmType::Constant) {
    validValue = parseConstant(*(const uhdm::Constant *)expr, &result);
  } else {
    validValue = false;
  }
  return result;
}

void CompileHelper::reorderAssignmentPattern(
    DesignComponent *mod, const uhdm::Any *lhs, uhdm::Any *rhs,
    CompileDesign *compileDesign, ValuedComponentI *instance, uint32_t level) {
  if (rhs->getUhdmType() != uhdm::UhdmType::Operation) return;
  uhdm::Operation *op = (uhdm::Operation *)rhs;
  int32_t optype = op->getOpType();
  if ((m_reduce == Reduce::Yes) && (optype == vpiConditionOp)) {
    bool invalidValue = false;
    uhdm::Expr *tmp = reduceExpr(op, invalidValue, mod, compileDesign, instance,
                                 BadPathId, 0, nullptr, true);
    if (tmp && (tmp->getUhdmType() == uhdm::UhdmType::Operation) &&
        (invalidValue == false)) {
      op = (uhdm::Operation *)tmp;
      optype = op->getOpType();
    }
  }
  if (op->getReordered()) return;
  if ((optype != vpiAssignmentPatternOp) && (optype != vpiConcatOp)) return;
  uhdm::AnyCollection *operands = op->getOperands();
  bool ordered = true;
  for (uhdm::Any *operand : *operands) {
    if (operand->getUhdmType() == uhdm::UhdmType::TaggedPattern) {
      ordered = false;
      break;
    }
  }
  if (ordered) {
    if (lhs->getUhdmType() == uhdm::UhdmType::Parameter) {
      uhdm::Parameter *p = (uhdm::Parameter *)lhs;
      uhdm::RangeCollection *ranges = nullptr;
      if (p->getRanges()) {
        ranges = p->getRanges();
      } else if (const uhdm::RefTypespec *rt = p->getTypespec()) {
        if (const uhdm::Typespec *tps = rt->getActual()) {
          uhdm::UhdmType ttype = tps->getUhdmType();
          if (ttype == uhdm::UhdmType::BitTypespec) {
            ranges = ((uhdm::BitTypespec *)tps)->getRanges();
          } else if (ttype == uhdm::UhdmType::LogicTypespec) {
            ranges = ((uhdm::LogicTypespec *)tps)->getRanges();
          } else if (ttype == uhdm::UhdmType::ArrayTypespec) {
            ranges = ((uhdm::ArrayTypespec *)tps)->getRanges();
          } else if (ttype == uhdm::UhdmType::PackedArrayTypespec) {
            ranges = ((uhdm::PackedArrayTypespec *)tps)->getRanges();
          }
        }
      }
      if (ranges) {
        if (level < ranges->size()) {
          uhdm::Range *r = ranges->at(level);
          uhdm::Expr *lr = (uhdm::Expr *)r->getLeftExpr();
          uhdm::Expr *rr = (uhdm::Expr *)r->getRightExpr();
          bool invalidValue = false;
          uhdm::ExprEval eval;
          lr = reduceExpr(lr, invalidValue, mod, compileDesign, instance,
                          BadPathId, 0, nullptr, true);
          int64_t lrv = eval.get_value(invalidValue, lr);
          rr = reduceExpr(rr, invalidValue, mod, compileDesign, instance,
                          BadPathId, 0, nullptr, true);
          int64_t rrv = eval.get_value(invalidValue, rr);
          if (lrv > rrv) {
            op->setReordered(true);
            std::reverse(operands->begin(), operands->end());
            if (level == 0) {
              if (instance) {
                instance->setComplexValue(p->getName(), op);
              } else {
                mod->setComplexValue(p->getName(), op);
              }
            }
          }
        }
      }
    }
  }
  for (uhdm::Any *operand : *operands) {
    if (operand->getUhdmType() == uhdm::UhdmType::Operation) {
      reorderAssignmentPattern(mod, lhs, operand, compileDesign, instance,
                               level + 1);
    }
  }
}
}  // namespace SURELOG
