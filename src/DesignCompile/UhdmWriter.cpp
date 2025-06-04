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
 * File:   UhdmWriter.cpp
 * Author: alain
 *
 * Created on January 17, 2020, 9:13 PM
 */

#include "Surelog/DesignCompile/UhdmWriter.h"

#include <uhdm/BaseClass.h>
#include <uhdm/expr.h>
#include <uhdm/import_typespec.h>
#include <uhdm/uhdm_types.h>

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <iostream>
#include <iterator>
#include <map>
#include <queue>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/Containers.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Common/SymbolId.h"
#include "Surelog/Design/ClockingBlock.h"
#include "Surelog/Design/DataType.h"
#include "Surelog/Design/DesignElement.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/Modport.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Netlist.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/Design/Signal.h"
#include "Surelog/Design/ValuedComponentI.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/DesignCompile/IntegrityChecker.h"
#include "Surelog/DesignCompile/ObjectBinder.h"
#include "Surelog/DesignCompile/UhdmChecker.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Expression/Value.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Testbench/Program.h"
#include "Surelog/Testbench/TypeDef.h"
#include "Surelog/Testbench/Variable.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/Serializer.h>
#include <uhdm/SynthSubset.h>
#include <uhdm/UhdmAdjuster.h>
#include <uhdm/UhdmLint.h>
#include <uhdm/UhdmListener.h>
#include <uhdm/VpiListener.h>
#include <uhdm/clone_tree.h>
#include <uhdm/sv_vpi_user.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_uhdm.h>
#include <uhdm/vpi_user.h>
#include <uhdm/vpi_visitor.h>

#include <algorithm>
#include <cstring>
#include <queue>
#include <set>

namespace SURELOG {
namespace fs = std::filesystem;
using namespace uhdm;  // NOLINT (we're using a whole bunch of these)

static uhdm::Typespec* replace(
    const uhdm::Typespec* orig,
    std::map<const uhdm::Typespec*, const uhdm::Typespec*>& typespecSwapMap) {
  if (orig && (orig->getUhdmType() == uhdm::UhdmType::UnsupportedTypespec)) {
    std::map<const uhdm::Typespec*, const uhdm::Typespec*>::const_iterator itr =
        typespecSwapMap.find(orig);
    if (itr != typespecSwapMap.end()) {
      const uhdm::Typespec* tps = (*itr).second;
      return (uhdm::Typespec*)tps;
    }
  }
  return (uhdm::Typespec*)orig;
}

std::string UhdmWriter::builtinGateName(VObjectType type) {
  std::string modName;
  switch (type) {
    case VObjectType::paNInpGate_And:
      modName = "work@and";
      break;
    case VObjectType::paNInpGate_Or:
      modName = "work@or";
      break;
    case VObjectType::paNInpGate_Nand:
      modName = "work@nand";
      break;
    case VObjectType::paNInpGate_Nor:
      modName = "work@nor";
      break;
    case VObjectType::paNInpGate_Xor:
      modName = "work@xor";
      break;
    case VObjectType::paNInpGate_Xnor:
      modName = "work@xnor";
      break;
    case VObjectType::paNOutGate_Buf:
      modName = "work@buf";
      break;
    case VObjectType::paNOutGate_Not:
      modName = "work@not";
      break;
    case VObjectType::paPassEnSwitch_Tranif0:
      modName = "work@tranif0";
      break;
    case VObjectType::paPassEnSwitch_Tranif1:
      modName = "work@tranif1";
      break;
    case VObjectType::paPassEnSwitch_RTranif1:
      modName = "work@rtranif1";
      break;
    case VObjectType::paPassEnSwitch_RTranif0:
      modName = "work@rtranif0";
      break;
    case VObjectType::paPassSwitch_Tran:
      modName = "work@tran";
      break;
    case VObjectType::paPassSwitch_RTran:
      modName = "work@rtran";
      break;
    case VObjectType::paCmosSwitchType_Cmos:
      modName = "work@cmos";
      break;
    case VObjectType::paCmosSwitchType_RCmos:
      modName = "work@rcmos";
      break;
    case VObjectType::paEnableGateType_Bufif0:
      modName = "work@bufif0";
      break;
    case VObjectType::paEnableGateType_Bufif1:
      modName = "work@bufif1";
      break;
    case VObjectType::paEnableGateType_Notif0:
      modName = "work@notif0";
      break;
    case VObjectType::paEnableGateType_Notif1:
      modName = "work@notif1";
      break;
    case VObjectType::paMosSwitchType_NMos:
      modName = "work@nmos";
      break;
    case VObjectType::paMosSwitchType_PMos:
      modName = "work@pmos";
      break;
    case VObjectType::paMosSwitchType_RNMos:
      modName = "work@rnmos";
      break;
    case VObjectType::paMosSwitchType_RPMos:
      modName = "work@rpmos";
      break;
    case VObjectType::paPULLUP:
      modName = "work@pullup";
      break;
    case VObjectType::paPULLDOWN:
      modName = "work@pulldown";
      break;
    default:
      modName = "work@UnsupportedPrimitive";
      break;
  }
  return modName;
}

UhdmWriter::UhdmWriter(Session* session, CompileDesign* compiler,
                       Design* design)
    : m_session(session),
      m_compileDesign(compiler),
      m_design(design),
      m_helper(session) {}

uint32_t UhdmWriter::getStrengthType(VObjectType type) {
  switch (type) {
    case VObjectType::paSUPPLY0:
      return vpiSupply0;
    case VObjectType::paSUPPLY1:
      return vpiSupply1;
    case VObjectType::paSTRONG0:
      return vpiStrongDrive;
    case VObjectType::paSTRONG1:
      return vpiStrongDrive;
    case VObjectType::paPULL0:
      return vpiPullDrive;
    case VObjectType::paPULL1:
      return vpiPullDrive;
    case VObjectType::paWEAK0:
      return vpiWeakDrive;
    case VObjectType::paWEAK1:
      return vpiWeakDrive;
    case VObjectType::paHIGHZ0:
      return vpiHighZ;
    case VObjectType::paHIGHZ1:
      return vpiHighZ;
    default:
      return 0;
  }
}

uint32_t UhdmWriter::getVpiOpType(VObjectType type) {
  switch (type) {
    case VObjectType::paBinOp_Plus:
      return vpiAddOp;
    case VObjectType::paBinOp_Minus:
      return vpiSubOp;
    case VObjectType::paBinOp_Mult:
      return vpiMultOp;
    case VObjectType::paBinOp_MultMult:
      return vpiPowerOp;
    case VObjectType::paBinOp_Div:
      return vpiDivOp;
    case VObjectType::paBinOp_Great:
      return vpiGtOp;
    case VObjectType::paBinOp_GreatEqual:
      return vpiGeOp;
    case VObjectType::paBinOp_Less:
      return vpiLtOp;
    case VObjectType::paBinOp_Imply:
      return vpiImplyOp;
    case VObjectType::paBinOp_Equivalence:
      return vpiEqOp;
    case VObjectType::paBinOp_LessEqual:
      return vpiLeOp;
    case VObjectType::paBinOp_Equiv:
      return vpiEqOp;
    case VObjectType::paBinOp_Not:
    case VObjectType::paNOT:
      return vpiNeqOp;
    case VObjectType::paBinOp_Percent:
      return vpiModOp;
    case VObjectType::paBinOp_LogicAnd:
      return vpiLogAndOp;
    case VObjectType::paBinOp_LogicOr:
      return vpiLogOrOp;
    case VObjectType::paBinOp_BitwAnd:
      return vpiBitAndOp;
    case VObjectType::paBinOp_BitwOr:
      return vpiBitOrOp;
    case VObjectType::paBinOp_BitwXor:
      return vpiBitXorOp;
    case VObjectType::paBinOp_ReductXnor1:
    case VObjectType::paBinOp_ReductXnor2:
    case VObjectType::paBinModOp_ReductXnor1:
    case VObjectType::paBinModOp_ReductXnor2:
      return vpiBitXNorOp;
    case VObjectType::paBinOp_ReductNand:
      return vpiUnaryNandOp;
    case VObjectType::paBinOp_ReductNor:
      return vpiUnaryNorOp;
    case VObjectType::paUnary_Plus:
      return vpiPlusOp;
    case VObjectType::paUnary_Minus:
      return vpiMinusOp;
    case VObjectType::paUnary_Not:
      return vpiNotOp;
    case VObjectType::paUnary_Tilda:
      return vpiBitNegOp;
    case VObjectType::paUnary_BitwAnd:
      return vpiUnaryAndOp;
    case VObjectType::paUnary_BitwOr:
      return vpiUnaryOrOp;
    case VObjectType::paUnary_BitwXor:
      return vpiUnaryXorOp;
    case VObjectType::paUnary_ReductNand:
      return vpiUnaryNandOp;
    case VObjectType::paUnary_ReductNor:
      return vpiUnaryNorOp;
    case VObjectType::paUnary_ReductXnor1:
    case VObjectType::paUnary_ReductXnor2:
      return vpiUnaryXNorOp;
    case VObjectType::paBinOp_ShiftLeft:
      return vpiLShiftOp;
    case VObjectType::paBinOp_ShiftRight:
      return vpiRShiftOp;
    case VObjectType::paBinOp_ArithShiftLeft:
      return vpiArithLShiftOp;
    case VObjectType::paBinOp_ArithShiftRight:
      return vpiArithRShiftOp;
    case VObjectType::paIncDec_PlusPlus:
      return vpiPostIncOp;
    case VObjectType::paIncDec_MinusMinus:
      return vpiPostDecOp;
    case VObjectType::paConditional_operator:
    case VObjectType::paQMARK:
      return vpiConditionOp;
    case VObjectType::paINSIDE:
    case VObjectType::paOpen_range_list:
      return vpiInsideOp;
    case VObjectType::paBinOp_FourStateLogicEqual:
      return vpiCaseEqOp;
    case VObjectType::paBinOp_FourStateLogicNotEqual:
      return vpiCaseNeqOp;
    case VObjectType::paAssignOp_Assign:
      return vpiAssignmentOp;
    case VObjectType::paAssignOp_Add:
      return vpiAddOp;
    case VObjectType::paAssignOp_Sub:
      return vpiSubOp;
    case VObjectType::paAssignOp_Mult:
      return vpiMultOp;
    case VObjectType::paAssignOp_Div:
      return vpiDivOp;
    case VObjectType::paAssignOp_Modulo:
      return vpiModOp;
    case VObjectType::paAssignOp_BitwAnd:
      return vpiBitAndOp;
    case VObjectType::paAssignOp_BitwOr:
      return vpiBitOrOp;
    case VObjectType::paAssignOp_BitwXor:
      return vpiBitXorOp;
    case VObjectType::paAssignOp_BitwLeftShift:
      return vpiLShiftOp;
    case VObjectType::paAssignOp_BitwRightShift:
      return vpiRShiftOp;
    case VObjectType::paAssignOp_ArithShiftLeft:
      return vpiArithLShiftOp;
    case VObjectType::paAssignOp_ArithShiftRight:
      return vpiArithRShiftOp;
    case VObjectType::paMatches:
      return vpiMatchOp;
    case VObjectType::paBinOp_WildcardEqual:
    case VObjectType::paBinOp_WildEqual:
      return vpiWildEqOp;
    case VObjectType::paBinOp_WildcardNotEqual:
    case VObjectType::paBinOp_WildNotEqual:
      return vpiWildNeqOp;
    case VObjectType::paIFF:
      return vpiIffOp;
    case VObjectType::paOR:
      return vpiLogOrOp;
    case VObjectType::paAND:
      return vpiLogAndOp;
    case VObjectType::paNON_OVERLAP_IMPLY:
      return vpiNonOverlapImplyOp;
    case VObjectType::paOVERLAP_IMPLY:
      return vpiOverlapImplyOp;
    case VObjectType::paOVERLAPPED:
      return vpiOverlapFollowedByOp;
    case VObjectType::paNONOVERLAPPED:
      return vpiNonOverlapFollowedByOp;
    case VObjectType::paUNTIL:
      return vpiUntilOp;
    case VObjectType::paS_UNTIL:
      return vpiUntilOp;
    case VObjectType::paUNTIL_WITH:
      return vpiUntilWithOp;
    case VObjectType::paS_UNTIL_WITH:
      return vpiUntilWithOp;
    case VObjectType::paIMPLIES:
      return vpiImpliesOp;
    case VObjectType::paCycle_delay_range:
      return vpiCycleDelayOp;
    case VObjectType::paConsecutive_repetition:
      return vpiConsecutiveRepeatOp;
    case VObjectType::paNon_consecutive_repetition:
      return vpiRepeatOp;
    case VObjectType::paGoto_repetition:
      return vpiGotoRepeatOp;
    case VObjectType::paTHROUGHOUT:
      return vpiThroughoutOp;
    case VObjectType::paWITHIN:
      return vpiWithinOp;
    case VObjectType::paINTERSECT:
      return vpiIntersectOp;
    case VObjectType::paFIRST_MATCH:
      return vpiFirstMatchOp;
    case VObjectType::paSTRONG:
      return vpiOpStrong;
    case VObjectType::paACCEPT_ON:
      return vpiAcceptOnOp;
    case VObjectType::paSYNC_ACCEPT_ON:
      return vpiSyncAcceptOnOp;
    case VObjectType::paREJECT_ON:
      return vpiRejectOnOp;
    case VObjectType::paSYNC_REJECT_ON:
      return vpiSyncRejectOnOp;
    case VObjectType::paNEXTTIME:
      return vpiNexttimeOp;
    case VObjectType::paS_NEXTTIME:
      return vpiNexttimeOp;
    case VObjectType::paALWAYS:
      return vpiAlwaysOp;
    case VObjectType::paEVENTUALLY:
      return vpiEventuallyOp;
    default:
      return 0;
  }
}

bool isMultidimensional(const uhdm::Typespec* ts) {
  bool isMultiDimension = false;
  if (ts) {
    if (ts->getUhdmType() == uhdm::UhdmType::LogicTypespec) {
      uhdm::LogicTypespec* lts = (uhdm::LogicTypespec*)ts;
      if (lts->getRanges() && lts->getRanges()->size() > 1)
        isMultiDimension = true;
    } else if (ts->getUhdmType() == uhdm::UhdmType::ArrayTypespec) {
      uhdm::ArrayTypespec* lts = (uhdm::ArrayTypespec*)ts;
      if (lts->getRanges() && lts->getRanges()->size() > 1)
        isMultiDimension = true;
    } else if (ts->getUhdmType() == uhdm::UhdmType::PackedArrayTypespec) {
      uhdm::PackedArrayTypespec* lts = (uhdm::PackedArrayTypespec*)ts;
      if (lts->getRanges() && lts->getRanges()->size() > 1)
        isMultiDimension = true;
    } else if (ts->getUhdmType() == uhdm::UhdmType::BitTypespec) {
      uhdm::BitTypespec* lts = (uhdm::BitTypespec*)ts;
      if (lts->getRanges() && lts->getRanges()->size() > 1)
        isMultiDimension = true;
    }
  }
  return isMultiDimension;
}

bool writeElabParameters(Serializer& s, ModuleInstance* instance,
                         uhdm::Scope* m, ExprBuilder& exprBuilder) {
  Netlist* netlist = instance->getNetlist();
  DesignComponent* mod = instance->getDefinition();

  std::map<std::string_view, uhdm::Any*> paramSet;
  if (netlist->param_assigns()) {
    m->setParamAssigns(netlist->param_assigns());
  }

  if (mod) {
    if (uhdm::AnyCollection* orig_params = mod->getParameters()) {
      uhdm::AnyCollection* params = m->getParameters(true);
      for (auto orig : *orig_params) {
        const std::string_view name = orig->getName();
        bool pushed = false;
        // Specifc handling of type parameters
        if (orig->getUhdmType() == uhdm::UhdmType::TypeParameter) {
          for (auto p : instance->getTypeParams()) {
            if (p->getName() == orig->getName()) {
              uhdm::Any* uparam = p->getUhdmParam();
              if (uparam) {
                uparam->setParent(m);
                for (AnyCollection::iterator itr = params->begin();
                     itr != params->end(); itr++) {
                  if ((*itr)->getName() == p->getName()) {
                    params->erase(itr);
                    break;
                  }
                }
                params->emplace_back(uparam);
                pushed = true;
              }
              break;
            }
          }
          if (!pushed) {
            // These point to the sole copy (unelaborated)
            for (AnyCollection::iterator itr = params->begin();
                 itr != params->end(); itr++) {
              if ((*itr)->getName() == orig->getName()) {
                params->erase(itr);
                break;
              }
            }
            params->emplace_back(orig);
          }
        } else {
          // Regular param
          uhdm::ElaboratorContext elaboratorContext(&s, false, true);
          uhdm::Any* pclone = uhdm::clone_tree(orig, &elaboratorContext);
          pclone->setParent(m);
          paramSet.emplace(name, pclone);

          /*

            Keep the value of the parameter used during definition. The
          param_assign contains the actual value useful for elaboration

          const uhdm::Typespec* ts = ((uhdm::Parameter*)pclone)->getTypespec();
          bool multi = isMultidimensional(ts);
          if (((uhdm::Parameter*)pclone)->getRanges() &&
          ((uhdm::Parameter*)pclone)->getRanges()->size() > 1) multi = true;

          if (instance->getComplexValue(name)) {
          } else {
            Value* val = instance->getValue(name, exprBuilder);
            if (val && val->isValid() && (!multi)) {
              ((uhdm::Parameter*)pclone)->setValue(val->uhdmValue());
            }
          }
          */
          params->emplace_back(pclone);
        }
      }
    }
  }

  if (netlist->param_assigns()) {
    uhdm::AnyCollection* params = m->getParameters(true);
    for (auto p : *netlist->param_assigns()) {
      bool found = false;
      for (auto pt : *params) {
        if (pt->getName() == p->getLhs()->getName()) {
          found = true;
          break;
        }
      }
      if (!found) params->emplace_back(p->getLhs());
    }
  }

  if (netlist->param_assigns()) {
    for (auto ps : *m->getParamAssigns()) {
      ps->setParent(m);
      const std::string_view name = ps->getLhs()->getName();
      auto itr = paramSet.find(name);
      if (itr != paramSet.end()) {
        ps->setLhs((*itr).second);
      }
    }
  }
  return true;
}

uint32_t UhdmWriter::getVpiDirection(VObjectType type) {
  uint32_t direction = vpiInout;
  if (type == VObjectType::paPortDir_Inp ||
      type == VObjectType::paTfPortDir_Inp)
    direction = vpiInput;
  else if (type == VObjectType::paPortDir_Out ||
           type == VObjectType::paTfPortDir_Out)
    direction = vpiOutput;
  else if (type == VObjectType::paPortDir_Inout ||
           type == VObjectType::paTfPortDir_Inout)
    direction = vpiInout;
  else if (type == VObjectType::paTfPortDir_Ref ||
           type == VObjectType::paTfPortDir_ConstRef)
    direction = vpiRef;
  return direction;
}

uint32_t UhdmWriter::getVpiNetType(VObjectType type) {
  uint32_t nettype = 0;
  switch (type) {
    case VObjectType::paNetType_Wire:
      nettype = vpiWire;
      break;
    case VObjectType::paIntVec_TypeReg:
      nettype = vpiReg;
      break;
    case VObjectType::paNetType_Supply0:
      nettype = vpiSupply0;
      break;
    case VObjectType::paNetType_Supply1:
      nettype = vpiSupply1;
      break;
    case VObjectType::paIntVec_TypeLogic:
      nettype = vpiLogicNet;
      break;
    case VObjectType::paNetType_Wand:
      nettype = vpiWand;
      break;
    case VObjectType::paNetType_Wor:
      nettype = vpiWor;
      break;
    case VObjectType::paNetType_Tri:
      nettype = vpiTri;
      break;
    case VObjectType::paNetType_Tri0:
      nettype = vpiTri0;
      break;
    case VObjectType::paNetType_Tri1:
      nettype = vpiTri1;
      break;
    case VObjectType::paNetType_TriReg:
      nettype = vpiTriReg;
      break;
    case VObjectType::paNetType_TriAnd:
      nettype = vpiTriAnd;
      break;
    case VObjectType::paNetType_TriOr:
      nettype = vpiTriOr;
      break;
    case VObjectType::paNetType_Uwire:
      nettype = vpiUwire;
      break;
    case VObjectType::paImplicit_data_type:
    case VObjectType::paSigning_Signed:
    case VObjectType::paPacked_dimension:
    case VObjectType::paSigning_Unsigned:
      nettype = vpiNone;
      break;
    default:
      break;
  }
  return nettype;
}

void UhdmWriter::writePorts(const std::vector<Signal*>& orig_ports,
                            uhdm::BaseClass* parent, uhdm::Serializer& s,
                            ModportMap& modPortMap,
                            SignalBaseClassMap& signalBaseMap,
                            SignalMap& signalMap, ModuleInstance* instance,
                            DesignComponent* mod) {
  int32_t lastPortDirection = vpiInout;
  for (Signal* orig_port : orig_ports) {
    uhdm::Port* dest_port = s.make<uhdm::Port>();
    signalBaseMap.emplace(orig_port, dest_port);
    signalMap.emplace(orig_port->getName(), orig_port);

    if (orig_port->attributes()) {
      dest_port->setAttributes(orig_port->attributes());
      for (auto ats : *orig_port->attributes()) {
        ats->setParent(dest_port);
      }
    }

    const FileContent* fC = orig_port->getFileContent();
    if (fC->Type(orig_port->getNameId()) == VObjectType::slStringConst)
      dest_port->setName(orig_port->getName());
    if (orig_port->getDirection() != VObjectType::slNoType)
      lastPortDirection =
          UhdmWriter::getVpiDirection(orig_port->getDirection());
    dest_port->setDirection(lastPortDirection);
    if (const FileContent* const fC = orig_port->getFileContent()) {
      fC->populateCoreMembers(orig_port->getNameId(), orig_port->getNameId(),
                              dest_port);
    }
    dest_port->setParent(parent);
    if (Modport* orig_modport = orig_port->getModport()) {
      uhdm::RefObj* ref = s.make<uhdm::RefObj>();
      ref->setName(orig_port->getName());
      ref->setParent(dest_port);
      dest_port->setLowConn(ref);
      std::map<Modport*, uhdm::Modport*>::iterator itr =
          modPortMap.find(orig_modport);
      if (itr != modPortMap.end()) {
        ref->setActual((*itr).second);
      }
    } else if (ModuleDefinition* orig_interf = orig_port->getInterfaceDef()) {
      uhdm::RefObj* ref = s.make<uhdm::RefObj>();
      ref->setName(orig_port->getName());
      ref->setParent(dest_port);
      dest_port->setLowConn(ref);
      const auto& found = m_componentMap.find(orig_interf);
      if (found != m_componentMap.end()) {
        ref->setActual(found->second);
      }
    }
    if (NodeId defId = orig_port->getDefaultValue()) {
      if (uhdm::Any* exp = m_helper.compileExpression(
              mod, fC, defId, m_compileDesign, Reduce::No, dest_port, instance,
              false)) {
        dest_port->setHighConn(exp);
      }
    }
    if (orig_port->getTypespecId() && mod) {
      if (NodeId unpackedDimensions = orig_port->getUnpackedDimension()) {
        NodeId packedDimensions = orig_port->getPackedDimension();
        int32_t unpackedSize = 0;
        const FileContent* fC = orig_port->getFileContent();
        if (std::vector<uhdm::Range*>* ranges = m_helper.compileRanges(
                mod, fC, unpackedDimensions, m_compileDesign, Reduce::No,
                nullptr, instance, unpackedSize, false)) {
          uhdm::ArrayTypespec* array_ts = s.make<uhdm::ArrayTypespec>();
          array_ts->setRanges(ranges);
          array_ts->setParent(dest_port);
          fC->populateCoreMembers(unpackedDimensions, unpackedDimensions,
                                  array_ts);
          for (uhdm::Range* r : *ranges) {
            r->setParent(array_ts);
            const uhdm::Expr* rrange = r->getRightExpr();
            if (rrange->getValue() == "STRING:associative") {
              array_ts->setArrayType(vpiAssocArray);
              if (const uhdm::RefTypespec* rt = rrange->getTypespec()) {
                if (const uhdm::Typespec* ag = rt->getActual()) {
                  uhdm::RefTypespec* cro = s.make<uhdm::RefTypespec>();
                  cro->setName(ag->getName());
                  cro->setParent(array_ts);
                  cro->setFile(array_ts->getFile());
                  cro->setStartLine(array_ts->getStartLine());
                  cro->setStartColumn(array_ts->getStartColumn());
                  cro->setEndLine(array_ts->getEndLine());
                  cro->setEndColumn(array_ts->getEndColumn());
                  cro->setActual(const_cast<uhdm::Typespec*>(ag));
                  array_ts->setIndexTypespec(cro);
                }
              }
            } else if (rrange->getValue() == "STRING:unsized") {
              array_ts->setArrayType(vpiDynamicArray);
            } else if (rrange->getValue() == "STRING:$") {
              array_ts->setArrayType(vpiQueueArray);
            } else {
              array_ts->setArrayType(vpiStaticArray);
            }
          }
          if (dest_port->getTypespec() == nullptr) {
            uhdm::RefTypespec* dest_port_rt = s.make<uhdm::RefTypespec>();
            dest_port_rt->setName(fC->SymName(orig_port->getTypespecId()));
            dest_port_rt->setParent(dest_port);
            fC->populateCoreMembers(orig_port->getTypespecId(),
                                    orig_port->getTypespecId(), dest_port_rt);
            dest_port->setTypespec(dest_port_rt);
          }
          dest_port->getTypespec()->setActual(array_ts);

          if (uhdm::Typespec* ts = m_helper.compileTypespec(
                  mod, fC, orig_port->getTypespecId(), m_compileDesign,
                  Reduce::No, array_ts, nullptr, true)) {
            if (array_ts->getElemTypespec() == nullptr) {
              uhdm::RefTypespec* array_ts_rt = s.make<uhdm::RefTypespec>();
              array_ts_rt->setParent(array_ts);
              fC->populateCoreMembers(orig_port->getTypespecId(),
                                      packedDimensions
                                          ? packedDimensions
                                          : orig_port->getTypespecId(),
                                      array_ts_rt);
              array_ts_rt->setName(ts->getName());
              array_ts->setElemTypespec(array_ts_rt);
            }
            array_ts->getElemTypespec()->setActual(ts);
          }
        }
      } else if (uhdm::Typespec* ts = m_helper.compileTypespec(
                     mod, fC, orig_port->getTypespecId(), m_compileDesign,
                     Reduce::No, dest_port, nullptr, true)) {
        if (dest_port->getTypespec() == nullptr) {
          uhdm::RefTypespec* dest_port_rt = s.make<uhdm::RefTypespec>();
          dest_port_rt->setName(ts->getName());
          dest_port_rt->setParent(dest_port);
          dest_port->setTypespec(dest_port_rt);
          fC->populateCoreMembers(orig_port->getTypespecId(),
                                  orig_port->getTypespecId(), dest_port_rt);
        }
        dest_port->getTypespec()->setActual(ts);
      }
    }
  }
}

void UhdmWriter::writeDataTypes(const DesignComponent::DataTypeMap& datatypeMap,
                                uhdm::BaseClass* parent,
                                uhdm::TypespecCollection* dest_typespecs,
                                uhdm::Serializer& s, bool setParent) {
  std::set<uint64_t> ids;
  for (const uhdm::Typespec* t : *dest_typespecs) ids.emplace(t->getUhdmId());
  for (const auto& entry : datatypeMap) {
    const DataType* dtype = entry.second;
    if (dtype->getCategory() == DataType::Category::REF) {
      dtype = dtype->getDefinition();
    }
    if (dtype->getCategory() == DataType::Category::TYPEDEF) {
      if (dtype->getTypespec() == nullptr) dtype = dtype->getDefinition();
    }
    uhdm::Typespec* tps = dtype->getTypespec();
    tps = replace(tps, m_compileDesign->getSwapedObjects());
    if (parent->getUhdmType() == uhdm::UhdmType::Package) {
      if (tps && (tps->getName().find("::") == std::string::npos)) {
        const std::string newName =
            StrCat(parent->getName(), "::", tps->getName());
        tps->setName(newName);
      }
    }

    if (tps) {
      if (!tps->getInstance()) {
        if (parent->getUhdmType() != uhdm::UhdmType::ClassDefn)
          tps->setInstance((uhdm::Instance*)parent);
      }
      if (setParent && (tps->getParent() == nullptr)) {
        tps->setParent(parent);
        ids.emplace(tps->getUhdmId());
      } else if (ids.emplace(tps->getUhdmId()).second) {
        tps->setParent(parent);
      }
    }
  }
}

void UhdmWriter::writeNets(DesignComponent* mod,
                           const std::vector<Signal*>& orig_nets,
                           uhdm::BaseClass* parent, uhdm::Serializer& s,
                           SignalBaseClassMap& signalBaseMap,
                           SignalMap& signalMap, SignalMap& portMap,
                           ModuleInstance* instance /* = nullptr */) {
  for (auto& orig_net : orig_nets) {
    uhdm::Net* dest_net = nullptr;
    if (instance) {
      for (uhdm::Net* net : *instance->getNetlist()->nets()) {
        UhdmWriter::SignalMap::iterator itr = signalMap.find(net->getName());
        if (itr == signalMap.end()) {
          if (net->getName() == orig_net->getName()) {
            dest_net = net;
            break;
          }
        }
      }
    } else {
      dest_net = s.make<uhdm::LogicNet>();
    }
    if (dest_net) {
      const FileContent* fC = orig_net->getFileContent();
      if (fC->Type(orig_net->getNameId()) == VObjectType::slStringConst) {
        auto portItr = portMap.find(orig_net->getName());
        if (portItr != portMap.end()) {
          Signal* sig = (*portItr).second;
          if (sig) {
            UhdmWriter::SignalBaseClassMap::iterator itr =
                signalBaseMap.find(sig);
            if (itr != signalBaseMap.end()) {
              uhdm::Port* p = (uhdm::Port*)((*itr).second);
              NodeId nameId = orig_net->getNameId();
              if (p->getLowConn() == nullptr) {
                uhdm::RefObj* ref = s.make<uhdm::RefObj>();
                ref->setName(p->getName());
                ref->setActual(dest_net);
                ref->setParent(p);
                p->setLowConn(ref);
                fC->populateCoreMembers(nameId, nameId, ref);
              } else if (p->getLowConn()->getUhdmType() ==
                         uhdm::UhdmType::RefObj) {
                uhdm::RefObj* ref = (uhdm::RefObj*)p->getLowConn();
                ref->setName(p->getName());
                if (ref->getStartLine() == 0) {
                  fC->populateCoreMembers(nameId, nameId, ref);
                }
                if (ref->getActual() == nullptr) {
                  ref->setActual(dest_net);
                }
                ref->setParent(p);
              }
            }
          }
        } else if (dest_net->getTypespec() == nullptr) {
          // compileTypespec function need to account for range
          // location information if there is any in the typespec.
          if (orig_net->getTypespecId()) {
            if (uhdm::Typespec* ts = m_helper.compileTypespec(
                    mod, fC, orig_net->getTypespecId(), m_compileDesign,
                    Reduce::No, nullptr, nullptr, true)) {
              uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
              rt->setName(ts->getName());
              rt->setParent(dest_net);
              rt->setActual(ts);
              dest_net->setTypespec(rt);
              fC->populateCoreMembers(orig_net->getTypespecId(),
                                      orig_net->getTypespecId(), rt);
              NodeId dimensions = orig_net->getUnpackedDimension();
              if (!dimensions) dimensions = orig_net->getPackedDimension();
              if (dimensions) {
                fC->populateCoreMembers(InvalidNodeId, dimensions, ts);
              }
            }
          }
        }
        signalBaseMap.emplace(orig_net, dest_net);
        signalMap.emplace(orig_net->getName(), orig_net);
        dest_net->setName(orig_net->getName());
        if (const FileContent* const fC = orig_net->getFileContent()) {
          fC->populateCoreMembers(orig_net->getNameId(), orig_net->getNameId(),
                                  dest_net);
        }
        dest_net->setNetType(UhdmWriter::getVpiNetType(orig_net->getType()));
        dest_net->setParent(parent);
      }
    }
  }
}

void mapLowConns(const std::vector<Signal*>& orig_ports, uhdm::Serializer& s,
                 UhdmWriter::SignalBaseClassMap& signalBaseMap) {
  for (Signal* orig_port : orig_ports) {
    if (Signal* lowconn = orig_port->getLowConn()) {
      UhdmWriter::SignalBaseClassMap::iterator itrlow =
          signalBaseMap.find(lowconn);
      if (itrlow != signalBaseMap.end()) {
        UhdmWriter::SignalBaseClassMap::iterator itrport =
            signalBaseMap.find(orig_port);
        if (itrport != signalBaseMap.end()) {
          uhdm::RefObj* ref = s.make<uhdm::RefObj>();
          ((uhdm::Port*)itrport->second)->setLowConn(ref);
          ref->setParent(itrport->second);
          ref->setActual(itrlow->second);
          ref->setName(orig_port->getName());
          orig_port->getFileContent()->populateCoreMembers(
              orig_port->getNodeId(), orig_port->getNodeId(), ref);
        }
      }
    }
  }
}

void UhdmWriter::writeClass(ClassDefinition* classDef, uhdm::Serializer& s,
                            uhdm::BaseClass* parent) {
  if (!classDef->getFileContents().empty() &&
      classDef->getType() == VObjectType::paClass_declaration) {
    const FileContent* fC = classDef->getFileContents()[0];
    uhdm::ClassDefn* c = classDef->getUhdmModel<uhdm::ClassDefn>();
    m_componentMap.emplace(classDef, c);
    c->setParent(parent);
    c->setEndLabel(classDef->getEndLabel());
    c->setTaskFuncDecls(classDef->getTaskFuncDecls());

    // Typepecs
    uhdm::TypespecCollection* typespecs = c->getTypespecs(true);
    writeDataTypes(classDef->getDataTypeMap(), c, typespecs, s, true);

    // Variables
    // Already bound in TestbenchElaboration

    // Extends, fix late binding
    if (const uhdm::Extends* ext = c->getExtends()) {
      if (const uhdm::RefTypespec* ext_rt = ext->getClassTypespec()) {
        if (const uhdm::ClassTypespec* tps =
                ext_rt->getActual<uhdm::ClassTypespec>()) {
          if (tps->getClassDefn() == nullptr) {
            const std::string_view tpsName = tps->getName();
            if (c->getParameters()) {
              for (auto ps : *c->getParameters()) {
                if (ps->getName() == tpsName) {
                  if (ps->getUhdmType() == uhdm::UhdmType::TypeParameter) {
                    uhdm::TypeParameter* tp = (uhdm::TypeParameter*)ps;
                    if (const uhdm::RefTypespec* tp_rt = tp->getTypespec()) {
                      if (const uhdm::ClassTypespec* cptp =
                              tp_rt->getActual<uhdm::ClassTypespec>()) {
                        ((uhdm::ClassTypespec*)tps)
                            ->setClassDefn(
                                (uhdm::ClassDefn*)cptp->getClassDefn());
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    // Param_assigns
    if (classDef->getParamAssigns()) {
      c->setParamAssigns(classDef->getParamAssigns());
      for (auto ps : *c->getParamAssigns()) {
        ps->setParent(c);
      }
    }
    c->setParent(parent);

    const std::string_view name = classDef->getName();
    if (c->getName().empty()) c->setName(name);
    if (c->getFullName().empty()) c->setFullName(name);
    if (classDef->getAttributes() != nullptr) {
      c->setAttributes(classDef->getAttributes());
      for (auto a : *c->getAttributes()) {
        a->setParent(c);
      }
    }
    if (fC) {
      // Builtin classes have no file
      const NodeId modId = classDef->getNodeIds()[0];
      const NodeId startId = fC->sl_collect(modId, VObjectType::paCLASS);
      fC->populateCoreMembers(startId, modId, c);
    }
    // Activate when hier_path is better supported
    // lateTypedefBinding(s, classDef, c);
    // lateBinding(s, classDef, c);

    for (auto& nested : classDef->getClassMap()) {
      writeClass(nested.second, s, c);
    }
  }
}

void UhdmWriter::writeClasses(ClassNameClassDefinitionMultiMap& orig_classes,
                              uhdm::Serializer& s, uhdm::BaseClass* parent) {
  for (auto& orig_class : orig_classes) {
    writeClass(orig_class.second, s, parent);
  }
}

void UhdmWriter::writeVariables(const DesignComponent::VariableMap& orig_vars,
                                uhdm::BaseClass* parent, uhdm::Serializer& s) {
  for (auto& orig_var : orig_vars) {
    Variable* var = orig_var.second;
    const DataType* dtype = var->getDataType();
    const ClassDefinition* classdef = datatype_cast<ClassDefinition>(dtype);
    if (classdef) {
      uhdm::ClassVar* cvar = s.make<uhdm::ClassVar>();
      cvar->setName(var->getName());
      var->getFileContent()->populateCoreMembers(var->getNodeId(),
                                                 var->getNodeId(), cvar);
      cvar->setParent(parent);
      const auto& found = m_componentMap.find(classdef);
      if (found != m_componentMap.end()) {
        // TODO: Bind Class type,
        // class_var -> class_typespec -> class_defn
      }
    }
  }
}

class ReInstanceTypespec : public VpiListener {
 public:
  explicit ReInstanceTypespec(uhdm::Package* p) : m_package(p) {}
  ~ReInstanceTypespec() override = default;

  void leaveAny(const uhdm::Any* object, vpiHandle handle) final {
    if (any_cast<uhdm::Typespec>(object) != nullptr) {
      if ((object->getUhdmType() != uhdm::UhdmType::EventTypespec) &&
          (object->getUhdmType() != uhdm::UhdmType::ImportTypespec) &&
          (object->getUhdmType() != uhdm::UhdmType::TypeParameter)) {
        reInstance(object);
      }
    }
  }

  void leaveFunction(const uhdm::Function* object, vpiHandle handle) final {
    reInstance(object);
  }
  void leaveTask(const uhdm::Task* object, vpiHandle handle) final {
    reInstance(object);
  }
  void reInstance(const uhdm::Any* cobject) {
    if (cobject == nullptr) return;
    uhdm::Any* object = (uhdm::Any*)cobject;
    const uhdm::Instance* inst = nullptr;
    if (uhdm::Typespec* tps = any_cast<uhdm::Typespec>(object)) {
      inst = (uhdm::Instance*)tps->getInstance();
    } else if (uhdm::Function* tps = any_cast<uhdm::Function>(object)) {
      inst = (uhdm::Instance*)tps->getInstance();
    } else if (uhdm::Task* tps = any_cast<uhdm::Task>(object)) {
      inst = (uhdm::Instance*)tps->getInstance();
    }
    if (inst) {
      const std::string_view name = inst->getName();
      uhdm::Design* d = (uhdm::Design*)m_package->getParent();
      if (d->getAllPackages() != nullptr) {
        for (auto pack : *d->getAllPackages()) {
          if (pack->getName() == name) {
            if (uhdm::Typespec* tps = any_cast<uhdm::Typespec>(object)) {
              tps->setInstance(pack);
              if (const uhdm::EnumTypespec* et =
                      any_cast<uhdm::EnumTypespec>(cobject)) {
                reInstance(et->getBaseTypespec());
              }
            } else if (uhdm::Function* tps = any_cast<uhdm::Function>(object)) {
              tps->setInstance(pack);
            } else if (uhdm::Task* tps = any_cast<uhdm::Task>(object)) {
              tps->setInstance(pack);
            }
            break;
          }
        }
      }
    }
  }

 private:
  uhdm::Package* m_package = nullptr;
};

// Non-elaborated package typespec Instance relation need to point to
// non-elablarated package
void reInstanceTypespec(Serializer& serializer, uhdm::Any* root,
                        uhdm::Package* p) {
  ReInstanceTypespec* listener = new ReInstanceTypespec(p);
  vpiHandle handle = serializer.makeUhdmHandle(root->getUhdmType(), root);
  listener->listenAny(handle);
  vpi_release_handle(handle);
  delete listener;
}

void UhdmWriter::writePackage(Package* pack, uhdm::Package* p,
                              uhdm::Serializer& s, bool elaborated) {
  const uhdm::ScopedScope scopedScope(p);

  if (!pack->getEndLabel().empty()) {
    p->setEndLabel(pack->getEndLabel());
  }

  // Classes
  ClassNameClassDefinitionMultiMap& orig_classes = pack->getClassDefinitions();
  writeClasses(orig_classes, s, p);

  // Parameters
  if (p->getParameters()) {
    for (auto ps : *p->getParameters()) {
      if (ps->getUhdmType() == uhdm::UhdmType::Parameter) {
        ((uhdm::Parameter*)ps)
            ->setFullName(StrCat(pack->getName(), "::", ps->getName()));
      } else {
        ((uhdm::TypeParameter*)ps)
            ->setFullName(StrCat(pack->getName(), "::", ps->getName()));
      }
    }
  }

  // Param_assigns

  if (pack->getParamAssigns()) {
    p->setParamAssigns(pack->getParamAssigns());
    for (auto ps : *p->getParamAssigns()) {
      ps->setParent(p);
      reInstanceTypespec(s, ps, p);
    }
  }

  if (p->getTypespecs()) {
    for (auto t : *p->getTypespecs()) {
      reInstanceTypespec(s, t, p);
    }
  }

  if (p->getVariables()) {
    for (auto v : *p->getVariables()) {
      reInstanceTypespec(s, v, p);
    }
  }

  // Function and tasks
  if (pack->getTaskFuncs()) {
    for (auto tf : *pack->getTaskFuncs()) {
      const std::string_view funcName = tf->getName();
      if (funcName.find("::") != std::string::npos) {
        std::vector<std::string_view> res;
        StringUtils::tokenizeMulti(funcName, "::", res);
        const std::string_view className = res[0];
        const std::string_view funcName = res[1];
        bool foundParentClass = false;
        if (p->getClassDefns()) {
          for (auto cl : *p->getClassDefns()) {
            if (cl->getName() == className) {
              tf->setParent(cl, true);
              tf->setInstance(p);
              foundParentClass = true;
              break;
            }
          }
        }
        if (foundParentClass) {
          tf->setName(funcName);
          ((uhdm::TaskFunc*)tf)
              ->setFullName(StrCat(pack->getName(), "::", className,
                                   "::", tf->getName()));
        } else {
          tf->setParent(p);
          tf->setInstance(p);
          ((uhdm::TaskFunc*)tf)
              ->setFullName(StrCat(pack->getName(), "::", tf->getName()));
        }
      } else {
        tf->setParent(p);
        tf->setInstance(p);
        ((uhdm::TaskFunc*)tf)
            ->setFullName(StrCat(pack->getName(), "::", tf->getName()));
      }
    }
  }
  // Variables
  if (Netlist* netlist = pack->getNetlist()) {
    p->setVariables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->setParent(p);
        ((uhdm::Variables*)obj)
            ->setFullName(StrCat(pack->getName(), "::", obj->getName()));
      }
    }
  }
  // Nets
  SignalBaseClassMap signalBaseMap;
  SignalMap portMap;
  SignalMap netMap;
  const std::vector<Signal*>& orig_nets = pack->getSignals();
  writeNets(pack, orig_nets, p, s, signalBaseMap, netMap, portMap, nullptr);
}

void UhdmWriter::writeImportedSymbols(DesignComponent* mod, Serializer& s,
                                      TypespecCollection* typespecs) {
#if 0
  for (auto item : mod->getImportedSymbols()) {
    bool append = true;
    for (auto tpsiter : *typespecs) {
      if (item->getName() == tpsiter->getName()) {
        append = false;
        break;
      }
    }
    if (append) {  // Prevents multiple definition
      typespecs->push_back(item);
    }
    Constant* c = item->getItem();
    if (c) {
      std::string_view packName = item->getName();
      std::string_view typeName = c->getDecompile();
      Package* pack =
          m_compileDesign->getCompiler()->getDesign()->getPackage(packName);
      if (pack) {
        const auto& itr = m_componentMap.find(pack);
        if (itr != m_componentMap.end()) {
          Package* p = (Package*)itr->second;
          Typespec* tps = nullptr;
          EnumConst* cts = nullptr;
          if (p->getTypespecs()) {
            for (auto n : *p->getTypespecs()) {
              if (n->VpiName() == typeName) {
                tps = n;
                break;
              }
              const std::string pname = StrCat(p->getName(), "::", typeName);
              if (n->getName() == pname) {
                tps = n;
                break;
              }
              if (n->getUhdmType() == uhdm::UhdmType::EnumTypespec) {
                EnumTypespec* tpsiter = any_cast<EnumTypespec*>(n);
                if (tpsiter && tpsiter->getEnumConsts()) {
                  for (auto c : *tpsiter->getEnumConsts()) {
                    if (c->getName() == typeName) {
                      cts = c;
                      tps = tpsiter;
                      break;
                    }
                    if (pname == c->getName()) {
                      cts = c;
                      tps = tpsiter;
                      break;
                    }
                  }
                }
              }
              if (cts) break;
            }
          }
          if (cts) {
            // Ideally we would want to import only the given symbol,
            // But Synlig does not process that properly, so instead we import
            // the whole enum
            bool append = true;
            for (auto tpsiter : *typespecs) {
              if (tps->getName() == tpsiter->getName()) {
                append = false;
                break;
              }
            }
            if (append) {  // Prevents multiple definition
              ElaboratorContext elaboratorContext(&s, false, true);
              Typespec* item =
                  (Typespec*)uhdm::clone_tree(tps, &elaboratorContext);
              typespecs->push_back(item);
            }
          } else if (tps) {
            bool append = true;
            for (auto tpsiter : *typespecs) {
              if (tps->getName() == tpsiter->getName()) {
                append = false;
                break;
              }
            }
            if (append) {  // Prevents multiple definition
              ElaboratorContext elaboratorContext(&s, false, true);
              Typespec* item =
                  (Typespec*)uhdm::clone_tree(tps, &elaboratorContext);
              item->setName(typeName);
              typespecs->push_back(item);
            }
          }
        }
      }
    }
  }
#endif
}

void UhdmWriter::writeModule(ModuleDefinition* mod, uhdm::Module* m,
                             uhdm::Serializer& s,
                             InstanceDefinitionMap& instanceDefinitionMap,
                             ModportMap& modPortMap, ModuleInstance* instance) {
  const uhdm::ScopedScope scopedScope(m);
  SignalBaseClassMap signalBaseMap;
  SignalMap portMap;
  SignalMap netMap;

  m->setEndLabel(mod->getEndLabel());

  // Let decls
  if (!mod->getLetStmts().empty()) {
    for (auto& stmt : mod->getLetStmts()) {
      const_cast<uhdm::LetDecl*>(stmt.second->getDecl())->setParent(m);
    }
  }
  // Gen vars
  if (mod->getGenVars()) {
    for (auto var : *mod->getGenVars()) {
      var->setParent(m);
    }
  }
  // Gen stmts
  if (mod->getGenStmts()) {
    for (auto stmt : *mod->getGenStmts()) {
      stmt->setParent(m);
    }
  }
  if (!mod->getPropertyDecls().empty()) {
    for (auto decl : mod->getPropertyDecls()) {
      decl->setParent(m);
    }
  }
  if (!mod->getSequenceDecls().empty()) {
    for (auto decl : mod->getSequenceDecls()) {
      decl->setParent(m);
    }
  }

  // writeImportedSymbols(mod, s, typespecs);
  // Ports
  const std::vector<Signal*>& orig_ports = mod->getPorts();
  writePorts(orig_ports, m, s, modPortMap, signalBaseMap, portMap, instance,
             mod);
  // Nets
  mapLowConns(orig_ports, s, signalBaseMap);
  // Classes
  ClassNameClassDefinitionMultiMap& orig_classes = mod->getClassDefinitions();
  writeClasses(orig_classes, s, m);

  // Function and tasks
  if ((m_helper.getElaborate() == Elaborate::Yes) && m->getTaskFuncs()) {
    for (auto tf : *m->getTaskFuncs()) {
      if (tf->getInstance() == nullptr) tf->setInstance(m);
    }
  }

  // ClockingBlocks
  for (const auto& ctupple : mod->getClockingBlockMap()) {
    const ClockingBlock& cblock = ctupple.second;
    cblock.getActual()->setParent(m);
    switch (cblock.getType()) {
      case ClockingBlock::Type::Default: {
        m->setDefaultClocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Global: {
        m->setGlobalClocking(cblock.getActual());
        break;
      }
      default:
        break;
    }
  }

  // Assertions
  if (mod->getAssertions()) {
    for (auto ps : *mod->getAssertions()) {
      ps->setParent(m);
    }
  }
  // Module Instantiation
  if (std::vector<uhdm::RefModule*>* subModules = mod->getRefModules()) {
    for (auto subModArr : *subModules) {
      subModArr->setParent(m);
    }
  }
  if (uhdm::ModuleArrayCollection* subModuleArrays = mod->getModuleArrays()) {
    for (auto subModArr : *subModuleArrays) {
      subModArr->setParent(m);
    }
  }
  if (uhdm::PrimitiveCollection* subModules = mod->getPrimitives()) {
    for (auto subModArr : *subModules) {
      subModArr->setParent(m);
    }
  }
  if (uhdm::PrimitiveArrayCollection* subModules = mod->getPrimitiveArrays()) {
    for (auto subModArr : *subModules) {
      subModArr->setParent(m);
    }
  }
  // Interface instantiation
  const std::vector<Signal*>& signals = mod->getSignals();
  if (!signals.empty()) {
    uhdm::InterfaceArrayCollection* subInterfaceArrays =
        m->getInterfaceArrays(true);
    for (Signal* sig : signals) {
      NodeId unpackedDimension = sig->getUnpackedDimension();
      if (unpackedDimension && sig->getInterfaceDef()) {
        int32_t unpackedSize = 0;
        const FileContent* fC = sig->getFileContent();
        if (std::vector<uhdm::Range*>* unpackedDimensions =
                m_helper.compileRanges(mod, fC, unpackedDimension,
                                       m_compileDesign, Reduce::No, nullptr,
                                       instance, unpackedSize, false)) {
          NodeId id = sig->getNodeId();
          const std::string typeName = sig->getInterfaceTypeName();
          uhdm::InterfaceArray* smarray = s.make<uhdm::InterfaceArray>();
          smarray->setRanges(unpackedDimensions);
          for (auto d : *unpackedDimensions) d->setParent(smarray);
          if (fC->Type(sig->getNameId()) == VObjectType::slStringConst) {
            smarray->setName(sig->getName());
          }
          smarray->setFullName(typeName);
          smarray->setParent(m);
          fC->populateCoreMembers(id, id, smarray);

          NodeId typespecStart = sig->getInterfaceTypeNameId();
          NodeId typespecEnd = typespecStart;
          while (fC->Sibling(typespecEnd)) {
            typespecEnd = fC->Sibling(typespecEnd);
          }
          uhdm::InterfaceTypespec* tps = s.make<uhdm::InterfaceTypespec>();
          if (smarray->getElemTypespec() == nullptr) {
            uhdm::RefTypespec* tps_rt = s.make<uhdm::RefTypespec>();
            tps_rt->setParent(smarray);
            smarray->setElemTypespec(tps_rt);
          }
          smarray->getElemTypespec()->setActual(tps);
          tps->setName(typeName);
          fC->populateCoreMembers(typespecStart, typespecEnd, tps);

          subInterfaceArrays->emplace_back(smarray);
        }
      }
    }
  }
}

void UhdmWriter::writeInterface(ModuleDefinition* mod, uhdm::Interface* m,
                                uhdm::Serializer& s, ModportMap& modPortMap,
                                ModuleInstance* instance) {
  const uhdm::ScopedScope scopedScope(m);

  SignalBaseClassMap signalBaseMap;
  SignalMap portMap;
  SignalMap netMap;

  m->setEndLabel(mod->getEndLabel());

  // Let decls
  if (!mod->getLetStmts().empty()) {
    uhdm::LetDeclCollection* decls = m->getLetDecls(true);
    for (auto stmt : mod->getLetStmts()) {
      decls->emplace_back((uhdm::LetDecl*)stmt.second->getDecl());
    }
  }
  // Gen stmts
  if (mod->getGenStmts()) {
    for (auto stmt : *mod->getGenStmts()) {
      stmt->setParent(m);
    }
  }
  if (!mod->getPropertyDecls().empty()) {
    for (auto decl : mod->getPropertyDecls()) {
      decl->setParent(m);
    }
  }
  if (!mod->getSequenceDecls().empty()) {
    for (auto decl : mod->getSequenceDecls()) {
      decl->setParent(m);
    }
  }

  // Typepecs
  uhdm::TypespecCollection* typespecs = m->getTypespecs(true);
  writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, true);
  writeImportedSymbols(mod, s, typespecs);
  // Ports
  const std::vector<Signal*>& orig_ports = mod->getPorts();
  writePorts(orig_ports, m, s, modPortMap, signalBaseMap, portMap, instance,
             mod);
  const std::vector<Signal*>& orig_nets = mod->getSignals();
  writeNets(mod, orig_nets, m, s, signalBaseMap, netMap, portMap, instance);

  // Modports
  ModuleDefinition::ModportSignalMap& orig_modports =
      mod->getModportSignalMap();
  for (auto& orig_modport : orig_modports) {
    uhdm::Modport* dest_modport = s.make<uhdm::Modport>();
    // dest_modport->Interface(m); // Loop in elaboration!
    dest_modport->setParent(m);
    const FileContent* orig_fC = orig_modport.second.getFileContent();
    const NodeId orig_nodeId = orig_modport.second.getNodeId();
    orig_fC->populateCoreMembers(orig_nodeId, orig_nodeId, dest_modport);
    modPortMap.emplace(&orig_modport.second, dest_modport);
    dest_modport->setName(orig_modport.first);
    for (auto& sig : orig_modport.second.getPorts()) {
      const FileContent* fC = sig.getFileContent();
      uhdm::IODecl* io = s.make<uhdm::IODecl>();
      io->setName(sig.getName());
      fC->populateCoreMembers(sig.getNameId(), sig.getNameId(), io);
      if (NodeId Expression = fC->Sibling(sig.getNodeId())) {
        m_helper.checkForLoops(true);
        if (uhdm::Any* exp =
                m_helper.compileExpression(mod, fC, Expression, m_compileDesign,
                                           Reduce::Yes, io, instance, true)) {
          io->setExpr(exp);
        }
        m_helper.checkForLoops(false);
      }
      uint32_t direction = UhdmWriter::getVpiDirection(sig.getDirection());
      io->setDirection(direction);
      io->setParent(dest_modport);
    }
  }

  // Cont assigns
  if (mod->getContAssigns()) {
    for (auto ps : *mod->getContAssigns()) {
      ps->setParent(m);
    }
  }

  // Assertions
  if (mod->getAssertions()) {
    for (auto ps : *mod->getAssertions()) {
      ps->setParent(m);
    }
  }

  // Processes
  if (mod->getProcesses()) {
    for (auto ps : *mod->getProcesses()) {
      ps->setParent(m);
    }
  }

  // Function and tasks
  if ((m_helper.getElaborate() == Elaborate::Yes) && m->getTaskFuncs()) {
    for (auto tf : *m->getTaskFuncs()) {
      if (tf->getInstance() == nullptr) tf->setInstance(m);
    }
  }

  // ClockingBlocks
  for (const auto& ctupple : mod->getClockingBlockMap()) {
    const ClockingBlock& cblock = ctupple.second;
    cblock.getActual()->setParent(m);
    switch (cblock.getType()) {
      case ClockingBlock::Type::Default: {
        m->setDefaultClocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Global: {
        m->setGlobalClocking(cblock.getActual());
        break;
      }
      default:
        break;
    }
  }
}

void UhdmWriter::writeProgram(Program* mod, uhdm::Program* m,
                              uhdm::Serializer& s, ModportMap& modPortMap,
                              ModuleInstance* instance) {
  const uhdm::ScopedScope scopedScope(m);

  SignalBaseClassMap signalBaseMap;
  SignalMap portMap;
  SignalMap netMap;

  m->setEndLabel(mod->getEndLabel());

  // Typepecs
  uhdm::TypespecCollection* typespecs = m->getTypespecs(true);
  writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, true);
  writeImportedSymbols(mod, s, typespecs);
  // Ports
  const std::vector<Signal*>& orig_ports = mod->getPorts();
  writePorts(orig_ports, m, s, modPortMap, signalBaseMap, portMap, instance,
             mod);

  // Nets
  const std::vector<Signal*>& orig_nets = mod->getSignals();
  writeNets(mod, orig_nets, m, s, signalBaseMap, netMap, portMap, instance);
  mapLowConns(orig_ports, s, signalBaseMap);

  // Assertions
  if (mod->getAssertions()) {
    for (auto ps : *mod->getAssertions()) {
      ps->setParent(m);
    }
  }

  // Classes
  ClassNameClassDefinitionMultiMap& orig_classes = mod->getClassDefinitions();
  writeClasses(orig_classes, s, m);

  // Variables
  const DesignComponent::VariableMap& orig_vars = mod->getVariables();
  writeVariables(orig_vars, m, s);

  // Cont assigns
  if (mod->getContAssigns()) {
    for (auto ps : *mod->getContAssigns()) {
      ps->setParent(m);
    }
  }
  // Processes
  if (mod->getProcesses()) {
    for (auto ps : *mod->getProcesses()) {
      ps->setParent(m);
    }
  }
  if (mod->getTaskFuncs()) {
    for (auto tf : *mod->getTaskFuncs()) {
      tf->setParent(m);
    }
  }

  // ClockingBlocks
  for (const auto& ctupple : mod->getClockingBlockMap()) {
    const ClockingBlock& cblock = ctupple.second;
    cblock.getActual()->setParent(m);
    switch (cblock.getType()) {
      case ClockingBlock::Type::Default: {
        m->setDefaultClocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Global: {
        // m->Global_clocking(cblock.getActual());
        break;
      }
      default:
        break;
    }
  }
}

bool UhdmWriter::writeElabProgram(Serializer& s, ModuleInstance* instance,
                                  uhdm::Program* m, ModportMap& modPortMap) {
  Netlist* netlist = instance->getNetlist();
  DesignComponent* mod = instance->getDefinition();
  if (mod) {
    // Let decls
    if (!mod->getLetStmts().empty()) {
      for (auto& stmt : mod->getLetStmts()) {
        const_cast<uhdm::LetDecl*>(stmt.second->getDecl())->setParent(m);
      }
    }
    if (!mod->getPropertyDecls().empty()) {
      for (auto decl : mod->getPropertyDecls()) {
        decl->setParent(m);
      }
    }
    if (!mod->getSequenceDecls().empty()) {
      for (auto decl : mod->getSequenceDecls()) {
        decl->setParent(m);
      }
    }
    // Typepecs
    uhdm::TypespecCollection* typespecs = m->getTypespecs(true);
    writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, false);
    writeImportedSymbols(mod, s, typespecs);
    // Assertions
    if (mod->getAssertions()) {
      for (auto ps : *mod->getAssertions()) {
        ps->setParent(m);
      }
    }
  }
  if (netlist) {
    m->setPorts(netlist->ports());
    if (netlist->ports()) {
      typedef std::map<const uhdm::Modport*, Modport*> PortModportMap;
      PortModportMap portModportMap;
      for (auto& entry : netlist->getModportMap()) {
        portModportMap.emplace(entry.second.second, entry.second.first);
      }

      for (auto obj : *netlist->ports()) {
        obj->setParent(m);

        if (auto lc = obj->getLowConn()) {
          if (const uhdm::RefObj* ro = any_cast<uhdm::RefObj>(lc)) {
            if (const uhdm::Any* ag = ro->getActual()) {
              if (ag->getUhdmType() == uhdm::UhdmType::Modport) {
                PortModportMap::const_iterator it1 =
                    portModportMap.find((const uhdm::Modport*)ag);
                if (it1 != portModportMap.end()) {
                  ModportMap::const_iterator it2 = modPortMap.find(it1->second);
                  if (it2 != modPortMap.end()) {
                    const_cast<uhdm::RefObj*>(ro)->setActual(it2->second);
                  }
                }
              }
            }
          }
        }
      }
    }
    m->setNets(netlist->nets());
    if (netlist->nets()) {
      for (auto obj : *netlist->nets()) {
        obj->setParent(m);
      }
    }
    m->setGenScopeArrays(netlist->gen_scopes());
    m->setVariables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->setParent(m);
      }
    }
    m->setRegArrays(netlist->array_vars());
    if (netlist->array_vars()) {
      for (auto obj : *netlist->array_vars()) {
        obj->setParent(m);
      }
    }
    m->setNamedEvents(netlist->named_events());
    if (netlist->named_events()) {
      for (auto obj : *netlist->named_events()) {
        obj->setParent(m);
      }
    }
    m->setArrayNets(netlist->array_nets());
    if (netlist->array_nets()) {
      for (auto obj : *netlist->array_nets()) {
        obj->setParent(m);
      }
    }

    // Cont assigns
    m->setContAssigns(mod->getContAssigns());
    if (m->getContAssigns()) {
      for (auto ps : *m->getContAssigns()) {
        ps->setParent(m);
      }
    }
    // Processes
    m->setProcesses(mod->getProcesses());
    if (m->getProcesses()) {
      for (auto ps : *m->getProcesses()) {
        ps->setParent(m);
      }
    }
  }
  if (mod) {
    if (auto from = mod->getTaskFuncs()) {
      uhdm::TaskFuncCollection* target = m->getTaskFuncs(true);
      for (auto tf : *from) {
        target->emplace_back(tf);
        if (tf->getParent() == nullptr) tf->setParent(m);
        if (tf->getInstance() == nullptr) tf->setInstance(m);
      }
    }
  }

  if (mod) {
    // ClockingBlocks
    ModuleDefinition* def = (ModuleDefinition*)mod;
    for (const auto& ctupple : def->getClockingBlockMap()) {
      const ClockingBlock& cblock = ctupple.second;
      switch (cblock.getType()) {
        case ClockingBlock::Type::Default: {
          uhdm::ElaboratorContext elaboratorContext(&s, false, true);
          uhdm::ClockingBlock* cb = (uhdm::ClockingBlock*)uhdm::clone_tree(
              cblock.getActual(), &elaboratorContext);
          cb->setParent(m);
          m->setDefaultClocking(cb);
          break;
        }
        case ClockingBlock::Type::Global: {
          // m->Global_clocking(cblock.getActual());
          break;
        }
        case ClockingBlock::Type::Regular: {
          uhdm::ElaboratorContext elaboratorContext(&s, false, true);
          uhdm::ClockingBlock* cb = (uhdm::ClockingBlock*)uhdm::clone_tree(
              cblock.getActual(), &elaboratorContext);
          cb->setParent(m);
          break;
        }
      }
    }
  }

  return true;
}

class DetectUnsizedConstant final : public VpiListener {
 public:
  DetectUnsizedConstant() = default;
  bool unsizedDetected() { return m_unsized; }

 private:
  void leaveConstant(const uhdm::Constant* object, vpiHandle handle) final {
    if (object->getSize() == -1) m_unsized = true;
  }
  bool m_unsized = false;
};

void UhdmWriter::writeContAssign(Netlist* netlist, uhdm::Serializer& s,
                                 DesignComponent* mod, uhdm::Any* m,
                                 std::vector<uhdm::ContAssign*>* assigns) {
  FileSystem* const fileSystem = m_session->getFileSystem();
  SymbolTable* const symbols = m_session->getSymbolTable();
  if (netlist->cont_assigns()) {
    for (auto assign : *netlist->cont_assigns()) {
      const uhdm::Expr* lhs = assign->getLhs();
      const uhdm::Expr* rhs = assign->getRhs();
      const uhdm::Expr* delay = assign->getDelay();
      const uhdm::Typespec* tps = nullptr;
      if (const uhdm::RefTypespec* rt = lhs->getTypespec()) {
        tps = rt->getActual();
      }
      bool simplified = false;
      bool cloned = false;
      if (delay && delay->getUhdmType() == uhdm::UhdmType::RefObj) {
        uhdm::Any* var = m_helper.bindParameter(
            mod, netlist->getParent(), delay->getName(), m_compileDesign, true);
        uhdm::ElaboratorContext elaboratorContext(&s, false, true);
        assign =
            (uhdm::ContAssign*)uhdm::clone_tree(assign, &elaboratorContext);
        lhs = assign->getLhs();
        rhs = assign->getRhs();
        if (const uhdm::RefTypespec* rt = lhs->getTypespec()) {
          tps = rt->getActual();
        }
        delay = assign->getDelay();
        uhdm::RefObj* ref = (uhdm::RefObj*)delay;
        ref->setActual(var);
        cloned = true;
      }

      if (lhs->getUhdmType() == uhdm::UhdmType::RefObj) {
        uhdm::Any* var =
            m_helper.bindVariable(mod, m, lhs->getName(), m_compileDesign);
        if (var) {
          if (rhs->getUhdmType() == uhdm::UhdmType::Operation) {
            if (cloned == false) {
              uhdm::ElaboratorContext elaboratorContext(&s, false, true);
              const uhdm::Any* pp = assign->getParent();
              assign = (uhdm::ContAssign*)uhdm::clone_tree(assign,
                                                           &elaboratorContext);
              if (pp != nullptr) assign->setParent(const_cast<uhdm::Any*>(pp));
              lhs = assign->getLhs();
              rhs = assign->getRhs();
              m_helper.checkForLoops(true);
              bool invalidValue = false;
              uhdm::Any* rhstmp = m_helper.reduceExpr(
                  (uhdm::Expr*)rhs, invalidValue, mod, m_compileDesign,
                  netlist->getParent(),
                  fileSystem->toPathId(rhs->getFile(), symbols),
                  rhs->getStartLine(), assign, true);
              m_helper.checkForLoops(false);
              if (const uhdm::RefTypespec* rt = lhs->getTypespec()) {
                tps = rt->getActual();
              }
              if (uhdm::Expr* exp = any_cast<uhdm::Expr>(var)) {
                if (const uhdm::RefTypespec* rt = exp->getTypespec()) {
                  if (const uhdm::Typespec* temp = rt->getActual()) {
                    tps = temp;
                  }
                }
              }
              if (!invalidValue && rhstmp) {
                if (rhstmp->getUhdmType() == uhdm::UhdmType::Constant)
                  rhstmp = m_helper.adjustSize(tps, mod, m_compileDesign,
                                               netlist->getParent(),
                                               (uhdm::Constant*)rhstmp, true);
                assign->setRhs((uhdm::Expr*)rhstmp);
              }
              rhs = assign->getRhs();
              delay = assign->getDelay();
            }
            uhdm::RefObj* ref = (uhdm::RefObj*)lhs;
            ref->setActual(var);
            cloned = true;
          }

          if (uhdm::Expr* exp = any_cast<uhdm::Expr>(var)) {
            if (const uhdm::RefTypespec* rt = exp->getTypespec()) {
              if (const uhdm::Typespec* temp = rt->getActual()) {
                tps = temp;
              }
            }
          }
        }
      }
      if (tps) {
        uhdm::ExprEval eval(true);
        uhdm::Expr* tmp =
            eval.flattenPatternAssignments(s, tps, (uhdm::Expr*)rhs);
        if (tmp->getUhdmType() == uhdm::UhdmType::Operation) {
          if (cloned == false) {
            uhdm::ElaboratorContext elaboratorContext(&s, false, true);
            const uhdm::Any* pp = assign->getParent();
            assign =
                (uhdm::ContAssign*)uhdm::clone_tree(assign, &elaboratorContext);
            if (pp != nullptr) assign->setParent(const_cast<uhdm::Any*>(pp));
            assign->setParent(m);
            lhs = assign->getLhs();
            rhs = assign->getRhs();
            delay = assign->getDelay();
            if (const uhdm::RefTypespec* rt = lhs->getTypespec()) {
              tps = rt->getActual();
            }
            cloned = true;
          }
          ((uhdm::Operation*)rhs)
              ->setOperands(((uhdm::Operation*)tmp)->getOperands());
          for (auto o : *((uhdm::Operation*)tmp)->getOperands()) {
            o->setParent(const_cast<uhdm::Expr*>(rhs));
          }
          uhdm::Operation* op = (uhdm::Operation*)rhs;
          int32_t opType = op->getOpType();
          if (opType == vpiAssignmentPatternOp || opType == vpiConditionOp) {
            if (m_helper.substituteAssignedValue(rhs, m_compileDesign)) {
              rhs = m_helper.expandPatternAssignment(
                  tps, (uhdm::Expr*)rhs, mod, m_compileDesign,
                  m_helper.getReduce(), netlist->getParent());
            }
          }
          rhs = (uhdm::Expr*)m_helper.defaultPatternAssignment(
              tps, (uhdm::Expr*)rhs, mod, m_compileDesign, m_helper.getReduce(),
              netlist->getParent());

          assign->setRhs((uhdm::Expr*)rhs);
          m_helper.reorderAssignmentPattern(mod, lhs, (uhdm::Expr*)rhs,
                                            m_compileDesign,
                                            netlist->getParent(), 0);
          simplified = true;
        }
      } else if (rhs->getUhdmType() == uhdm::UhdmType::Operation) {
        uhdm::Operation* op = (uhdm::Operation*)rhs;
        if (const uhdm::RefTypespec* ro1 = op->getTypespec()) {
          if (const uhdm::Typespec* tps = ro1->getActual()) {
            uhdm::ExprEval eval(true);
            uhdm::Expr* tmp =
                eval.flattenPatternAssignments(s, tps, (uhdm::Expr*)rhs);
            if (tmp->getUhdmType() == uhdm::UhdmType::Operation) {
              if (cloned == false) {
                uhdm::ElaboratorContext elaboratorContext(&s, false, true);
                assign = (uhdm::ContAssign*)uhdm::clone_tree(
                    assign, &elaboratorContext);
                assign->setParent(m);
                lhs = assign->getLhs();
                rhs = assign->getRhs();
                delay = assign->getDelay();
                if (const uhdm::RefTypespec* ro2 = lhs->getTypespec()) {
                  tps = ro2->getActual();
                }
                cloned = true;
              }
              ((uhdm::Operation*)rhs)
                  ->setOperands(((uhdm::Operation*)tmp)->getOperands());
              simplified = true;
            }
          }
        }
      }
      if (simplified == false) {
        bool invalidValue = false;
        if ((rhs->getUhdmType() == uhdm::UhdmType::SysFuncCall) &&
            ((uhdm::Expr*)rhs)->getTypespec() == nullptr) {
          if (((uhdm::Expr*)rhs)->getTypespec() == nullptr) {
            uhdm::RefTypespec* crt = s.make<uhdm::RefTypespec>();
            crt->setParent((uhdm::Expr*)rhs);
            ((uhdm::Expr*)rhs)->setTypespec(crt);
          }
          ((uhdm::Expr*)rhs)
              ->getTypespec()
              ->setActual(const_cast<uhdm::Typespec*>(tps));
        }
        m_helper.checkForLoops(true);
        uhdm::Any* res = m_helper.reduceExpr(
            (uhdm::Expr*)rhs, invalidValue, mod, m_compileDesign,
            netlist->getParent(), fileSystem->toPathId(rhs->getFile(), symbols),
            rhs->getStartLine(), assign, true);
        m_helper.checkForLoops(false);
        if (!invalidValue && res &&
            (res->getUhdmType() == uhdm::UhdmType::Constant)) {
          if (cloned == false) {
            uhdm::ElaboratorContext elaboratorContext(&s, false, true);
            assign =
                (uhdm::ContAssign*)uhdm::clone_tree(assign, &elaboratorContext);
            assign->setParent(m);
            lhs = assign->getLhs();
            cloned = true;
            res = m_helper.adjustSize(tps, mod, m_compileDesign,
                                      netlist->getParent(),
                                      (uhdm::Constant*)res, true);
            res->setParent(assign);
          }
          assign->setRhs((uhdm::Constant*)res);
        }
      }
      if (simplified == false && cloned == false) {
        DetectUnsizedConstant detector;
        vpiHandle h_rhs = NewVpiHandle(rhs);
        detector.listenAny(h_rhs);
        vpi_free_object(h_rhs);
        if (detector.unsizedDetected()) {
          uhdm::ElaboratorContext elaboratorContext(&s, false, true);
          assign =
              (uhdm::ContAssign*)uhdm::clone_tree(assign, &elaboratorContext);
          assign->setParent(m);
          cloned = true;
        }
      }
      if (tps != nullptr) const_cast<uhdm::Typespec*>(tps)->setParent(nullptr);
      if (cloned || (assign->getParent() == nullptr)) assign->setParent(m);
      assigns->emplace_back(assign);
    }
  }
}

bool UhdmWriter::writeElabGenScope(Serializer& s, ModuleInstance* instance,
                                   uhdm::GenScope* m,
                                   ExprBuilder& exprBuilder) {
  FileSystem* const fileSystem = m_session->getFileSystem();
  Netlist* netlist = instance->getNetlist();
  ModuleDefinition* mod =
      valuedcomponenti_cast<ModuleDefinition>(instance->getDefinition());
  if (mod) {
    // Let decls
    if (!mod->getLetStmts().empty()) {
      uhdm::LetDeclCollection* decls = m->getLetDecls(true);
      for (auto stmt : mod->getLetStmts()) {
        decls->emplace_back((uhdm::LetDecl*)stmt.second->getDecl());
      }
    }
    if (!mod->getPropertyDecls().empty()) {
      uhdm::PropertyDeclCollection* decls = m->getPropertyDecls(true);
      for (auto decl : mod->getPropertyDecls()) {
        decl->setParent(m);
        decls->emplace_back(decl);
      }
    }
    if (!mod->getSequenceDecls().empty()) {
      uhdm::SequenceDeclCollection* decls = m->getSequenceDecls(true);
      for (auto decl : mod->getSequenceDecls()) {
        decl->setParent(m);
        decls->emplace_back(decl);
      }
    }
    // Typepecs
    uhdm::TypespecCollection* typespecs = m->getTypespecs(true);
    writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, true);
    writeImportedSymbols(mod, s, typespecs);
    // System elab tasks
    m->setSysTaskCalls((std::vector<uhdm::TFCall*>*)&mod->getElabSysCalls());
    if (m->getSysTaskCalls()) {
      for (auto et : *m->getSysTaskCalls()) {
        et->setParent(m);
      }
    }
    // Assertions
    if (mod->getAssertions()) {
      m->setAssertions(mod->getAssertions());
      for (auto ps : *m->getAssertions()) {
        ps->setParent(m);
      }
    }
  }
  if (netlist) {
    m->setNets(netlist->nets());
    if (netlist->nets()) {
      for (auto obj : *netlist->nets()) {
        obj->setParent(m);
      }
    }

    if (netlist->cont_assigns()) {
      std::vector<uhdm::ContAssign*>* assigns = m->getContAssigns(true);
      writeContAssign(netlist, s, mod, m, assigns);
      for (auto obj : *assigns) {
        obj->setParent(m);
      }
    }

    // Processes
    if (netlist->process_stmts()) {
      m->setProcess(netlist->process_stmts());
      for (auto ps : *m->getProcess()) {
        ps->setParent(m);
      }
    }

    std::vector<uhdm::GenScopeArray*>* gen_scope_arrays = netlist->gen_scopes();
    if (gen_scope_arrays) {
      writeElabParameters(s, instance, m, exprBuilder);

      // Loop indexes
      for (auto& param : instance->getMappedValues()) {
        const std::string_view name = param.first;
        Value* val = param.second.first;
        uhdm::AnyCollection* params = m->getParameters(true);
        bool found = false;
        for (auto p : *params) {
          if (p->getName() == name) {
            found = true;
            break;
          }
        }
        if (!found) {
          uhdm::Parameter* p = s.make<uhdm::Parameter>();
          p->setName(name);
          if (val && val->isValid()) p->setValue(val->uhdmValue());
          p->setFile(fileSystem->toPath(instance->getFileId()));
          p->setStartLine(param.second.second);
          p->setParent(m);
          p->setLocalParam(true);
          uhdm::IntTypespec* ts = s.make<uhdm::IntTypespec>();
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(p);
          p->setTypespec(rt);
          rt->setActual(ts);
          params->emplace_back(p);
        }
      }
    }

    m->setVariables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->setParent(m);
      }
    }
    m->setRegArrays(netlist->array_vars());
    if (netlist->array_vars()) {
      for (auto obj : *netlist->array_vars()) {
        obj->setParent(m);
      }
    }
    m->setNamedEvents(netlist->named_events());
    if (netlist->named_events()) {
      for (auto obj : *netlist->named_events()) {
        obj->setParent(m);
      }
    }
    m->setArrayNets(netlist->array_nets());
    if (netlist->array_nets()) {
      for (auto obj : *netlist->array_nets()) {
        obj->setParent(m);
      }
    }
  }

  DesignComponent* def = instance->getDefinition();
  if (def->getTaskFuncs()) {
    // Function and tasks
    uhdm::TaskFuncCollection* target = m->getTaskFuncs(true);
    for (auto tf : *def->getTaskFuncs()) {
      target->emplace_back(tf);
      if (tf->getParent() == nullptr) tf->setParent(m);
    }
  }

  // ClockingBlocks
  for (const auto& ctupple : mod->getClockingBlockMap()) {
    const ClockingBlock& cblock = ctupple.second;
    switch (cblock.getType()) {
      case ClockingBlock::Type::Default: {
        // No default clocking
        // m->Default_clocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Regular: {
        uhdm::ElaboratorContext elaboratorContext(&s, false, true);
        uhdm::ClockingBlock* cb = (uhdm::ClockingBlock*)uhdm::clone_tree(
            cblock.getActual(), &elaboratorContext);
        cb->setParent(m);
        break;
      }
      default:
        break;
    }
  }

  return true;
}

uhdm::Any* UhdmWriter::swapForSpecifiedVar(
    uhdm::Serializer& s, DesignComponent* mod, uhdm::Any* tmp,
    uhdm::VariablesCollection* lvariables, uhdm::Variables* lvariable,
    std::string_view name, const uhdm::Any* var, const uhdm::Any* parent) {
  FileSystem* const fileSystem = m_session->getFileSystem();
  SymbolTable* const symbols = m_session->getSymbolTable();
  if (tmp->getName() == name) {
    if (var->getUhdmType() == uhdm::UhdmType::RefVar) {
      uhdm::RefVar* ref = (uhdm::RefVar*)var;
      const uhdm::Typespec* tp = nullptr;
      if (uhdm::RefTypespec* rt = ref->getTypespec()) tp = rt->getActual();
      if (tp && tp->getUhdmType() == uhdm::UhdmType::UnsupportedTypespec) {
        const uhdm::Typespec* indexTypespec = nullptr;
        if (lvariables) {
          for (auto var : *lvariables) {
            if (var->getUhdmType() == uhdm::UhdmType::HierPath) {
              PathId parentFileId =
                  fileSystem->toPathId(parent->getFile(), symbols);
              bool invalidValue = false;
              indexTypespec = (uhdm::Typespec*)m_helper.decodeHierPath(
                  (uhdm::HierPath*)var, invalidValue, mod, m_compileDesign,
                  Reduce::Yes, nullptr, parentFileId, parent->getStartLine(),
                  (uhdm::Any*)parent, true /*mute for now*/, true);
            }
          }
        } else if (const uhdm::Variables* var = lvariable) {
          if (var->getUhdmType() == uhdm::UhdmType::HierPath) {
            PathId parentFileId =
                fileSystem->toPathId(parent->getFile(), symbols);
            bool invalidValue = false;
            indexTypespec = (uhdm::Typespec*)m_helper.decodeHierPath(
                (uhdm::HierPath*)var, invalidValue, mod, m_compileDesign,
                Reduce::Yes, nullptr, parentFileId, parent->getStartLine(),
                (uhdm::Any*)parent, true /*mute for now*/, true);
          } else if (var->getUhdmType() == uhdm::UhdmType::RefVar) {
            bool invalidValue = false;
            uhdm::HierPath* path = s.make<uhdm::HierPath>();
            uhdm::AnyCollection* elems = path->getPathElems(true);
            uhdm::RefObj* ref = s.make<uhdm::RefObj>();
            elems->emplace_back(ref);
            ref->setName(var->getName());
            path->setFullName(var->getName());
            PathId parentFileId =
                fileSystem->toPathId(parent->getFile(), symbols);
            indexTypespec = (uhdm::Typespec*)m_helper.decodeHierPath(
                path, invalidValue, mod, m_compileDesign, Reduce::Yes, nullptr,
                parentFileId, parent->getStartLine(), (uhdm::Any*)parent,
                true /*mute for now*/, true);
          }
        }
        uhdm::Variables* swapVar = nullptr;
        if (indexTypespec) {
          swapVar = m_helper.getSimpleVarFromTypespec(
              nullptr, InvalidNodeId, InvalidNodeId,
              (uhdm::Typespec*)indexTypespec, nullptr, m_compileDesign);
        } else {
          uhdm::IntVar* ivar = s.make<uhdm::IntVar>();
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setActual(s.make<uhdm::IntTypespec>());
          rt->setParent(ivar);
          ivar->setTypespec(rt);
          swapVar = ivar;
        }
        if (swapVar) {
          swapVar->setName(ref->getName());
          swapVar->setParent(const_cast<uhdm::Any*>(ref->getParent()));
          swapVar->setFile(ref->getFile());
          swapVar->setStartLine(ref->getStartLine());
          swapVar->setStartColumn(ref->getStartColumn());
          swapVar->setEndLine(ref->getEndLine());
          swapVar->setEndColumn(ref->getEndColumn());
          tmp = swapVar;
        }
      }
    }
  }
  return tmp;
}

void UhdmWriter::bind(uhdm::Serializer& s,
                      const std::vector<vpiHandle>& designs) {
  CommandLineParser* commandLineParser = m_session->getCommandLineParser();
  if (ObjectBinder* const listener = new ObjectBinder(
          m_session, m_componentMap, s, commandLineParser->muteStdout())) {
    for (auto h : designs) {
      const uhdm::Design* const d =
          static_cast<const uhdm::Design*>(((const uhdm_handle*)h)->object);
      listener->bind(d, true);
    }
    delete listener;
  }
}

bool UhdmWriter::writeElabModule(Serializer& s, ModuleInstance* instance,
                                 uhdm::Module* m, ExprBuilder& exprBuilder) {
  Netlist* netlist = instance->getNetlist();
  if (netlist == nullptr) return true;
  m->setPorts(netlist->ports());
  DesignComponent* mod = instance->getDefinition();
  if (mod) {
    // Let decls
    if (!mod->getLetStmts().empty()) {
      uhdm::LetDeclCollection* decls = m->getLetDecls(true);
      for (auto stmt : mod->getLetStmts()) {
        decls->emplace_back((uhdm::LetDecl*)stmt.second->getDecl());
      }
    }
    if (!mod->getPropertyDecls().empty()) {
      uhdm::PropertyDeclCollection* decls = m->getPropertyDecls(true);
      for (auto decl : mod->getPropertyDecls()) {
        decl->setParent(m);
        decls->emplace_back(decl);
      }
    }
    // Typepecs
    uhdm::TypespecCollection* typespecs = m->getTypespecs(true);
    writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, false);
    writeImportedSymbols(mod, s, typespecs);
    // System elab tasks
    m->setSysTaskCalls((std::vector<uhdm::TFCall*>*)&mod->getElabSysCalls());
    if (m->getSysTaskCalls()) {
      for (auto et : *m->getSysTaskCalls()) {
        et->setParent(m);
      }
    }
    // Assertions
    if (mod->getAssertions()) {
      m->setAssertions(mod->getAssertions());
      for (auto ps : *m->getAssertions()) {
        ps->setParent(m);
      }
    }
  }

  writeElabParameters(s, instance, m, exprBuilder);
  if (netlist) {
    if (netlist->ports()) {
      for (auto obj : *netlist->ports()) {
        obj->setParent(m);
      }
    }
    m->setNets(netlist->nets());
    if (netlist->nets()) {
      for (auto obj : *netlist->nets()) {
        obj->setParent(m);
      }
    }
    m->setGenScopeArrays(netlist->gen_scopes());
    if (netlist->gen_scopes()) {
      for (auto obj : *netlist->gen_scopes()) {
        obj->setParent(m);
      }
    }
    m->setVariables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->setParent(m);
      }
    }
    m->setRegArrays(netlist->array_vars());
    if (netlist->array_vars()) {
      for (auto obj : *netlist->array_vars()) {
        obj->setParent(m);
      }
    }
    m->setNamedEvents(netlist->named_events());
    if (netlist->named_events()) {
      for (auto obj : *netlist->named_events()) {
        obj->setParent(m);
      }
    }
    m->setArrayNets(netlist->array_nets());
    if (netlist->array_nets()) {
      for (auto obj : *netlist->array_nets()) {
        obj->setParent(m);
      }
    }

    if (netlist->cont_assigns()) {
      std::vector<uhdm::ContAssign*>* assigns = m->getContAssigns(true);
      writeContAssign(netlist, s, mod, m, assigns);
    }

    // Processes
    m->setProcesses(netlist->process_stmts());
  }

  if (mod) {
    // ClockingBlocks
    ModuleDefinition* def = (ModuleDefinition*)mod;
    for (const auto& ctupple : def->getClockingBlockMap()) {
      const ClockingBlock& cblock = ctupple.second;
      uhdm::ElaboratorContext elaboratorContext(&s, false, true);
      uhdm::ClockingBlock* cb = (uhdm::ClockingBlock*)uhdm::clone_tree(
          cblock.getActual(), &elaboratorContext);
      cb->setParent(m);
      switch (cblock.getType()) {
        case ClockingBlock::Type::Default: {
          m->setDefaultClocking(cb);
          break;
        }
        case ClockingBlock::Type::Global: {
          m->setGlobalClocking(cb);
          break;
        }
        default:
          break;
      }
    }
  }

  if (mod) {
    if (auto from = mod->getTaskFuncs()) {
      uhdm::TaskFuncCollection* target = m->getTaskFuncs(true);
      for (auto tf : *from) {
        target->emplace_back(tf);
        if (tf->getParent() == nullptr) tf->setParent(m);
        if (tf->getInstance() == nullptr) tf->setInstance(m);
      }
    }
  }
  return true;
}

bool UhdmWriter::writeElabInterface(Serializer& s, ModuleInstance* instance,
                                    uhdm::Interface* m,
                                    ExprBuilder& exprBuilder) {
  Netlist* netlist = instance->getNetlist();
  DesignComponent* mod = instance->getDefinition();
  if (mod) {
    // Let decls
    if (!mod->getLetStmts().empty()) {
      uhdm::LetDeclCollection* decls = m->getLetDecls(true);
      for (auto stmt : mod->getLetStmts()) {
        decls->emplace_back((uhdm::LetDecl*)stmt.second->getDecl());
      }
    }
    if (!mod->getPropertyDecls().empty()) {
      uhdm::PropertyDeclCollection* decls = m->getPropertyDecls(true);
      for (auto decl : mod->getPropertyDecls()) {
        decl->setParent(m);
        decls->emplace_back(decl);
      }
    }
    // Typepecs
    uhdm::TypespecCollection* typespecs = m->getTypespecs(true);
    writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, false);
    writeImportedSymbols(mod, s, typespecs);
    // System elab tasks
    m->setSysTaskCalls((std::vector<uhdm::TFCall*>*)&mod->getElabSysCalls());
    if (m->getSysTaskCalls()) {
      for (auto et : *m->getSysTaskCalls()) {
        et->setParent(m);
      }
    }
    // Assertions
    if (mod->getAssertions()) {
      m->setAssertions(mod->getAssertions());
      for (auto ps : *m->getAssertions()) {
        ps->setParent(m);
      }
    }
  }

  writeElabParameters(s, instance, m, exprBuilder);
  if (netlist) {
    m->setPorts(netlist->ports());
    if (netlist->ports()) {
      for (auto obj : *netlist->ports()) {
        obj->setParent(m);
      }
    }
    m->setNets(netlist->nets());
    if (netlist->nets()) {
      for (auto obj : *netlist->nets()) {
        obj->setParent(m);
      }
    }
    m->setGenScopeArrays(netlist->gen_scopes());
    if (netlist->gen_scopes()) {
      for (auto obj : *netlist->gen_scopes()) {
        obj->setParent(m);
      }
    }
    m->setVariables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->setParent(m);
      }
    }
    m->setRegArrays(netlist->array_vars());
    if (netlist->array_vars()) {
      for (auto obj : *netlist->array_vars()) {
        obj->setParent(m);
      }
    }
    m->setNamedEvents(netlist->named_events());
    if (netlist->named_events()) {
      for (auto obj : *netlist->named_events()) {
        obj->setParent(m);
      }
    }
    m->setArrayNets(netlist->array_nets());
    if (netlist->array_nets()) {
      for (auto obj : *netlist->array_nets()) {
        obj->setParent(m);
      }
    }
  }

  if (netlist) {
    if (netlist->cont_assigns()) {
      std::vector<uhdm::ContAssign*>* assigns = m->getContAssigns(true);
      writeContAssign(netlist, s, mod, m, assigns);
    }

    // Processes
    m->setProcesses(netlist->process_stmts());
  }

  // Modports
  ModuleDefinition* module = (ModuleDefinition*)mod;
  ModuleDefinition::ModportSignalMap& orig_modports =
      module->getModportSignalMap();
  for (auto& orig_modport : orig_modports) {
    uhdm::Modport* dest_modport = s.make<uhdm::Modport>();
    dest_modport->setInterface(m);
    dest_modport->setName(orig_modport.first);
    dest_modport->setParent(m);
    const FileContent* orig_fC = orig_modport.second.getFileContent();
    const NodeId orig_nodeId = orig_modport.second.getNodeId();
    orig_fC->populateCoreMembers(orig_nodeId, orig_nodeId, dest_modport);
    uhdm::IODeclCollection* ios = dest_modport->getIODecls(true);
    for (auto& sig : orig_modport.second.getPorts()) {
      const FileContent* fC = sig.getFileContent();
      uhdm::IODecl* io = s.make<uhdm::IODecl>();
      io->setName(sig.getName());
      NodeId id = sig.getNodeId();
      fC->populateCoreMembers(id, id, io);
      if (NodeId Expression = fC->Sibling(id)) {
        m_helper.checkForLoops(true);
        uhdm::Any* exp =
            m_helper.compileExpression(mod, fC, Expression, m_compileDesign,
                                       Reduce::Yes, io, instance, true);
        m_helper.checkForLoops(false);
        io->setExpr(exp);
      }
      uint32_t direction = UhdmWriter::getVpiDirection(sig.getDirection());
      io->setDirection(direction);
      io->setParent(dest_modport);
      ios->emplace_back(io);
    }
  }

  if (mod) {
    // ClockingBlocks
    ModuleDefinition* def = (ModuleDefinition*)mod;
    for (const auto& ctupple : def->getClockingBlockMap()) {
      const ClockingBlock& cblock = ctupple.second;
      uhdm::ElaboratorContext elaboratorContext(&s, false, true);
      uhdm::ClockingBlock* cb = (uhdm::ClockingBlock*)uhdm::clone_tree(
          cblock.getActual(), &elaboratorContext);
      cb->setParent(m);
      switch (cblock.getType()) {
        case ClockingBlock::Type::Default: {
          m->setDefaultClocking(cb);
          break;
        }
        case ClockingBlock::Type::Global: {
          m->setGlobalClocking(cb);
          break;
        }
        default:
          break;
      }
    }
  }

  if (mod) {
    if (auto from = mod->getTaskFuncs()) {
      uhdm::TaskFuncCollection* target = m->getTaskFuncs(true);
      for (auto tf : *from) {
        target->emplace_back(tf);
        if (tf->getParent() == nullptr) tf->setParent(m);
        if (tf->getInstance() == nullptr) tf->setInstance(m);
      }
    }
  }
  return true;
}

void writePrimTerms(ModuleInstance* instance, uhdm::Primitive* prim,
                    int32_t vpiGateType, uhdm::Serializer& s) {
  Netlist* netlist = instance->getNetlist();
  if (uhdm::PortCollection* ports = netlist->ports()) {
    uhdm::PrimTermCollection* terms = prim->getPrimTerms(true);
    uint32_t index = 0;
    for (auto port : *ports) {
      uhdm::PrimTerm* term = s.make<uhdm::PrimTerm>();
      terms->emplace_back(term);
      uhdm::Expr* hconn = (uhdm::Expr*)port->getHighConn();
      hconn->setParent(prim);
      term->setExpr(hconn);
      term->setFile(port->getFile());
      term->setStartLine(port->getStartLine());
      term->setStartColumn(port->getStartColumn());
      term->setEndLine(port->getEndLine());
      term->setEndColumn(port->getEndColumn());
      term->setDirection(port->getDirection());
      term->setParent(prim);
      term->setTermIndex(index);
      if (vpiGateType == vpiBufPrim || vpiGateType == vpiNotPrim) {
        if (index < ports->size() - 1) {
          term->setDirection(vpiOutput);
        } else {
          term->setDirection(vpiInput);
        }
      } else if (vpiGateType == vpiTranif1Prim ||
                 vpiGateType == vpiTranif0Prim ||
                 vpiGateType == vpiRtranif1Prim ||
                 vpiGateType == vpiRtranif0Prim || vpiGateType == vpiTranPrim ||
                 vpiGateType == vpiRtranPrim) {
        if (index < ports->size() - 1) {
          term->setDirection(vpiInout);
        } else {
          term->setDirection(vpiInput);
        }
      } else {
        if (index == 0) {
          term->setDirection(vpiOutput);
        } else {
          term->setDirection(vpiInput);
        }
      }
      index++;
    }
  }
}

void UhdmWriter::writeInstance(ModuleDefinition* mod, ModuleInstance* instance,
                               uhdm::Any* m, CompileDesign* compileDesign,
                               ModportMap& modPortMap,
                               ModuleInstanceMap& moduleInstanceMap,
                               ExprBuilder& exprBuilder) {
  Compiler* const compiler = m_compileDesign->getCompiler();
  FileSystem* const fileSystem = m_session->getFileSystem();
  uhdm::Serializer& s = compileDesign->getSerializer();
  uhdm::ModuleCollection* subModules = nullptr;
  uhdm::ProgramCollection* subPrograms = nullptr;
  uhdm::InterfaceCollection* subInterfaces = nullptr;
  uhdm::PrimitiveCollection* subPrimitives = nullptr;
  uhdm::PrimitiveArrayCollection* subPrimitiveArrays = nullptr;
  uhdm::GenScopeArrayCollection* subGenScopeArrays = nullptr;
  m_componentMap.emplace(instance, m);
  if (m->getUhdmType() == uhdm::UhdmType::Module) {
    writeElabModule(s, instance, (uhdm::Module*)m, exprBuilder);
  } else if (m->getUhdmType() == uhdm::UhdmType::GenScope) {
    writeElabGenScope(s, instance, (uhdm::GenScope*)m, exprBuilder);
  } else if (m->getUhdmType() == uhdm::UhdmType::Interface) {
    writeElabInterface(s, instance, (uhdm::Interface*)m, exprBuilder);
  }
  Netlist* netlist = instance->getNetlist();
  if (netlist) {
    if (uhdm::InterfaceArrayCollection* subInterfaceArrays =
            netlist->interface_arrays()) {
      uhdm::UhdmType utype = m->getUhdmType();
      if (utype == uhdm::UhdmType::Module) {
        ((uhdm::Module*)m)->setInterfaceArrays(subInterfaceArrays);
        for (uhdm::InterfaceArray* array : *subInterfaceArrays) {
          array->setParent(m);
        }
      } else if (utype == uhdm::UhdmType::GenScope) {
        ((uhdm::GenScope*)m)->setInterfaceArrays(subInterfaceArrays);
        for (uhdm::InterfaceArray* array : *subInterfaceArrays) {
          array->setParent(m);
        }
      } else if (utype == uhdm::UhdmType::Interface) {
        ((uhdm::Interface*)m)->setInterfaceArrays(subInterfaceArrays);
        for (uhdm::InterfaceArray* array : *subInterfaceArrays) {
          array->setParent(m);
        }
      }
    }
    if (uhdm::InterfaceCollection* subInterfaces = netlist->interfaces()) {
      uhdm::UhdmType utype = m->getUhdmType();
      if (utype == uhdm::UhdmType::Module) {
        ((uhdm::Module*)m)->setInterfaces(subInterfaces);
        for (uhdm::Interface* interf : *subInterfaces) {
          interf->setParent(m);
        }
      } else if (utype == uhdm::UhdmType::GenScope) {
        ((uhdm::GenScope*)m)->setInterfaces(subInterfaces);
        for (uhdm::Interface* interf : *subInterfaces) {
          interf->setParent(m);
        }
      } else if (utype == uhdm::UhdmType::Interface) {
        ((uhdm::Interface*)m)->setInterfaces(subInterfaces);
        for (uhdm::Interface* interf : *subInterfaces) {
          interf->setParent(m);
        }
      }
    }
  }
  std::map<ModuleInstance*, uhdm::Module*> tempInstanceMap;
  for (uint32_t i = 0; i < instance->getNbChildren(); i++) {
    ModuleInstance* child = instance->getChildren(i);
    DesignComponent* childDef = child->getDefinition();
    if (ModuleDefinition* mm =
            valuedcomponenti_cast<ModuleDefinition>(childDef)) {
      VObjectType insttype = child->getType();
      if (insttype == VObjectType::paModule_instantiation) {
        if (subModules == nullptr)
          subModules = s.makeCollection<uhdm::Module>();
        uhdm::Module* sm = s.make<uhdm::Module>();
        tempInstanceMap.emplace(child, sm);
        moduleInstanceMap.emplace(child, sm);
        if (childDef && !childDef->getFileContents().empty() &&
            compiler->isLibraryFile(
                childDef->getFileContents()[0]->getFileId())) {
          sm->setCellInstance(true);
        }
        sm->setName(child->getInstanceName());
        sm->setDefName(child->getModuleName());
        sm->setFullName(child->getFullPathName());
        const FileContent* defFile = mm->getFileContents()[0];
        sm->setDefFile(fileSystem->toPath(defFile->getFileId()));
        sm->setDefLineNo(defFile->Line(mm->getNodeIds()[0]));
        child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                     child->getNodeId(), sm);
        subModules->emplace_back(sm);
        if (m->getUhdmType() == uhdm::UhdmType::Module) {
          ((uhdm::Module*)m)->setModules(subModules);
          sm->setInstance((uhdm::Module*)m);
          sm->setModule((uhdm::Module*)m);
          sm->setParent(m);
        } else if (m->getUhdmType() == uhdm::UhdmType::GenScope) {
          ((uhdm::GenScope*)m)->setModules(subModules);
          sm->setParent(m);
        }
        writeInstance(mm, child, sm, compileDesign, modPortMap,
                      moduleInstanceMap, exprBuilder);
      } else if (insttype == VObjectType::paConditional_generate_construct ||
                 insttype == VObjectType::paLoop_generate_construct ||
                 insttype == VObjectType::paGenerate_begin_end_block ||
                 insttype == VObjectType::paGenerate_item ||
                 insttype == VObjectType::paGenerate_region ||
                 insttype == VObjectType::paGenerate_module_loop_statement ||
                 insttype ==
                     VObjectType::paGenerate_module_conditional_statement ||
                 insttype == VObjectType::paGenerate_module_block ||
                 insttype == VObjectType::paGenerate_module_item ||
                 insttype == VObjectType::paGenerate_module_named_block ||
                 insttype == VObjectType::paGenerate_module_block ||
                 insttype == VObjectType::paGenerate_module_item ||
                 insttype == VObjectType::paGenerate_interface_loop_statement ||
                 insttype ==
                     VObjectType::paGenerate_interface_conditional_statement ||
                 insttype == VObjectType::paGenerate_interface_block ||
                 insttype == VObjectType::paGenerate_interface_item ||
                 insttype == VObjectType::paGenerate_interface_named_block ||
                 insttype == VObjectType::paGenerate_interface_block ||
                 insttype == VObjectType::paGenerate_interface_item) {
        if (subGenScopeArrays == nullptr)
          subGenScopeArrays = s.makeCollection<uhdm::GenScopeArray>();
        uhdm::GenScopeArray* sm = s.make<uhdm::GenScopeArray>();
        sm->setName(child->getInstanceName());
        sm->setFullName(child->getFullPathName());
        child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                     child->getNodeId(), sm);
        subGenScopeArrays->emplace_back(sm);
        uhdm::GenScope* a_gen_scope = s.make<uhdm::GenScope>();
        sm->getGenScopes(true)->emplace_back(a_gen_scope);
        child->getFileContent()->populateCoreMembers(
            child->getNodeId(), child->getNodeId(), a_gen_scope);
        a_gen_scope->setParent(sm);
        uhdm::UhdmType utype = m->getUhdmType();
        if (utype == uhdm::UhdmType::Module) {
          ((uhdm::Module*)m)->setGenScopeArrays(subGenScopeArrays);
          sm->setParent(m);
        } else if (utype == uhdm::UhdmType::GenScope) {
          ((uhdm::GenScope*)m)->setGenScopeArrays(subGenScopeArrays);
          sm->setParent(m);
        } else if (utype == uhdm::UhdmType::Interface) {
          ((uhdm::Interface*)m)->setGenScopeArrays(subGenScopeArrays);
          sm->setParent(m);
        }
        writeInstance(mm, child, a_gen_scope, compileDesign, modPortMap,
                      moduleInstanceMap, exprBuilder);

      } else if (insttype == VObjectType::paInterface_instantiation) {
        if (subInterfaces == nullptr)
          subInterfaces = s.makeCollection<uhdm::Interface>();
        uhdm::Interface* sm = s.make<uhdm::Interface>();
        sm->setName(child->getInstanceName());
        sm->setDefName(child->getModuleName());
        sm->setFullName(child->getFullPathName());
        child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                     child->getNodeId(), sm);
        const FileContent* defFile = mm->getFileContents()[0];
        sm->setDefFile(fileSystem->toPath(defFile->getFileId()));
        sm->setDefLineNo(defFile->Line(mm->getNodeIds()[0]));
        subInterfaces->emplace_back(sm);
        uhdm::UhdmType utype = m->getUhdmType();
        if (utype == uhdm::UhdmType::Module) {
          ((uhdm::Module*)m)->setInterfaces(subInterfaces);
          sm->setInstance((uhdm::Module*)m);
          sm->setParent(m);
        } else if (utype == uhdm::UhdmType::GenScope) {
          ((uhdm::GenScope*)m)->setInterfaces(subInterfaces);
          sm->setParent(m);
        } else if (utype == uhdm::UhdmType::Interface) {
          ((uhdm::Interface*)m)->setInterfaces(subInterfaces);
          sm->setParent(m);
        }
        writeInstance(mm, child, sm, compileDesign, modPortMap,
                      moduleInstanceMap, exprBuilder);

      } else if ((insttype == VObjectType::paUdp_instantiation) ||
                 (insttype == VObjectType::paCmos_switch_instance) ||
                 (insttype == VObjectType::paEnable_gate_instance) ||
                 (insttype == VObjectType::paMos_switch_instance) ||
                 (insttype == VObjectType::paN_input_gate_instance) ||
                 (insttype == VObjectType::paN_output_gate_instance) ||
                 (insttype == VObjectType::paPass_enable_switch_instance) ||
                 (insttype == VObjectType::paPass_switch_instance) ||
                 (insttype == VObjectType::paPull_gate_instance)) {
        uhdm::Primitive* gate = nullptr;
        uhdm::PrimitiveArray* gate_array = nullptr;
        const FileContent* fC = child->getFileContent();
        NodeId gatenode = fC->Child(fC->Parent(child->getNodeId()));
        VObjectType gatetype = fC->Type(gatenode);
        int32_t vpiGateType = m_helper.getBuiltinType(gatetype);
        if (insttype == VObjectType::paUdp_instantiation) {
          uhdm::Udp* udp = s.make<uhdm::Udp>();
          gate = udp;
          if (ModuleDefinition* mm =
                  valuedcomponenti_cast<ModuleDefinition>(childDef)) {
            udp->setUdpDefn(mm->getUhdmModel<uhdm::UdpDefn>());
          }
          if (uhdm::RangeCollection* ranges = child->getNetlist()->ranges()) {
            gate_array = s.make<uhdm::UdpArray>();
            uhdm::PrimitiveCollection* prims = gate_array->getPrimitives(true);
            gate_array->setRanges(ranges);
            gate_array->setParent(m);
            prims->emplace_back(gate);
            gate->setParent(gate_array);
            for (auto r : *ranges) r->setParent(gate_array);
            if (subPrimitiveArrays == nullptr)
              subPrimitiveArrays = s.makeCollection<uhdm::PrimitiveArray>();
            subPrimitiveArrays->emplace_back(gate_array);
          } else {
            if (subPrimitives == nullptr)
              subPrimitives = s.makeCollection<uhdm::Primitive>();
            subPrimitives->emplace_back(gate);
          }
        } else if (vpiGateType == vpiPmosPrim || vpiGateType == vpiRpmosPrim ||
                   vpiGateType == vpiNmosPrim || vpiGateType == vpiRnmosPrim ||
                   vpiGateType == vpiCmosPrim || vpiGateType == vpiRcmosPrim ||
                   vpiGateType == vpiTranif1Prim ||
                   vpiGateType == vpiTranif0Prim ||
                   vpiGateType == vpiRtranif1Prim ||
                   vpiGateType == vpiRtranif0Prim ||
                   vpiGateType == vpiTranPrim || vpiGateType == vpiRtranPrim) {
          gate = s.make<uhdm::SwitchTran>();
          if (uhdm::RangeCollection* ranges = child->getNetlist()->ranges()) {
            gate_array = s.make<uhdm::SwitchArray>();
            uhdm::PrimitiveCollection* prims = gate_array->getPrimitives(true);
            gate_array->setRanges(ranges);
            gate_array->setParent(m);
            prims->emplace_back(gate);
            gate->setParent(gate_array);
            for (auto r : *ranges) r->setParent(gate_array);
            if (subPrimitiveArrays == nullptr)
              subPrimitiveArrays = s.makeCollection<uhdm::PrimitiveArray>();
            subPrimitiveArrays->emplace_back(gate_array);
          } else {
            if (subPrimitives == nullptr)
              subPrimitives = s.makeCollection<uhdm::Primitive>();
            subPrimitives->emplace_back(gate);
          }
          gate->setPrimType(vpiGateType);
        } else {
          gate = s.make<uhdm::Gate>();
          if (uhdm::RangeCollection* ranges = child->getNetlist()->ranges()) {
            gate_array = s.make<uhdm::GateArray>();
            gate_array->setName(child->getInstanceName());
            gate_array->setFullName(child->getFullPathName());
            child->getFileContent()->populateCoreMembers(
                child->getNodeId(), child->getNodeId(), gate_array);
            uhdm::PrimitiveCollection* prims = gate_array->getPrimitives(true);
            gate_array->setRanges(ranges);
            gate_array->setParent(m);
            prims->emplace_back(gate);
            gate->setParent(gate_array);
            for (auto r : *ranges) r->setParent(gate_array);
            if (subPrimitiveArrays == nullptr)
              subPrimitiveArrays = s.makeCollection<uhdm::PrimitiveArray>();
            subPrimitiveArrays->emplace_back(gate_array);
          } else {
            if (subPrimitives == nullptr)
              subPrimitives = s.makeCollection<uhdm::Primitive>();
            subPrimitives->emplace_back(gate);
          }
          gate->setPrimType(vpiGateType);
        }
        if (uhdm::ExprCollection* delays = child->getNetlist()->delays()) {
          if (delays->size() == 1) {
            gate->setDelay((*delays)[0]);
          }
        }

        gate->setName(child->getInstanceName());
        gate->setDefName(child->getModuleName());
        gate->setFullName(child->getFullPathName());
        child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                     child->getNodeId(), gate);
        uhdm::UhdmType utype = m->getUhdmType();
        if (utype == uhdm::UhdmType::Module) {
          ((uhdm::Module*)m)->setPrimitives(subPrimitives);
          ((uhdm::Module*)m)->setPrimitiveArrays(subPrimitiveArrays);
          gate->setParent(m);
        } else if (utype == uhdm::UhdmType::GenScope) {
          ((uhdm::GenScope*)m)->setPrimitives(subPrimitives);
          ((uhdm::GenScope*)m)->setPrimitiveArrays(subPrimitiveArrays);
          gate->setParent(m);
        }
        writePrimTerms(child, gate, vpiGateType, s);
      } else {
        // Unknown object type
      }
    } else if (Program* prog = valuedcomponenti_cast<Program>(childDef)) {
      if (subPrograms == nullptr)
        subPrograms = s.makeCollection<uhdm::Program>();
      uhdm::Program* sm = prog->getUhdmModel<uhdm::Program>();
      sm->setName(child->getInstanceName());
      sm->setDefName(child->getModuleName());
      sm->setFullName(child->getFullPathName());
      child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                   child->getNodeId(), sm);
      const FileContent* defFile = prog->getFileContents()[0];
      sm->setDefFile(fileSystem->toPath(defFile->getFileId()));
      sm->setDefLineNo(defFile->Line(prog->getNodeIds()[0]));
      subPrograms->emplace_back(sm);
      uhdm::UhdmType utype = m->getUhdmType();
      if (utype == uhdm::UhdmType::Module) {
        ((uhdm::Module*)m)->setPrograms(subPrograms);
        sm->setInstance((uhdm::Module*)m);
        sm->setParent(m);
      } else if (utype == uhdm::UhdmType::GenScope) {
        ((uhdm::GenScope*)m)->setPrograms(subPrograms);
        sm->setParent(m);
      }
      writeElabProgram(s, child, sm, modPortMap);
    } else {
      // Undefined module
      if (subModules == nullptr) subModules = s.makeCollection<uhdm::Module>();
      uhdm::Module* sm = s.make<uhdm::Module>();
      sm->setName(child->getInstanceName());
      sm->setDefName(child->getModuleName());
      sm->setFullName(child->getFullPathName());
      child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                   child->getNodeId(), sm);
      subModules->emplace_back(sm);
      uhdm::UhdmType utype = m->getUhdmType();
      if (utype == uhdm::UhdmType::Module) {
        ((uhdm::Module*)m)->setModules(subModules);
        sm->setInstance((uhdm::Module*)m);
        sm->setModule((uhdm::Module*)m);
        sm->setParent(m);
      } else if (utype == uhdm::UhdmType::GenScope) {
        ((uhdm::GenScope*)m)->setModules(subModules);
        sm->setParent(m);
      }
      writeInstance(mm, child, sm, compileDesign, modPortMap, moduleInstanceMap,
                    exprBuilder);
    }
  }

  if (m->getUhdmType() == uhdm::UhdmType::Module) {
    const auto& moduleArrayModuleInstancesMap =
        instance->getModuleArrayModuleInstancesMap();
    if (!moduleArrayModuleInstancesMap.empty()) {
      ((uhdm::Module*)m)
          ->setModuleArrays(s.makeCollection<uhdm::ModuleArray>());
      std::vector<uhdm::ModuleArray*> moduleArrays;
      std::transform(
          moduleArrayModuleInstancesMap.begin(),
          moduleArrayModuleInstancesMap.end(), std::back_inserter(moduleArrays),
          [](ModuleInstance::ModuleArrayModuleInstancesMap::const_reference
                 pair) { return pair.first; });
      std::sort(moduleArrays.begin(), moduleArrays.end(),
                [](const uhdm::ModuleArray* lhs, const uhdm::ModuleArray* rhs) {
                  return lhs->getUhdmId() < rhs->getUhdmId();
                });
      for (uhdm::ModuleArray* modArray : moduleArrays) {
        const auto& modInstances =
            moduleArrayModuleInstancesMap.find(modArray)->second;
        if (!modInstances.empty()) {
          modArray->setParent(m);
          ((uhdm::Module*)m)->getModuleArrays()->emplace_back(modArray);
          for (ModuleInstance* modInst : modInstances) {
            auto it = tempInstanceMap.find(modInst);
            if (it != tempInstanceMap.end()) {
              modArray->getModules(true)->emplace_back(it->second);
            }
          }
        }
      }
    }
  }
}

class AlwaysWithForLoop : public VpiListener {
 public:
  explicit AlwaysWithForLoop() {}
  ~AlwaysWithForLoop() override = default;
  void leaveForStmt(const uhdm::ForStmt* object, vpiHandle handle) override {
    containtsForStmt = true;
  }
  bool containtsForStmt = false;
};

bool alwaysContainsForLoop(Serializer& serializer, uhdm::Any* root) {
  AlwaysWithForLoop* listener = new AlwaysWithForLoop();
  vpiHandle handle = serializer.makeUhdmHandle(root->getUhdmType(), root);
  listener->listenAny(handle);
  vpi_release_handle(handle);
  bool result = listener->containtsForStmt;
  delete listener;
  return result;
}

// synlig has a major problem processing always blocks.
// They are processed mainly in the allModules section which is incorrect in
// some case. They should be processed from the topModules section. Here we try
// to fix temporarily this by filtering out the always blocks containing
// for-loops from the allModules, and those without from the topModules
void filterAlwaysBlocks(Serializer& s, uhdm::Design* d) {
  if (d->getAllModules()) {
    for (auto module : *d->getAllModules()) {
      if (module->getProcesses()) {
        bool more = true;
        while (more) {
          more = false;
          for (std::vector<uhdm::Process*>::iterator itr =
                   module->getProcesses()->begin();
               itr != module->getProcesses()->end(); itr++) {
            if ((*itr)->getUhdmType() == uhdm::UhdmType::Always) {
              if (alwaysContainsForLoop(s, (*itr))) {
                more = true;
                module->getProcesses()->erase(itr);
                break;
              }
            }
          }
        }
      }
    }
  }
  std::queue<uhdm::Scope*> instances;
  if (d->getTopModules()) {
    for (auto mod : *d->getTopModules()) {
      instances.push(mod);
    }
  }
  while (!instances.empty()) {
    uhdm::Scope* current = instances.front();
    instances.pop();
    if (current->getUhdmType() == uhdm::UhdmType::Module) {
      uhdm::Module* mod = (uhdm::Module*)current;
      if (mod->getProcesses()) {
        bool more = true;
        while (more) {
          more = false;
          for (std::vector<uhdm::Process*>::iterator itr =
                   mod->getProcesses()->begin();
               itr != mod->getProcesses()->end(); itr++) {
            if ((*itr)->getUhdmType() == uhdm::UhdmType::Always) {
              if (!alwaysContainsForLoop(s, (*itr))) {
                more = true;
                mod->getProcesses()->erase(itr);
                break;
              }
            }
          }
        }
      }
      if (mod->getModules()) {
        for (auto m : *mod->getModules()) {
          instances.push(m);
        }
      }
      if (mod->getGenScopeArrays()) {
        for (auto m : *mod->getGenScopeArrays()) {
          instances.push(m->getGenScopes()->at(0));
        }
      }
    } else if (current->getUhdmType() == uhdm::UhdmType::GenScope) {
      uhdm::GenScope* sc = (uhdm::GenScope*)current;
      if (sc->getModules()) {
        for (auto m : *sc->getModules()) {
          instances.push(m);
        }
      }
      if (sc->getGenScopeArrays()) {
        for (auto m : *sc->getGenScopeArrays()) {
          instances.push(m->getGenScopes()->at(0));
        }
      }
    }
  }
}

bool UhdmWriter::write(PathId uhdmFileId) {
  Compiler* const compiler = m_compileDesign->getCompiler();
  FileSystem* const fileSystem = m_session->getFileSystem();
  SymbolTable* const symbols = m_session->getSymbolTable();
  ErrorContainer* const errors = m_session->getErrorContainer();
  CommandLineParser* const clp = m_session->getCommandLineParser();
  ModportMap modPortMap;
  InstanceDefinitionMap instanceDefinitionMap;
  ModuleInstanceMap moduleInstanceMap;
  uhdm::Serializer& s = m_compileDesign->getSerializer();
  ExprBuilder exprBuilder(m_session);

  Location loc(uhdmFileId);
  Error err(ErrorDefinition::UHDM_CREATING_MODEL, loc);
  errors->addError(err);
  errors->printMessages(clp->muteStdout());

  m_helper.setElaborate(Elaborate::No);
  m_helper.setReduce(Reduce::No);

  // Compute list of design components that are part of the instance tree
  std::set<DesignComponent*> designComponents;
  {
    std::queue<ModuleInstance*> queue;
    for (const auto& pack : m_design->getPackageDefinitions()) {
      if (!pack.second->getFileContents().empty()) {
        if (pack.second->getFileContents()[0] != nullptr)
          designComponents.insert(pack.second);
      }
    }
    for (auto instance : m_design->getTopLevelModuleInstances()) {
      queue.push(instance);
    }

    while (!queue.empty()) {
      ModuleInstance* current = queue.front();
      DesignComponent* def = current->getDefinition();
      queue.pop();
      if (current == nullptr) continue;
      for (ModuleInstance* sub : current->getAllSubInstances()) {
        queue.push(sub);
      }
      const FileContent* fC = current->getFileContent();
      if (fC) {
        designComponents.insert(def);
      }
    }
  }

  std::vector<vpiHandle> designs;
  uhdm::Design* d = nullptr;
  if (m_design) {
    d = m_design->getUhdmDesign();
    vpiHandle designHandle =
        reinterpret_cast<vpiHandle>(new uhdm_handle(UhdmType::Design, d));
    std::string designName = "unnamed";
    const auto& topLevelModules = m_design->getTopLevelModuleInstances();
    if (!topLevelModules.empty()) {
      designName = topLevelModules.front()->getModuleName();
    }
    d->setName(designName);
    designs.emplace_back(designHandle);

    // -------------------------------
    // Non-Elaborated Model

    // Packages
    SURELOG::PackageDefinitionVec packages =
        m_design->getOrderedPackageDefinitions();
    for (auto& pack : m_design->getPackageDefinitions()) {
      if (pack.first == "builtin") {
        pack.second->getUhdmModel()->setParent(d);
        if (pack.second) packages.insert(packages.begin(), pack.second);
        break;
      }
    }

    if (clp->elaborate()) {
      m_helper.setElaborate(Elaborate::Yes);
      m_helper.setReduce(Reduce::Yes);

      uhdm::PackageCollection* v2 = d->getTopPackages(true);
      for (Package* pack : packages) {
        if (!pack) continue;
        if (!pack->getFileContents().empty() &&
            pack->getType() == VObjectType::paPackage_declaration) {
          const FileContent* fC = pack->getFileContents()[0];
          uhdm::Package* p = pack->getUhdmModel<uhdm::Package>();
          m_componentMap.emplace(pack, p);
          p->setParent(d);
          p->setTop(true);
          p->setDefName(pack->getName());
          if (pack->getAttributes() != nullptr) {
            p->setAttributes(pack->getAttributes());
            for (auto a : *p->getAttributes()) {
              a->setParent(p);
            }
          }
          writePackage(pack, p, s, true);
          if (fC) {
            // Builtin package has no file
            const NodeId modId = pack->getNodeIds()[0];
            const NodeId startId =
                fC->sl_collect(modId, VObjectType::paPACKAGE);
            fC->populateCoreMembers(startId, modId, p);
          }
          v2->emplace_back(p);
        }
      }
    }

    m_helper.setElaborate(Elaborate::No);
    m_helper.setReduce(Reduce::No);

    for (Package* pack : packages) {
      if (!pack) continue;
      if (!pack->getFileContents().empty() &&
          pack->getType() == VObjectType::paPackage_declaration) {
        const FileContent* fC = pack->getFileContents()[0];
        uhdm::Package* p =
            pack->getUnElabPackage()->getUhdmModel<uhdm::Package>();
        m_componentMap.emplace(pack->getUnElabPackage(), p);
        p->setName(pack->getName());
        p->setParent(d);
        p->setDefName(pack->getName());
        if (pack->getAttributes() != nullptr) {
          p->setAttributes(pack->getAttributes());
          for (auto a : *p->getAttributes()) {
            a->setParent(p);
          }
        }
        writePackage(pack->getUnElabPackage(), p, s, false);
        if (fC) {
          // Builtin package has no file
          const NodeId modId = pack->getNodeIds()[0];
          const NodeId startId = fC->sl_collect(modId, VObjectType::paPACKAGE);
          fC->populateCoreMembers(startId, modId, p);
        }
      }
    }

    // Programs
    const auto& programs = m_design->getProgramDefinitions();
    for (const auto& progNamePair : programs) {
      Program* prog = progNamePair.second;
      if (!prog->getFileContents().empty() &&
          prog->getType() == VObjectType::paProgram_declaration) {
        const FileContent* fC = prog->getFileContents()[0];
        uhdm::Program* p = prog->getUhdmModel<uhdm::Program>();
        m_componentMap.emplace(prog, p);
        instanceDefinitionMap.emplace(prog->getName(), p);
        p->setParent(d);
        p->setDefName(prog->getName());
        const NodeId modId = prog->getNodeIds()[0];
        const NodeId startId = fC->sl_collect(modId, VObjectType::paPROGRAM);
        fC->populateCoreMembers(startId, modId, p);
        if (prog->getAttributes() != nullptr) {
          p->setAttributes(prog->getAttributes());
          for (auto a : *p->getAttributes()) {
            a->setParent(p);
          }
        }
        writeProgram(prog, p, s, modPortMap);
      }
    }

    // Interfaces
    const auto& modules = m_design->getModuleDefinitions();
    for (const auto& modNamePair : modules) {
      ModuleDefinition* mod = modNamePair.second;
      if (mod->getFileContents().empty()) {
        // Built-in primitive
      } else if (mod->getType() == VObjectType::paInterface_declaration) {
        const FileContent* fC = mod->getFileContents()[0];
        uhdm::Interface* m = mod->getUhdmModel<uhdm::Interface>();
        m_componentMap.emplace(mod, m);
        instanceDefinitionMap.emplace(mod->getName(), m);
        m->setParent(d);
        m->setDefName(mod->getName());
        const NodeId modId = mod->getNodeIds()[0];
        const NodeId startId = fC->sl_collect(modId, VObjectType::paINTERFACE);
        fC->populateCoreMembers(startId, modId, m);
        if (mod->getAttributes() != nullptr) {
          m->setAttributes(mod->getAttributes());
          for (auto a : *m->getAttributes()) {
            a->setParent(m);
          }
        }
        writeInterface(mod, m, s, modPortMap);
      }
    }

    // Modules & Udps
    for (const auto& modNamePair : modules) {
      ModuleDefinition* mod = modNamePair.second;
      if (mod->getFileContents().empty()) {
        // Built-in primitive
      } else if (mod->getType() == VObjectType::paModule_declaration) {
        uhdm::Module* m = mod->getUhdmModel<uhdm::Module>();
        if (clp->getElabUhdm() &&
            compiler->isLibraryFile(mod->getFileContents()[0]->getFileId())) {
          m->setCellInstance(true);
          // Don't list library cells unused in the design
          if (mod && (designComponents.find(mod) == designComponents.end()))
            continue;
        }
        m_componentMap.emplace(mod, m);
        std::string_view modName = mod->getName();
        instanceDefinitionMap.emplace(modName, m);
        m->setDefName(modName);
        if (modName.find("::") == std::string_view::npos) {
          m->setParent(d);
        } else {
          modName = StringUtils::rtrim_until(modName, ':');
          modName.remove_suffix(1);
          InstanceDefinitionMap::const_iterator pmodIt =
              instanceDefinitionMap.find(modName);
          if (pmodIt == instanceDefinitionMap.end()) {
            m->setParent(d);
          } else {
            m->setParent(pmodIt->second);
          }
        }
        if (mod->getAttributes() != nullptr) {
          m->setAttributes(mod->getAttributes());
          for (auto a : *m->getAttributes()) {
            a->setParent(m);
          }
        }
        writeModule(mod->getUnelabMmodule(), m, s, instanceDefinitionMap,
                    modPortMap);
      } else if (mod->getType() == VObjectType::paUdp_declaration) {
        const FileContent* fC = mod->getFileContents()[0];
        if (uhdm::UdpDefn* defn = mod->getUhdmModel<uhdm::UdpDefn>()) {
          m_componentMap.emplace(mod, defn);
          defn->setParent(d);
          defn->setDefName(mod->getName());
          const NodeId modId = mod->getNodeIds()[0];
          const NodeId startId =
              fC->sl_collect(modId, VObjectType::paPRIMITIVE);
          fC->populateCoreMembers(startId, modId, defn);
          if (mod->getAttributes() != nullptr) {
            defn->setAttributes(mod->getAttributes());
            for (auto a : *defn->getAttributes()) {
              a->setParent(defn);
            }
          }
        }
      }
    }

    if (uhdm::ModuleCollection* uhdm_modules = d->getAllModules()) {
      for (uhdm::Module* mod : *uhdm_modules) {
        if (mod->getRefModules()) {
          for (auto subMod : *mod->getRefModules()) {
            InstanceDefinitionMap::iterator itr =
                instanceDefinitionMap.find(std::string(subMod->getDefName()));
            if (itr != instanceDefinitionMap.end()) {
              subMod->setActual(itr->second);
            }
          }
        }
      }
    }

    // Classes
    const auto& classes = m_design->getClassDefinitions();
    for (const auto& classNamePair : classes) {
      ClassDefinition* classDef = classNamePair.second;
      if (!classDef->getFileContents().empty() &&
          classDef->getType() == VObjectType::paClass_declaration) {
        uhdm::ClassDefn* c = classDef->getUhdmModel<uhdm::ClassDefn>();
        if (!c->getParent()) {
          writeClass(classDef, s, d);
        }
      }
    }

    // -------------------------------
    // Elaborated Model (Folded)
    if (clp->elaborate()) {
      m_helper.setElaborate(Elaborate::Yes);
      m_helper.setReduce(Reduce::Yes);

      // Top-level modules
      uhdm::ModuleCollection* uhdm_top_modules = d->getTopModules(true);
      for (ModuleInstance* inst : topLevelModules) {
        DesignComponent* component = inst->getDefinition();
        ModuleDefinition* mod =
            valuedcomponenti_cast<ModuleDefinition>(component);
        const auto& itr = m_componentMap.find(mod);
        uhdm::Module* m = s.make<uhdm::Module>();
        m->setTopModule(true);
        m->setTop(true);
        uhdm::Module* def = (uhdm::Module*)itr->second;
        m->setDefName(def->getDefName());
        m->setName(def->getDefName());  // Top's instance name is module name
        m->setFullName(
            def->getDefName());  // Top's full instance name is module name
        m->setFile(def->getFile());
        m->setStartLine(def->getStartLine());
        m->setStartColumn(def->getStartColumn());
        m->setEndLine(def->getEndLine());
        m->setEndColumn(def->getEndColumn());
        writeInstance(mod, inst, m, m_compileDesign, modPortMap,
                      moduleInstanceMap, exprBuilder);
        uhdm_top_modules->emplace_back(m);
      }
    }
  }

  if (clp->getUhdmStats()) {
    s.printStats(std::cerr, "Non-Elaborated Model");
  }

  m_helper.setElaborate(Elaborate::Yes);
  m_helper.setReduce(Reduce::Yes);

  // ----------------------------------
  // Fully elaborated model
  if (clp->getElabUhdm()) {
    Error err(ErrorDefinition::UHDM_ELABORATION, loc);
    errors->addError(err);
    errors->printMessages(clp->muteStdout());

    if (ElaboratorContext* elaboratorContext =
            new uhdm::ElaboratorContext(&s, false, false)) {
      elaboratorContext->m_elaborator.uniquifyTypespec(false);
      elaboratorContext->m_elaborator.listenDesigns(designs);
      delete elaboratorContext;
    }

    bind(s, designs);

    if (clp->getUhdmStats()) {
      s.printStats(std::cerr, "Elaborated Model");
    }

    if (UhdmAdjuster* adjuster = new UhdmAdjuster(&s, d)) {
      adjuster->listenDesigns(designs);
      delete adjuster;
    }
  } else {
    bind(s, designs);
  }

  // if (IntegrityChecker* const checker = new IntegrityChecker(m_session)) {
  //   for (auto h : designs) {
  //     const uhdm::Design* const d =
  //         static_cast<const uhdm::Design*>(((const uhdm_handle*)h)->object);
  //     checker->check(d);
  //   }
  //
  //   delete checker;
  //   errors->printMessages(clp->muteStdout());
  // }

  // ----------------------------------
  // Lint only the elaborated model
  // if (m_session->getCommandLineParser()->getElabUhdm()) {
  //   if (UhdmLint* linter = new UhdmLint(&s, d)) {
  //     linter->listenDesigns(designs);
  //     delete linter;
  //   }
  // }

  // if (clp->getElabUhdm() && clp->reportNonSynthesizable()) {
  //   std::set<const uhdm::Any*> nonSynthesizableObjects;
  //   if (SynthSubset* annotate =
  //           new SynthSubset(&s, nonSynthesizableObjects, d, true,
  //                           clp->reportNonSynthesizableWithFormal())) {
  //     annotate->listenDesigns(designs);
  //     annotate->filterNonSynthesizable();
  //     delete annotate;
  //   }
  // }

  // Purge obsolete typespecs
  for (auto o : m_compileDesign->getSwapedObjects()) {
    const uhdm::Typespec* orig = o.first;
    const uhdm::Typespec* tps = o.second;
    if (tps != orig) s.erase(orig);
  }

  const fs::path uhdmFile = fileSystem->toPlatformAbsPath(uhdmFileId);
  if (clp->writeUhdm()) {
    Error err(ErrorDefinition::UHDM_WRITE_DB, loc);
    errors->addError(err);
    errors->printMessages(clp->muteStdout());
    s.setGCEnabled(clp->gc());
    s.save(uhdmFile);
  }

  // if (clp->getDebugUhdm() || clp->getCoverUhdm()) {
  //   // Check before restore
  //   Location loc(fileSystem->getCheckerHtmlFile(uhdmFileId, symbols));
  //   Error err(ErrorDefinition::UHDM_WRITE_HTML_COVERAGE, loc);
  //   errors->addError(err);
  //   errors->printMessages(clp->muteStdout());
  //
  //   if (UhdmChecker* uhdmchecker =
  //           new UhdmChecker(m_session, m_compileDesign, m_design)) {
  //     uhdmchecker->check(uhdmFileId);
  //     delete uhdmchecker;
  //   }
  // }

  if (clp->getDebugUhdm()) {
    Location loc(symbols->registerSymbol("in-memory uhdm"));
    Error err2(ErrorDefinition::UHDM_VISITOR, loc);
    errors->addError(err2);
    errors->printMessages(clp->muteStdout());
    std::cout << "====== UHDM =======\n";
    vpi_show_ids(clp->showVpiIds());
    visit_designs(designs, std::cout);
    std::cout << "===================\n";
  }
  errors->printMessages(clp->muteStdout());
  return true;
}
}  // namespace SURELOG
