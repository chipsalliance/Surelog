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

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/FileSystem.h>
#include <Surelog/Design/DesignElement.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/ModPort.h>
#include <Surelog/Design/ModuleDefinition.h>
#include <Surelog/Design/ModuleInstance.h>
#include <Surelog/Design/Netlist.h>
#include <Surelog/Design/Parameter.h>
#include <Surelog/Design/Signal.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/UhdmChecker.h>
#include <Surelog/DesignCompile/UhdmWriter.h>
#include <Surelog/Package/Package.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Testbench/ClassDefinition.h>
#include <Surelog/Testbench/Program.h>
#include <Surelog/Testbench/TypeDef.h>
#include <Surelog/Testbench/Variable.h>
#include <Surelog/Utils/StringUtils.h>

#include <cstring>

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/Serializer.h>
#include <uhdm/SynthSubset.h>
#include <uhdm/UhdmAdjuster.h>
#include <uhdm/UhdmLint.h>
#include <uhdm/VpiListener.h>
#include <uhdm/clone_tree.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_visitor.h>

namespace SURELOG {
namespace fs = std::filesystem;
using namespace UHDM;  // NOLINT (we're using a whole bunch of these)

std::string UhdmWriter::builtinGateName(VObjectType type) {
  std::string modName;
  switch (type) {
    case VObjectType::slNInpGate_And:
      modName = "work@and";
      break;
    case VObjectType::slNInpGate_Or:
      modName = "work@or";
      break;
    case VObjectType::slNInpGate_Nand:
      modName = "work@nand";
      break;
    case VObjectType::slNInpGate_Nor:
      modName = "work@nor";
      break;
    case VObjectType::slNInpGate_Xor:
      modName = "work@xor";
      break;
    case VObjectType::slNInpGate_Xnor:
      modName = "work@xnor";
      break;
    case VObjectType::slNOutGate_Buf:
      modName = "work@buf";
      break;
    case VObjectType::slNOutGate_Not:
      modName = "work@not";
      break;
    case VObjectType::slPassEnSwitch_Tranif0:
      modName = "work@tranif0";
      break;
    case VObjectType::slPassEnSwitch_Tranif1:
      modName = "work@tranif1";
      break;
    case VObjectType::slPassEnSwitch_RTranif1:
      modName = "work@rtranif1";
      break;
    case VObjectType::slPassEnSwitch_RTranif0:
      modName = "work@rtranif0";
      break;
    case VObjectType::slPassSwitch_Tran:
      modName = "work@tran";
      break;
    case VObjectType::slPassSwitch_RTran:
      modName = "work@rtran";
      break;
    case VObjectType::slCmosSwitchType_Cmos:
      modName = "work@cmos";
      break;
    case VObjectType::slCmosSwitchType_RCmos:
      modName = "work@rcmos";
      break;
    case VObjectType::slEnableGateType_Bufif0:
      modName = "work@bufif0";
      break;
    case VObjectType::slEnableGateType_Bufif1:
      modName = "work@bufif1";
      break;
    case VObjectType::slEnableGateType_Notif0:
      modName = "work@notif0";
      break;
    case VObjectType::slEnableGateType_Notif1:
      modName = "work@notif1";
      break;
    case VObjectType::slMosSwitchType_NMos:
      modName = "work@nmos";
      break;
    case VObjectType::slMosSwitchType_PMos:
      modName = "work@pmos";
      break;
    case VObjectType::slMosSwitchType_RNMos:
      modName = "work@rnmos";
      break;
    case VObjectType::slMosSwitchType_RPMos:
      modName = "work@rpmos";
      break;
    case VObjectType::slPullup:
      modName = "work@pullup";
      break;
    case VObjectType::slPulldown:
      modName = "work@pulldown";
      break;
    default:
      modName = "work@UnsupportedPrimitive";
      break;
  }
  return modName;
}

unsigned int UhdmWriter::getBuiltinType(VObjectType type) {
  switch (type) {
    case VObjectType::slNInpGate_And:
      return vpiAndPrim;
    case VObjectType::slNInpGate_Or:
      return vpiOrPrim;
    case VObjectType::slNInpGate_Nor:
      return vpiNorPrim;
    case VObjectType::slNInpGate_Nand:
      return vpiNandPrim;
    case VObjectType::slNInpGate_Xor:
      return vpiXorPrim;
    case VObjectType::slNInpGate_Xnor:
      return vpiXnorPrim;
    case VObjectType::slNOutGate_Buf:
      return vpiBufPrim;
    case VObjectType::slNOutGate_Not:
      return vpiNotPrim;
    case VObjectType::slPassEnSwitch_Tranif0:
      return vpiTranif0Prim;
    case VObjectType::slPassEnSwitch_Tranif1:
      return vpiTranif1Prim;
    case VObjectType::slPassEnSwitch_RTranif1:
      return vpiRtranif1Prim;
    case VObjectType::slPassEnSwitch_RTranif0:
      return vpiRtranif0Prim;
    case VObjectType::slPassSwitch_Tran:
      return vpiTranPrim;
    case VObjectType::slPassSwitch_RTran:
      return vpiRtranPrim;
    case VObjectType::slCmosSwitchType_Cmos:
      return vpiCmosPrim;
    case VObjectType::slCmosSwitchType_RCmos:
      return vpiRcmosPrim;
    case VObjectType::slEnableGateType_Bufif0:
      return vpiBufif0Prim;
    case VObjectType::slEnableGateType_Bufif1:
      return vpiBufif1Prim;
    case VObjectType::slEnableGateType_Notif0:
      return vpiNotif0Prim;
    case VObjectType::slEnableGateType_Notif1:
      return vpiNotif1Prim;
    case VObjectType::slMosSwitchType_NMos:
      return vpiNmosPrim;
    case VObjectType::slMosSwitchType_PMos:
      return vpiPmosPrim;
    case VObjectType::slMosSwitchType_RNMos:
      return vpiRnmosPrim;
    case VObjectType::slMosSwitchType_RPMos:
      return vpiRpmosPrim;
    case VObjectType::slPullup:
      return vpiPullupPrim;
    case VObjectType::slPulldown:
      return vpiPulldownPrim;
    default:
      return 0;
  }
}

UhdmWriter::UhdmWriter(CompileDesign* compiler, Design* design)
    : m_compileDesign(compiler), m_design(design) {
  m_helper.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
}

unsigned int UhdmWriter::getStrengthType(VObjectType type) {
  switch (type) {
    case VObjectType::slSupply0:
      return vpiSupply0;
    case VObjectType::slSupply1:
      return vpiSupply1;
    case VObjectType::slStrong0:
      return vpiStrongDrive;
    case VObjectType::slStrong1:
      return vpiStrongDrive;
    case VObjectType::slPull0:
      return vpiPullDrive;
    case VObjectType::slPull1:
      return vpiPullDrive;
    case VObjectType::slWeak0:
      return vpiWeakDrive;
    case VObjectType::slWeak1:
      return vpiWeakDrive;
    case VObjectType::slHighZ0:
      return vpiHighZ;
    case VObjectType::slHighZ1:
      return vpiHighZ;
    default:
      return 0;
  }
}

unsigned int UhdmWriter::getVpiOpType(VObjectType type) {
  switch (type) {
    case VObjectType::slBinOp_Plus:
      return vpiAddOp;
    case VObjectType::slBinOp_Minus:
      return vpiSubOp;
    case VObjectType::slBinOp_Mult:
      return vpiMultOp;
    case VObjectType::slBinOp_MultMult:
      return vpiPowerOp;
    case VObjectType::slBinOp_Div:
      return vpiDivOp;
    case VObjectType::slBinOp_Great:
      return vpiGtOp;
    case VObjectType::slBinOp_GreatEqual:
      return vpiGeOp;
    case VObjectType::slBinOp_Less:
      return vpiLtOp;
    case VObjectType::slBinOp_Imply:
      return vpiImplyOp;
    case VObjectType::slBinOp_Equivalence:
      return vpiEqOp;
    case VObjectType::slBinOp_LessEqual:
      return vpiLeOp;
    case VObjectType::slBinOp_Equiv:
      return vpiEqOp;
    case VObjectType::slBinOp_Not:
    case VObjectType::slNOT:
      return vpiNeqOp;
    case VObjectType::slBinOp_Percent:
      return vpiModOp;
    case VObjectType::slBinOp_LogicAnd:
      return vpiLogAndOp;
    case VObjectType::slBinOp_LogicOr:
      return vpiLogOrOp;
    case VObjectType::slBinOp_BitwAnd:
      return vpiBitAndOp;
    case VObjectType::slBinOp_BitwOr:
      return vpiBitOrOp;
    case VObjectType::slBinOp_BitwXor:
      return vpiBitXorOp;
    case VObjectType::slBinOp_ReductXnor1:
    case VObjectType::slBinOp_ReductXnor2:
    case VObjectType::slBinModOp_ReductXnor1:
    case VObjectType::slBinModOp_ReductXnor2:
      return vpiBitXNorOp;
    case VObjectType::slBinOp_ReductNand:
      return vpiUnaryNandOp;
    case VObjectType::slBinOp_ReductNor:
      return vpiUnaryNorOp;
    case VObjectType::slUnary_Plus:
      return vpiPlusOp;
    case VObjectType::slUnary_Minus:
      return vpiMinusOp;
    case VObjectType::slUnary_Not:
      return vpiNotOp;
    case VObjectType::slUnary_Tilda:
      return vpiBitNegOp;
    case VObjectType::slUnary_BitwAnd:
      return vpiUnaryAndOp;
    case VObjectType::slUnary_BitwOr:
      return vpiUnaryOrOp;
    case VObjectType::slUnary_BitwXor:
      return vpiUnaryXorOp;
    case VObjectType::slUnary_ReductNand:
      return vpiUnaryNandOp;
    case VObjectType::slUnary_ReductNor:
      return vpiUnaryNorOp;
    case VObjectType::slUnary_ReductXnor1:
    case VObjectType::slUnary_ReductXnor2:
      return vpiUnaryXNorOp;
    case VObjectType::slBinOp_ShiftLeft:
      return vpiLShiftOp;
    case VObjectType::slBinOp_ShiftRight:
      return vpiRShiftOp;
    case VObjectType::slBinOp_ArithShiftLeft:
      return vpiArithLShiftOp;
    case VObjectType::slBinOp_ArithShiftRight:
      return vpiArithRShiftOp;
    case VObjectType::slIncDec_PlusPlus:
      return vpiPostIncOp;
    case VObjectType::slIncDec_MinusMinus:
      return vpiPostDecOp;
    case VObjectType::slConditional_operator:
    case VObjectType::slQmark:
      return vpiConditionOp;
    case VObjectType::slInsideOp:
    case VObjectType::slOpen_range_list:
      return vpiInsideOp;
    case VObjectType::slBinOp_FourStateLogicEqual:
      return vpiCaseEqOp;
    case VObjectType::slBinOp_FourStateLogicNotEqual:
      return vpiCaseNeqOp;
    case VObjectType::slAssignOp_Assign:
      return vpiAssignmentOp;
    case VObjectType::slAssignOp_Add:
      return vpiAddOp;
    case VObjectType::slAssignOp_Sub:
      return vpiSubOp;
    case VObjectType::slAssignOp_Mult:
      return vpiMultOp;
    case VObjectType::slAssignOp_Div:
      return vpiDivOp;
    case VObjectType::slAssignOp_Modulo:
      return vpiModOp;
    case VObjectType::slAssignOp_BitwAnd:
      return vpiBitAndOp;
    case VObjectType::slAssignOp_BitwOr:
      return vpiBitOrOp;
    case VObjectType::slAssignOp_BitwXor:
      return vpiBitXorOp;
    case VObjectType::slAssignOp_BitwLeftShift:
      return vpiLShiftOp;
    case VObjectType::slAssignOp_BitwRightShift:
      return vpiRShiftOp;
    case VObjectType::slAssignOp_ArithShiftLeft:
      return vpiArithLShiftOp;
    case VObjectType::slAssignOp_ArithShiftRight:
      return vpiArithRShiftOp;
    case VObjectType::slMatches:
      return vpiMatchOp;
    case VObjectType::slBinOp_WildcardEqual:
    case VObjectType::slBinOp_WildEqual:
      return vpiWildEqOp;
    case VObjectType::slBinOp_WildcardNotEqual:
    case VObjectType::slBinOp_WildNotEqual:
      return vpiWildNeqOp;
    case VObjectType::slIFF:
      return vpiIffOp;
    case VObjectType::slNON_OVERLAP_IMPLY:
      return vpiNonOverlapImplyOp;
    case VObjectType::slOVERLAP_IMPLY:
      return vpiOverlapImplyOp;
    case VObjectType::slOVERLAPPED:
      return vpiOverlapFollowedByOp;
    case VObjectType::slNONOVERLAPPED:
      return vpiNonOverlapFollowedByOp;
    case VObjectType::slUNTIL:
      return vpiUntilOp;
    case VObjectType::slS_UNTIL:
      return vpiUntilOp;
    case VObjectType::slUNTIL_WITH:
      return vpiUntilWithOp;
    case VObjectType::slS_UNTIL_WITH:
      return vpiUntilWithOp;
    case VObjectType::slIMPLIES:
      return vpiImpliesOp;
    case VObjectType::slCycle_delay_range:
      return vpiCycleDelayOp;
    case VObjectType::slConsecutive_repetition:
      return vpiConsecutiveRepeatOp;
    case VObjectType::slNon_consecutive_repetition:
      return vpiRepeatOp;
    case VObjectType::slGoto_repetition:
      return vpiGotoRepeatOp;
    case VObjectType::slThroughout:
      return vpiThroughoutOp;
    case VObjectType::slWithin:
      return vpiWithinOp;
    case VObjectType::slIntersect:
      return vpiIntersectOp;
    case VObjectType::slFirstMatch:
      return vpiFirstMatchOp;
    default:
      return 0;
  }
}

bool isMultidimensional(const UHDM::typespec* ts) {
  bool isMultiDimension = false;
  if (ts) {
    if (ts->UhdmType() == uhdmlogic_typespec) {
      logic_typespec* lts = (logic_typespec*)ts;
      if (lts->Ranges() && lts->Ranges()->size() > 1) isMultiDimension = true;
    } else if (ts->UhdmType() == uhdmarray_typespec) {
      array_typespec* lts = (array_typespec*)ts;
      if (lts->Ranges() && lts->Ranges()->size() > 1) isMultiDimension = true;
    } else if (ts->UhdmType() == uhdmpacked_array_typespec) {
      packed_array_typespec* lts = (packed_array_typespec*)ts;
      if (lts->Ranges() && lts->Ranges()->size() > 1) isMultiDimension = true;
    } else if (ts->UhdmType() == uhdmbit_typespec) {
      bit_typespec* lts = (bit_typespec*)ts;
      if (lts->Ranges() && lts->Ranges()->size() > 1) isMultiDimension = true;
    }
  }
  return isMultiDimension;
}

bool writeElabParameters(Serializer& s, ModuleInstance* instance,
                         UHDM::scope* m, ExprBuilder& exprBuilder) {
  Netlist* netlist = instance->getNetlist();
  DesignComponent* mod = instance->getDefinition();

  std::map<std::string_view, any*> paramSet;
  if (netlist->param_assigns()) {
    VectorOfany* params = m->Parameters();
    if (params == nullptr) params = s.MakeAnyVec();
    m->Parameters(params);
    m->Param_assigns(netlist->param_assigns());
  }

  if (mod) {
    VectorOfany* params = m->Parameters();
    if (params == nullptr) params = s.MakeAnyVec();
    m->Parameters(params);
    VectorOfany* orig_params = mod->getParameters();
    if (orig_params) {
      for (auto orig : *orig_params) {
        const std::string_view name = orig->VpiName();
        bool pushed = false;
        // Specifc handling of type parameters
        if (orig->UhdmType() == uhdmtype_parameter) {
          for (auto p : instance->getTypeParams()) {
            if (p->getName() == orig->VpiName()) {
              any* uparam = p->getUhdmParam();
              if (uparam) {
                uparam->VpiParent(m);
                for (VectorOfany::iterator itr = params->begin();
                     itr != params->end(); itr++) {
                  if ((*itr)->VpiName() == p->getName()) {
                    params->erase(itr);
                    break;
                  }
                }
                params->push_back(uparam);
                pushed = true;
              }
              break;
            }
          }
          if (!pushed) {
            // These point to the sole copy (unelaborated)
            for (VectorOfany::iterator itr = params->begin();
                 itr != params->end(); itr++) {
              if ((*itr)->VpiName() == orig->VpiName()) {
                params->erase(itr);
                break;
              }
            }
            params->push_back(orig);
          }
        } else {
          // Regular param
          ElaboratorListener listener(&s, false, true);
          any* pclone = UHDM::clone_tree(orig, s, &listener);
          pclone->VpiParent(m);
          paramSet.emplace(name, pclone);
          /*

            Keep the value of the parameter used during definition. The
          param_assign contains the actual value useful for elaboration

          const typespec* ts = ((parameter*)pclone)->Typespec();
          bool multi = isMultidimensional(ts);
          if (((parameter*)pclone)->Ranges() &&
          ((parameter*)pclone)->Ranges()->size() > 1) multi = true;

          if (instance->getComplexValue(name)) {
          } else {
            Value* val = instance->getValue(name, exprBuilder);
            if (val && val->isValid() && (!multi)) {
              ((parameter*)pclone)->VpiValue(val->uhdmValue());
            }
          }
          */
          params->push_back(pclone);
        }
      }
    }
  }

  if (netlist->param_assigns()) {
    for (auto ps : *m->Param_assigns()) {
      ps->VpiParent(m);
      const std::string_view name = ps->Lhs()->VpiName();
      auto itr = paramSet.find(name);
      if (itr != paramSet.end()) {
        ps->Lhs((*itr).second);
      }
    }
  }
  return true;
}

unsigned int UhdmWriter::getVpiDirection(VObjectType type) {
  unsigned int direction = vpiInout;
  if (type == VObjectType::slPortDir_Inp ||
      type == VObjectType::slTfPortDir_Inp)
    direction = vpiInput;
  else if (type == VObjectType::slPortDir_Out ||
           type == VObjectType::slTfPortDir_Out)
    direction = vpiOutput;
  else if (type == VObjectType::slPortDir_Inout ||
           type == VObjectType::slTfPortDir_Inout)
    direction = vpiInout;
  else if (type == VObjectType::slTfPortDir_Ref ||
           type == VObjectType::slTfPortDir_ConstRef)
    direction = vpiRef;
  return direction;
}

unsigned int UhdmWriter::getVpiNetType(VObjectType type) {
  unsigned int nettype = 0;
  switch (type) {
    case VObjectType::slNetType_Wire:
      nettype = vpiWire;
      break;
    case VObjectType::slIntVec_TypeReg:
      nettype = vpiReg;
      break;
    case VObjectType::slNetType_Supply0:
      nettype = vpiSupply0;
      break;
    case VObjectType::slNetType_Supply1:
      nettype = vpiSupply1;
      break;
    case VObjectType::slIntVec_TypeLogic:
      nettype = vpiLogicNet;
      break;
    case VObjectType::slNetType_Wand:
      nettype = vpiWand;
      break;
    case VObjectType::slNetType_Wor:
      nettype = vpiWor;
      break;
    case VObjectType::slNetType_Tri:
      nettype = vpiTri;
      break;
    case VObjectType::slNetType_Tri0:
      nettype = vpiTri0;
      break;
    case VObjectType::slNetType_Tri1:
      nettype = vpiTri1;
      break;
    case VObjectType::slNetType_TriReg:
      nettype = vpiTriReg;
      break;
    case VObjectType::slNetType_TriAnd:
      nettype = vpiTriAnd;
      break;
    case VObjectType::slNetType_TriOr:
      nettype = vpiTriOr;
      break;
    case VObjectType::slNetType_Uwire:
      nettype = vpiUwire;
      break;
    case VObjectType::slImplicit_data_type:
    case VObjectType::slSigning_Signed:
    case VObjectType::slPacked_dimension:
    case VObjectType::slSigning_Unsigned:
      nettype = vpiNone;
      break;
    default:
      break;
  }
  return nettype;
}

void UhdmWriter::writePorts(std::vector<Signal*>& orig_ports, BaseClass* parent,
                            VectorOfport* dest_ports, VectorOfnet* dest_nets,
                            Serializer& s,
                            UhdmWriter::ComponentMap& componentMap,
                            UhdmWriter::ModPortMap& modPortMap,
                            UhdmWriter::SignalBaseClassMap& signalBaseMap,
                            UhdmWriter::SignalMap& signalMap,
                            ModuleInstance* instance, ModuleDefinition* mod) {
  int lastPortDirection = vpiInout;
  for (Signal* orig_port : orig_ports) {
    port* dest_port = s.MakePort();
    signalBaseMap.emplace(orig_port, dest_port);
    signalMap.emplace(orig_port->getName(), orig_port);
    const FileContent* fC = orig_port->getFileContent();
    if (fC->Type(orig_port->getNodeId()) == VObjectType::slStringConst)
      dest_port->VpiName(orig_port->getName());
    if (orig_port->getDirection() != VObjectType::slNoType)
      lastPortDirection =
          UhdmWriter::getVpiDirection(orig_port->getDirection());
    dest_port->VpiDirection(lastPortDirection);
    orig_port->getFileContent()->populateCoreMembers(
        orig_port->getNodeId(), orig_port->getNodeId(), dest_port);
    dest_port->VpiParent(parent);
    if (ModPort* orig_modport = orig_port->getModPort()) {
      ref_obj* ref = s.MakeRef_obj();
      dest_port->Low_conn(ref);
      std::map<ModPort*, modport*>::iterator itr =
          modPortMap.find(orig_modport);
      if (itr != modPortMap.end()) {
        ref->Actual_group((*itr).second);
      }
    } else if (ModuleDefinition* orig_interf = orig_port->getInterfaceDef()) {
      ref_obj* ref = s.MakeRef_obj();
      dest_port->Low_conn(ref);
      const auto& found = componentMap.find(orig_interf);
      if (found != componentMap.end()) {
        ref->Actual_group(found->second);
      }
    }
    if (orig_port->getTypeSpecId() && mod) {
      if (NodeId unpackedDimensions = orig_port->getUnpackedDimension()) {
        int unpackedSize = 0;
        const FileContent* fC = orig_port->getFileContent();
        if (std::vector<UHDM::range*>* ranges = m_helper.compileRanges(
                mod, fC, unpackedDimensions, m_compileDesign, nullptr, instance,
                false, unpackedSize, false)) {
          array_typespec* array_ts = s.MakeArray_typespec();
          array_ts->Ranges(ranges);
          array_ts->VpiParent(dest_port);
          fC->populateCoreMembers(orig_port->getTypeSpecId(), InvalidNodeId,
                                  array_ts);
          if (!ranges->empty()) {
            array_ts->VpiEndLineNo(ranges->back()->VpiEndLineNo());
            array_ts->VpiEndColumnNo(ranges->back()->VpiEndColumnNo());
          }
          for (range* r : *ranges) {
            const expr* rrange = r->Right_expr();
            if (rrange->VpiValue() == "STRING:associative") {
              array_ts->VpiArrayType(vpiAssocArray);
              array_ts->Index_typespec((typespec*)rrange->Typespec());
            } else if (rrange->VpiValue() == "STRING:unsized") {
              array_ts->VpiArrayType(vpiDynamicArray);
            } else if (rrange->VpiValue() == "STRING:$") {
              array_ts->VpiArrayType(vpiQueueArray);
            } else {
              array_ts->VpiArrayType(vpiStaticArray);
            }
          }
          dest_port->Typespec(array_ts);

          if (typespec* typespec = m_helper.compileTypespec(
                  mod, fC, orig_port->getTypeSpecId(), m_compileDesign, nullptr,
                  nullptr, false, true)) {
            array_ts->Elem_typespec(typespec);
          }
        }
      } else if (typespec* typespec = m_helper.compileTypespec(
                     mod, fC, orig_port->getTypeSpecId(), m_compileDesign,
                     nullptr, nullptr, false, true)) {
        dest_port->Typespec(typespec);
      }
    }
    dest_ports->push_back(dest_port);
  }
}

void writeDataTypes(const DesignComponent::DataTypeMap& datatypeMap,
                    BaseClass* parent, VectorOftypespec* dest_typespecs,
                    Serializer& s, bool setParent) {
  std::set<uint64_t> ids;
  for (const auto& entry : datatypeMap) {
    const DataType* dtype = entry.second;
    if (dtype->getCategory() == DataType::Category::REF) {
      dtype = dtype->getDefinition();
    }
    if (dtype->getCategory() == DataType::Category::TYPEDEF) {
      if (dtype->getTypespec() == nullptr) dtype = dtype->getDefinition();
    }
    typespec* tps = dtype->getTypespec();
    if (parent->UhdmType() == uhdmpackage) {
      if (tps && (tps->VpiName().find("::") == std::string::npos)) {
        const std::string newName =
            StrCat(parent->VpiName(), "::", tps->VpiName());
        tps->VpiName(newName);
      }
    }

    if (tps) {
      if (!tps->Instance()) {
        if (parent->UhdmType() != uhdmclass_defn)
          tps->Instance((instance*)parent);
      }
      if (setParent) tps->VpiParent(parent);
      if (ids.find(tps->UhdmId()) == ids.end()) {
        dest_typespecs->push_back(tps);
        ids.insert(tps->UhdmId());
      }
    }
  }
}

void writeNets(std::vector<Signal*>& orig_nets, BaseClass* parent,
               VectorOfnet* dest_nets, Serializer& s,
               UhdmWriter::SignalBaseClassMap& signalBaseMap,
               UhdmWriter::SignalMap& signalMap, UhdmWriter::SignalMap& portMap,
               ModuleInstance* instance = nullptr) {
  for (auto& orig_net : orig_nets) {
    net* dest_net = nullptr;
    if (instance) {
      for (net* net : *instance->getNetlist()->nets()) {
        UhdmWriter::SignalMap::iterator itr = signalMap.find(net->VpiName());
        if (itr == signalMap.end()) {
          if (net->VpiName() == orig_net->getName()) {
            dest_net = net;
            break;
          }
        }
      }
    } else {
      dest_net = s.MakeLogic_net();
    }
    if (dest_net) {
      const FileContent* fC = orig_net->getFileContent();
      if (fC->Type(orig_net->getNodeId()) == VObjectType::slStringConst) {
        auto portItr = portMap.find(orig_net->getName());
        if (portItr != portMap.end()) {
          Signal* sig = (*portItr).second;
          if (sig) {
            UhdmWriter::SignalBaseClassMap::iterator itr =
                signalBaseMap.find(sig);
            if (itr != signalBaseMap.end()) {
              port* p = (port*)((*itr).second);
              if (p->Low_conn() == nullptr) {
                ref_obj* ref = s.MakeRef_obj();
                ref->Actual_group(dest_net);
                p->Low_conn(ref);
              } else if (p->Low_conn()->UhdmType() == uhdmref_obj) {
                ref_obj* ref = (ref_obj*)p->Low_conn();
                if (ref->Actual_group() == nullptr) {
                  ref->Actual_group(dest_net);
                }
              }
            }
          }
        }
        signalBaseMap.emplace(orig_net, dest_net);
        signalMap.emplace(orig_net->getName(), orig_net);
        dest_net->VpiName(orig_net->getName());
        orig_net->getFileContent()->populateCoreMembers(
            orig_net->getNodeId(), orig_net->getNodeId(), dest_net);
        dest_net->VpiNetType(UhdmWriter::getVpiNetType(orig_net->getType()));
        dest_net->VpiParent(parent);
        dest_nets->push_back(dest_net);
      }
    }
  }
}

void mapLowConns(std::vector<Signal*>& orig_ports, Serializer& s,
                 UhdmWriter::SignalBaseClassMap& signalBaseMap) {
  for (Signal* orig_port : orig_ports) {
    if (Signal* lowconn = orig_port->getLowConn()) {
      std::map<Signal*, BaseClass*>::iterator itrlow =
          signalBaseMap.find(lowconn);
      if (itrlow != signalBaseMap.end()) {
        std::map<Signal*, BaseClass*>::iterator itrport =
            signalBaseMap.find(orig_port);
        if (itrport != signalBaseMap.end()) {
          ref_obj* ref = s.MakeRef_obj();
          ((port*)(*itrport).second)->Low_conn(ref);
          ref->Actual_group((*itrlow).second);
        }
      }
    }
  }
}

void UhdmWriter::writeClass(ClassDefinition* classDef,
                            VectorOfclass_defn* dest_classes, Serializer& s,
                            UhdmWriter::ComponentMap& componentMap,
                            BaseClass* parent) {
  if (!classDef->getFileContents().empty() &&
      classDef->getType() == VObjectType::slClass_declaration) {
    const FileContent* fC = classDef->getFileContents()[0];
    class_defn* c = classDef->getUhdmDefinition();
    c->VpiParent(parent);
    // Typepecs
    VectorOftypespec* typespecs = s.MakeTypespecVec();
    c->Typespecs(typespecs);
    writeDataTypes(classDef->getDataTypeMap(), c, typespecs, s, true);

    // Variables
    // Already bound in TestbenchElaboration

    // Function and tasks
    c->Task_funcs(classDef->getTask_funcs());
    if (c->Task_funcs()) {
      for (auto tf : *c->Task_funcs()) {
        if (tf->VpiParent() == nullptr) tf->VpiParent(c);
      }
    }
    // Parameters
    if (classDef->getParameters()) {
      c->Parameters(classDef->getParameters());
      for (auto ps : *c->Parameters()) {
        ps->VpiParent(c);
      }
    }
    // Extends, fix late binding
    if (const extends* ext = c->Extends()) {
      if (const class_typespec* tps = ext->Class_typespec()) {
        if (tps->Class_defn() == nullptr) {
          const std::string_view tpsName = tps->VpiName();
          if (c->Parameters()) {
            for (auto ps : *c->Parameters()) {
              if (ps->VpiName() == tpsName) {
                if (ps->UhdmType() == uhdmtype_parameter) {
                  type_parameter* tp = (type_parameter*)ps;
                  if (const typespec* ptp = tp->Typespec()) {
                    if (ptp->UhdmType() == uhdmclass_typespec) {
                      class_typespec* cptp = (class_typespec*)ptp;
                      ((class_typespec*)tps)
                          ->Class_defn((class_defn*)cptp->Class_defn());
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
    if (classDef->getParam_assigns()) {
      c->Param_assigns(classDef->getParam_assigns());
      for (auto ps : *c->Param_assigns()) {
        ps->VpiParent(c);
      }
    }
    componentMap.emplace(classDef, c);
    c->VpiParent(parent);
    dest_classes->push_back(c);
    const std::string_view name = classDef->getName();
    if (c->VpiName().empty()) c->VpiName(name);
    if (c->VpiFullName().empty()) c->VpiFullName(name);
    c->Attributes(classDef->Attributes());
    if (fC) {
      // Builtin classes have no file
      const NodeId modId = classDef->getNodeIds()[0];
      const NodeId startId = fC->sl_collect(modId, VObjectType::slClass);
      fC->populateCoreMembers(startId, modId, c);
    }
    // Activate when hier_path is better supported
    // lateTypedefBinding(s, classDef, c, componentMap);
    // lateBinding(s, classDef, c, componentMap);

    for (auto& nested : classDef->getClassMap()) {
      ClassDefinition* c_nested = nested.second;
      VectorOfclass_defn* dest_classes = s.MakeClass_defnVec();
      writeClass(c_nested, dest_classes, s, componentMap, c);
    }
  }
}

void UhdmWriter::writeClasses(ClassNameClassDefinitionMultiMap& orig_classes,
                              VectorOfclass_defn* dest_classes, Serializer& s,
                              UhdmWriter::ComponentMap& componentMap,
                              BaseClass* parent) {
  for (auto& orig_class : orig_classes) {
    ClassDefinition* classDef = orig_class.second;
    writeClass(classDef, dest_classes, s, componentMap, parent);
  }
}

void writeVariables(const DesignComponent::VariableMap& orig_vars,
                    BaseClass* parent, VectorOfvariables* dest_vars,
                    Serializer& s, UhdmWriter::ComponentMap& componentMap) {
  for (auto& orig_var : orig_vars) {
    Variable* var = orig_var.second;
    const DataType* dtype = var->getDataType();
    const ClassDefinition* classdef =
        datatype_cast<const ClassDefinition*>(dtype);
    if (classdef) {
      class_var* cvar = s.MakeClass_var();
      cvar->VpiName(var->getName());
      var->getFileContent()->populateCoreMembers(var->getNodeId(),
                                                 var->getNodeId(), cvar);
      cvar->VpiParent(parent);
      const auto& found = componentMap.find(classdef);
      if (found != componentMap.end()) {
        // TODO: Bind Class type,
        // class_var -> class_typespec -> class_defn
      }
      dest_vars->push_back(cvar);
    }
  }
}

class ReInstanceTypespec : public VpiListener {
 public:
  explicit ReInstanceTypespec(package* p) : m_package(p) {}
  ~ReInstanceTypespec() override = default;

  void leaveAny(const any* object, vpiHandle handle) final {
    if (any_cast<const typespec*>(object) != nullptr) {
      if ((object->UhdmType() != uhdmclass_typespec) &&
          (object->UhdmType() != uhdmevent_typespec) &&
          (object->UhdmType() != uhdmimport_typespec) &&
          (object->UhdmType() != uhdmtype_parameter)) {
        reInstance(object);
      }
    }
  }

  void leaveFunction(const function* object, vpiHandle handle) final {
    reInstance(object);
  }
  void leaveTask(const task* object, vpiHandle handle) final {
    reInstance(object);
  }
  void reInstance(const any* cobject) {
    any* object = (any*)cobject;
    const instance* inst = nullptr;
    if (typespec* tps = any_cast<typespec*>(object)) {
      inst = (instance*)tps->Instance();
    } else if (function* tps = any_cast<function*>(object)) {
      inst = (instance*)tps->Instance();
    } else if (task* tps = any_cast<task*>(object)) {
      inst = (instance*)tps->Instance();
    }
    if (inst) {
      const std::string_view name = inst->VpiName();
      design* d = (design*)m_package->VpiParent();
      for (auto pack : *d->AllPackages()) {
        if (pack->VpiName() == name) {
          if (typespec* tps = any_cast<typespec*>(object)) {
            tps->Instance(pack);
          } else if (function* tps = any_cast<function*>(object)) {
            tps->Instance(pack);
          } else if (task* tps = any_cast<task*>(object)) {
            tps->Instance(pack);
          }
          break;
        }
      }
    }
  }

 private:
  package* m_package = nullptr;
};

// Non-elaborated package typespec Instance relation need to point to
// non-elablarated package
void reInstanceTypespec(Serializer& serializer, any* root, package* p) {
  ReInstanceTypespec* listener = new ReInstanceTypespec(p);
  vpiHandle handle = serializer.MakeUhdmHandle(root->UhdmType(), root);
  listener->listenAny(handle);
  vpi_release_handle(handle);
  delete listener;
}

void UhdmWriter::writePackage(Package* pack, package* p, Serializer& s,
                              UhdmWriter::ComponentMap& componentMap,
                              bool elaborated) {
  p->VpiFullName(StrCat(pack->getName(), "::"));
  VectorOfclass_defn* dest_classes = nullptr;

  // Typepecs
  VectorOftypespec* typespecs = s.MakeTypespecVec();
  p->Typespecs(typespecs);
  writeDataTypes(pack->getDataTypeMap(), p, typespecs, s, true);
  for (auto tp : *typespecs) {
    tp->Instance(p);
  }
  for (auto item : pack->getImportedSymbols()) {
    typespecs->push_back(item);
  }
  // Classes
  ClassNameClassDefinitionMultiMap& orig_classes = pack->getClassDefinitions();
  dest_classes = s.MakeClass_defnVec();
  writeClasses(orig_classes, dest_classes, s, componentMap, p);
  p->Class_defns(dest_classes);
  // Parameters
  if (pack->getParameters()) {
    p->Parameters(pack->getParameters());
    for (auto ps : *p->Parameters()) {
      ps->VpiParent(p);
      if (ps->UhdmType() == uhdmparameter) {
        ((parameter*)ps)
            ->VpiFullName(StrCat(pack->getName(), "::", ps->VpiName()));
      } else {
        ((type_parameter*)ps)
            ->VpiFullName(StrCat(pack->getName(), "::", ps->VpiName()));
      }
    }
  }

  // Param_assigns

  if (pack->getParam_assigns()) {
    p->Param_assigns(pack->getParam_assigns());
    for (auto ps : *p->Param_assigns()) {
      ps->VpiParent(p);
    }
  }

  // Function and tasks
  if (pack->getTask_funcs()) {
    p->Task_funcs(s.MakeTask_funcVec());
    for (auto tf : *pack->getTask_funcs()) {
      const std::string_view funcName = tf->VpiName();
      if (funcName.find("::") != std::string::npos) {
        std::vector<std::string_view> res;
        StringUtils::tokenizeMulti(funcName, "::", res);
        const std::string_view className = res[0];
        const std::string_view funcName = res[1];
        bool foundParentClass = false;
        for (auto cl : *dest_classes) {
          if (cl->VpiName() == className) {
            tf->VpiParent(cl);
            tf->Instance(p);
            if (cl->Task_funcs() == nullptr) {
              cl->Task_funcs(s.MakeTask_funcVec());
            }
            cl->Task_funcs()->push_back(tf);
            foundParentClass = true;
            break;
          }
        }
        if (foundParentClass) {
          tf->VpiName(funcName);
          ((task_func*)tf)
              ->VpiFullName(StrCat(pack->getName(), "::", className,
                                   "::", tf->VpiName()));
        } else {
          tf->VpiParent(p);
          tf->Instance(p);
          p->Task_funcs()->push_back(tf);
          ((task_func*)tf)
              ->VpiFullName(StrCat(pack->getName(), "::", tf->VpiName()));
        }
      } else {
        tf->VpiParent(p);
        tf->Instance(p);
        p->Task_funcs()->push_back(tf);
        ((task_func*)tf)
            ->VpiFullName(StrCat(pack->getName(), "::", tf->VpiName()));
      }
    }
  }
  // Variables
  Netlist* netlist = pack->getNetlist();
  if (netlist) {
    p->Variables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->VpiParent(p);
        ((variables*)obj)
            ->VpiFullName(StrCat(pack->getName(), "::", obj->VpiName()));
      }
    }
  }
  // Nets
  UhdmWriter::SignalBaseClassMap signalBaseMap;
  UhdmWriter::SignalMap portMap;
  UhdmWriter::SignalMap netMap;
  std::vector<Signal*> orig_nets = pack->getSignals();
  VectorOfnet* dest_nets = s.MakeNetVec();
  writeNets(orig_nets, p, dest_nets, s, signalBaseMap, netMap, portMap,
            nullptr);
  p->Nets(dest_nets);
  if (elaborated) {
    lateTypedefBinding(s, pack, p, componentMap);
  }
  lateBinding(s, pack, p, componentMap);
}

void UhdmWriter::writeModule(ModuleDefinition* mod, module_inst* m,
                             Serializer& s,
                             UhdmWriter::ComponentMap& componentMap,
                             /*ModuleMap& moduleMap,*/
                             UhdmWriter::ModPortMap& modPortMap,
                             ModuleInstance* instance) {
  UhdmWriter::SignalBaseClassMap signalBaseMap;
  UhdmWriter::SignalMap portMap;
  UhdmWriter::SignalMap netMap;

  // Let decls
  if (!mod->getLetStmts().empty()) {
    VectorOflet_decl* decls = s.MakeLet_declVec();
    m->Let_decls(decls);
    for (auto stmt : mod->getLetStmts()) {
      decls->push_back((let_decl*)stmt.second->Decl());
    }
  }

  // Typepecs
  VectorOftypespec* typespecs = s.MakeTypespecVec();
  m->Typespecs(typespecs);
  writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, true);
  for (auto item : mod->getImportedSymbols()) {
    typespecs->push_back(item);
  }
  // Ports
  std::vector<Signal*>& orig_ports = mod->getPorts();
  VectorOfport* dest_ports = s.MakePortVec();
  VectorOfnet* dest_nets = s.MakeNetVec();
  writePorts(orig_ports, m, dest_ports, dest_nets, s, componentMap, modPortMap,
             signalBaseMap, portMap, instance, mod);
  m->Ports(dest_ports);
  // Nets
  std::vector<Signal*> orig_nets = mod->getSignals();
  writeNets(orig_nets, m, dest_nets, s, signalBaseMap, netMap, portMap,
            instance);
  m->Nets(dest_nets);
  mapLowConns(orig_ports, s, signalBaseMap);
  // Classes
  ClassNameClassDefinitionMultiMap& orig_classes = mod->getClassDefinitions();
  VectorOfclass_defn* dest_classes = s.MakeClass_defnVec();
  writeClasses(orig_classes, dest_classes, s, componentMap, m);
  m->Class_defns(dest_classes);
  // Variables
  // DesignComponent::VariableMap& orig_vars = mod->getVariables();
  // VectorOfvariables* dest_vars = s.MakeVariablesVec();
  // writeVariables(orig_vars, m, dest_vars, s, componentMap);
  // m->Variables(dest_vars);

  // Cont assigns
  m->Cont_assigns(mod->getContAssigns());
  if (m->Cont_assigns()) {
    for (auto ps : *m->Cont_assigns()) {
      ps->VpiParent(m);
    }
  }

  // Processes
  m->Process(mod->getProcesses());
  if (m->Process()) {
    for (auto ps : *m->Process()) {
      ps->VpiParent(m);
    }
  }
  // Parameters
  if (mod->getParameters()) {
    m->Parameters(mod->getParameters());
    for (auto ps : *m->Parameters()) {
      ps->VpiParent(m);
    }
  }
  // Param_assigns
  if (mod->getParam_assigns()) {
    m->Param_assigns(mod->getParam_assigns());
    for (auto ps : *m->Param_assigns()) {
      ps->VpiParent(m);
    }
  }
  // Function and tasks
  if (auto from = mod->getTask_funcs()) {
    UHDM::VectorOftask_func* target = m->Task_funcs();
    if (target == nullptr) {
      m->Task_funcs(s.MakeTask_funcVec());
      target = m->Task_funcs();
    }
    for (auto tf : *from) {
      target->push_back(tf);
      if (tf->VpiParent() == nullptr) tf->VpiParent(m);
      if (tf->Instance() == nullptr) tf->Instance(m);
    }
  }

  // ClockingBlocks
  for (const auto& ctupple : mod->getClockingBlockMap()) {
    const ClockingBlock& cblock = ctupple.second;
    switch (cblock.getType()) {
      case ClockingBlock::Type::Default: {
        m->Default_clocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Global: {
        m->Global_clocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Regular: {
        VectorOfclocking_block* cblocks = m->Clocking_blocks();
        if (cblocks == nullptr) {
          m->Clocking_blocks(s.MakeClocking_blockVec());
          cblocks = m->Clocking_blocks();
        }
        cblocks->push_back(cblock.getActual());
        break;
      }
    }
  }

  // Assertions
  if (mod->getAssertions()) {
    m->Assertions(mod->getAssertions());
    for (auto ps : *m->Assertions()) {
      ps->VpiParent(m);
    }
  }
  // Module Instantiation
  /*
  if (std::vector<UHDM::ref_module*>* subModules = mod->getRefModules()) {
    m->Ref_modules(subModules);
    for (auto subMod : *subModules) {
      ModuleMap::iterator itr = moduleMap.find(std::string(subMod->VpiName()));
      if (itr != moduleMap.end()) {
        subMod->Actual_group((*itr).second);
      }
    }
  }
  */

  if (VectorOfmodule_array* subModuleArrays = mod->getModuleArrays()) {
    m->Module_arrays(subModuleArrays);
    for (auto subModArr : *subModuleArrays) {
      subModArr->VpiParent(m);
    }
  }
  // Interface instantiation
  const std::vector<Signal*>& signals = mod->getSignals();
  if (!signals.empty()) {
    VectorOfinterface_array* subInterfaceArrays = s.MakeInterface_arrayVec();
    m->Interface_arrays(subInterfaceArrays);
    for (Signal* sig : signals) {
      NodeId unpackedDimension = sig->getUnpackedDimension();
      if (unpackedDimension && sig->getInterfaceDef()) {
        int unpackedSize = 0;
        const FileContent* fC = sig->getFileContent();
        if (std::vector<UHDM::range*>* unpackedDimensions =
                m_helper.compileRanges(mod, fC, unpackedDimension,
                                       m_compileDesign, nullptr, instance,
                                       false, unpackedSize, false)) {
          NodeId id = sig->getNodeId();
          const std::string typeName = sig->getInterfaceTypeName();
          interface_array* smarray = s.MakeInterface_array();
          smarray->Ranges(unpackedDimensions);
          if (fC->Type(id) == VObjectType::slStringConst) {
            smarray->VpiName(sig->getName());
          }
          smarray->VpiFullName(typeName);
          smarray->VpiParent(m);
          fC->populateCoreMembers(id, id, smarray);

          NodeId typespecStart = sig->getInterfaceTypeNameId();
          NodeId typespecEnd = typespecStart;
          while (fC->Sibling(typespecEnd)) {
            typespecEnd = fC->Sibling(typespecEnd);
          }
          interface_typespec* tps = s.MakeInterface_typespec();
          tps->VpiName(typeName);
          fC->populateCoreMembers(typespecStart, typespecEnd, tps);
          smarray->Elem_typespec(tps);

          subInterfaceArrays->push_back(smarray);
        }
      }
    }
  }
}

void UhdmWriter::writeInterface(ModuleDefinition* mod, interface_inst* m,
                                Serializer& s, ComponentMap& componentMap,
                                ModPortMap& modPortMap,
                                ModuleInstance* instance) {
  SignalBaseClassMap signalBaseMap;
  SignalMap portMap;
  SignalMap netMap;

  // Let decls
  if (!mod->getLetStmts().empty()) {
    VectorOflet_decl* decls = s.MakeLet_declVec();
    m->Let_decls(decls);
    for (auto stmt : mod->getLetStmts()) {
      decls->push_back((let_decl*)stmt.second->Decl());
    }
  }

  // Typepecs
  VectorOftypespec* typespecs = s.MakeTypespecVec();
  m->Typespecs(typespecs);
  writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, true);
  for (auto item : mod->getImportedSymbols()) {
    typespecs->push_back(item);
  }
  // Ports
  std::vector<Signal*>& orig_ports = mod->getPorts();
  VectorOfport* dest_ports = s.MakePortVec();
  VectorOfnet* dest_nets = s.MakeNetVec();
  writePorts(orig_ports, m, dest_ports, dest_nets, s, componentMap, modPortMap,
             signalBaseMap, portMap, instance);
  m->Ports(dest_ports);
  std::vector<Signal*> orig_nets = mod->getSignals();
  writeNets(orig_nets, m, dest_nets, s, signalBaseMap, netMap, portMap,
            instance);
  m->Nets(dest_nets);
  // Modports
  ModuleDefinition::ModPortSignalMap& orig_modports =
      mod->getModPortSignalMap();
  VectorOfmodport* dest_modports = s.MakeModportVec();
  for (auto& orig_modport : orig_modports) {
    modport* dest_modport = s.MakeModport();
    // dest_modport->Interface(m); // Loop in elaboration!
    dest_modport->VpiParent(m);
    const FileContent* orig_fC = orig_modport.second.getFileContent();
    const NodeId orig_nodeId = orig_modport.second.getNodeId();
    orig_fC->populateCoreMembers(orig_nodeId, orig_nodeId, dest_modport);
    modPortMap.emplace(&orig_modport.second, dest_modport);
    dest_modport->VpiName(orig_modport.first);
    VectorOfio_decl* ios = s.MakeIo_declVec();
    for (auto& sig : orig_modport.second.getPorts()) {
      const FileContent* fC = sig.getFileContent();
      io_decl* io = s.MakeIo_decl();
      io->VpiName(sig.getName());
      NodeId id = sig.getNodeId();
      fC->populateCoreMembers(id, id, io);
      if (NodeId Expression = fC->Sibling(id)) {
        m_helper.checkForLoops(true);
        any* exp =
            m_helper.compileExpression(mod, fC, Expression, m_compileDesign,
                                       nullptr, instance, true, true);
        m_helper.checkForLoops(false);
        io->Expr(exp);
      }
      unsigned int direction = UhdmWriter::getVpiDirection(sig.getDirection());
      io->VpiDirection(direction);
      ios->push_back(io);
    }
    dest_modport->Io_decls(ios);
    dest_modports->push_back(dest_modport);
  }
  m->Modports(dest_modports);

  // Cont assigns
  m->Cont_assigns(mod->getContAssigns());
  if (m->Cont_assigns()) {
    for (auto ps : *m->Cont_assigns()) {
      ps->VpiParent(m);
    }
  }

  // Assertions
  if (mod->getAssertions()) {
    m->Assertions(mod->getAssertions());
    for (auto ps : *m->Assertions()) {
      ps->VpiParent(m);
    }
  }

  // Processes
  m->Process(mod->getProcesses());
  if (m->Process()) {
    for (auto ps : *m->Process()) {
      ps->VpiParent(m);
    }
  }

  // Parameters
  if (mod->getParameters()) {
    m->Parameters(mod->getParameters());
    for (auto ps : *m->Parameters()) {
      ps->VpiParent(m);
    }
  }
  // Param_assigns
  if (mod->getParam_assigns()) {
    m->Param_assigns(mod->getParam_assigns());
    for (auto ps : *m->Param_assigns()) {
      ps->VpiParent(m);
    }
  }

  // Function and tasks
  m->Task_funcs(mod->getTask_funcs());
  if (m->Task_funcs()) {
    for (auto tf : *m->Task_funcs()) {
      if (tf->VpiParent() == nullptr) tf->VpiParent(m);
      if (tf->Instance() == nullptr) tf->Instance(m);
    }
  }

  // ClockingBlocks
  for (const auto& ctupple : mod->getClockingBlockMap()) {
    const ClockingBlock& cblock = ctupple.second;
    switch (cblock.getType()) {
      case ClockingBlock::Type::Default: {
        m->Default_clocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Global: {
        m->Global_clocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Regular: {
        VectorOfclocking_block* cblocks = m->Clocking_blocks();
        if (cblocks == nullptr) {
          m->Clocking_blocks(s.MakeClocking_blockVec());
          cblocks = m->Clocking_blocks();
        }
        cblocks->push_back(cblock.getActual());
        break;
      }
    }
  }
}

void UhdmWriter::writeProgram(Program* mod, program* m, Serializer& s,
                              UhdmWriter::ComponentMap& componentMap,
                              UhdmWriter::ModPortMap& modPortMap,
                              ModuleInstance* instance) {
  UhdmWriter::SignalBaseClassMap signalBaseMap;
  UhdmWriter::SignalMap portMap;
  UhdmWriter::SignalMap netMap;
  // Typepecs
  VectorOftypespec* typespecs = s.MakeTypespecVec();
  m->Typespecs(typespecs);
  writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, true);
  for (auto item : mod->getImportedSymbols()) {
    typespecs->push_back(item);
  }
  // Ports
  std::vector<Signal*>& orig_ports = mod->getPorts();
  VectorOfport* dest_ports = s.MakePortVec();
  VectorOfnet* dest_nets = s.MakeNetVec();
  writePorts(orig_ports, m, dest_ports, dest_nets, s, componentMap, modPortMap,
             signalBaseMap, portMap, instance);
  m->Ports(dest_ports);
  // Nets
  std::vector<Signal*>& orig_nets = mod->getSignals();
  writeNets(orig_nets, m, dest_nets, s, signalBaseMap, netMap, portMap,
            instance);
  m->Nets(dest_nets);
  mapLowConns(orig_ports, s, signalBaseMap);
  // Parameters
  if (mod->getParameters()) {
    m->Parameters(mod->getParameters());
    for (auto ps : *m->Parameters()) {
      ps->VpiParent(m);
    }
  }

  // Assertions
  if (mod->getAssertions()) {
    m->Assertions(mod->getAssertions());
    for (auto ps : *m->Assertions()) {
      ps->VpiParent(m);
    }
  }

  // Param_assigns
  if (mod->getParam_assigns()) {
    m->Param_assigns(mod->getParam_assigns());
    for (auto ps : *m->Param_assigns()) {
      ps->VpiParent(m);
    }
  }
  // Classes
  ClassNameClassDefinitionMultiMap& orig_classes = mod->getClassDefinitions();
  VectorOfclass_defn* dest_classes = s.MakeClass_defnVec();
  writeClasses(orig_classes, dest_classes, s, componentMap, m);
  m->Class_defns(dest_classes);
  // Variables
  const DesignComponent::VariableMap& orig_vars = mod->getVariables();
  VectorOfvariables* dest_vars = s.MakeVariablesVec();
  writeVariables(orig_vars, m, dest_vars, s, componentMap);
  m->Variables(dest_vars);

  // Cont assigns
  m->Cont_assigns(mod->getContAssigns());
  if (m->Cont_assigns()) {
    for (auto ps : *m->Cont_assigns()) {
      ps->VpiParent(m);
    }
  }
  // Processes
  m->Process(mod->getProcesses());
  if (m->Process()) {
    for (auto ps : *m->Process()) {
      ps->VpiParent(m);
    }
  }
  m->Task_funcs(mod->getTask_funcs());
  if (m->Task_funcs()) {
    for (auto tf : *m->Task_funcs()) {
      tf->VpiParent(m);
    }
  }

  // ClockingBlocks
  for (const auto& ctupple : mod->getClockingBlockMap()) {
    const ClockingBlock& cblock = ctupple.second;
    switch (cblock.getType()) {
      case ClockingBlock::Type::Default: {
        m->Default_clocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Regular: {
        VectorOfclocking_block* cblocks = m->Clocking_blocks();
        if (cblocks == nullptr) {
          m->Clocking_blocks(s.MakeClocking_blockVec());
          cblocks = m->Clocking_blocks();
        }
        cblocks->push_back(cblock.getActual());
        break;
      }
      default:
        break;
    }
  }
}

bool UhdmWriter::writeElabProgram(Serializer& s, ModuleInstance* instance,
                                  program* m) {
  Netlist* netlist = instance->getNetlist();
  ComponentMap componentMap;
  DesignComponent* mod = instance->getDefinition();
  if (mod) {
    // Let decls
    if (!mod->getLetStmts().empty()) {
      VectorOflet_decl* decls = s.MakeLet_declVec();
      m->Let_decls(decls);
      for (auto stmt : mod->getLetStmts()) {
        decls->push_back((let_decl*)stmt.second->Decl());
      }
    }
    // Typepecs
    VectorOftypespec* typespecs = s.MakeTypespecVec();
    m->Typespecs(typespecs);
    writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, false);
    for (auto item : mod->getImportedSymbols()) {
      typespecs->push_back(item);
    }
    // Assertions
    if (mod->getAssertions()) {
      m->Assertions(mod->getAssertions());
    }
  }
  if (netlist) {
    m->Ports(netlist->ports());
    if (netlist->ports()) {
      for (auto obj : *netlist->ports()) {
        obj->VpiParent(m);
      }
    }
    m->Nets(netlist->nets());
    if (netlist->nets()) {
      for (auto obj : *netlist->nets()) {
        obj->VpiParent(m);
      }
    }
    m->Gen_scope_arrays(netlist->gen_scopes());
    m->Variables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->VpiParent(m);
      }
    }
    m->Array_vars(netlist->array_vars());
    if (netlist->array_vars()) {
      for (auto obj : *netlist->array_vars()) {
        obj->VpiParent(m);
      }
    }
    m->Named_events(netlist->named_events());
    if (netlist->named_events()) {
      for (auto obj : *netlist->named_events()) {
        obj->VpiParent(m);
      }
    }
    m->Array_nets(netlist->array_nets());
    if (netlist->array_nets()) {
      for (auto obj : *netlist->array_nets()) {
        obj->VpiParent(m);
      }
    }

    // Cont assigns
    m->Cont_assigns(mod->getContAssigns());
    if (m->Cont_assigns()) {
      for (auto ps : *m->Cont_assigns()) {
        ps->VpiParent(m);
      }
    }
    // Processes
    m->Process(mod->getProcesses());
    if (m->Process()) {
      for (auto ps : *m->Process()) {
        ps->VpiParent(m);
      }
    }
  }
  if (mod) {
    if (auto from = mod->getTask_funcs()) {
      UHDM::VectorOftask_func* target = m->Task_funcs();
      if (target == nullptr) {
        m->Task_funcs(s.MakeTask_funcVec());
        target = m->Task_funcs();
      }
      for (auto tf : *from) {
        target->push_back(tf);
        if (tf->VpiParent() == nullptr) tf->VpiParent(m);
        if (tf->Instance() == nullptr) tf->Instance(m);
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
          m->Default_clocking(cblock.getActual());
          break;
        }
        case ClockingBlock::Type::Global: {
          // m->Global_clocking(cblock.getActual());
          break;
        }
        case ClockingBlock::Type::Regular: {
          VectorOfclocking_block* cblocks = m->Clocking_blocks();
          if (cblocks == nullptr) {
            m->Clocking_blocks(s.MakeClocking_blockVec());
            cblocks = m->Clocking_blocks();
          }
          cblocks->push_back(cblock.getActual());
          break;
        }
      }
    }
  }

  if (mod) {
    lateTypedefBinding(s, mod, m, componentMap);
    lateBinding(s, mod, m, componentMap);
  }

  return true;
}

class DetectUnsizedConstant final : public VpiListener {
 public:
  DetectUnsizedConstant() {}
  bool unsizedDetected() { return unsized_; }

 private:
  void leaveConstant(const constant* object, vpiHandle handle) final {
    if (object->VpiSize() == -1) unsized_ = true;
  }
  bool unsized_ = false;
};

void UhdmWriter::writeCont_assign(Netlist* netlist, Serializer& s,
                                  DesignComponent* mod, any* m,
                                  std::vector<cont_assign*>* assigns) {
  if (netlist->cont_assigns()) {
    for (auto assign : *netlist->cont_assigns()) {
      const expr* lhs = assign->Lhs();
      const expr* rhs = assign->Rhs();
      const expr* delay = assign->Delay();
      const typespec* tps = lhs->Typespec();
      bool simplified = false;
      bool cloned = false;
      if (delay && delay->UhdmType() == uhdmref_obj) {
        UHDM::any* var = m_helper.bindParameter(
            mod, netlist->getParent(), delay->VpiName(), m_compileDesign, true);
        ElaboratorListener listener(&s, false, true);
        assign = (cont_assign*)UHDM::clone_tree(assign, s, &listener);
        lhs = assign->Lhs();
        rhs = assign->Rhs();
        tps = lhs->Typespec();
        delay = assign->Delay();
        ref_obj* ref = (ref_obj*)delay;
        ref->Actual_group(var);
        cloned = true;
      }

      if (lhs->UhdmType() == uhdmref_obj) {
        UHDM::any* var =
            m_helper.bindVariable(mod, m, lhs->VpiName(), m_compileDesign);
        if (var) {
          if (rhs->UhdmType() == uhdmoperation) {
            if (cloned == false) {
              ElaboratorListener listener(&s, false, true);
              assign = (cont_assign*)UHDM::clone_tree(assign, s, &listener);
              lhs = assign->Lhs();
              rhs = assign->Rhs();
              delay = assign->Delay();
              tps = lhs->Typespec();
            }
            ref_obj* ref = (ref_obj*)lhs;
            ref->Actual_group(var);
            cloned = true;
          }

          if (expr* exp = any_cast<expr*>(var)) {
            if (const typespec* temp = exp->Typespec()) {
              tps = temp;
            }
          }
        }
      }
      if (tps) {
        UHDM::ExprEval eval(true);
        expr* tmp = eval.flattenPatternAssignments(s, tps, (expr*)rhs);
        if (tmp->UhdmType() == uhdmoperation) {
          if (cloned == false) {
            ElaboratorListener listener(&s, false, true);
            assign = (cont_assign*)UHDM::clone_tree(assign, s, &listener);
            lhs = assign->Lhs();
            rhs = assign->Rhs();
            delay = assign->Delay();
            tps = lhs->Typespec();
            cloned = true;
          }
          ((operation*)rhs)->Operands(((operation*)tmp)->Operands());
          operation* op = (operation*)rhs;
          int opType = op->VpiOpType();
          if (opType == vpiAssignmentPatternOp || opType == vpiConditionOp) {
            if (m_helper.substituteAssignedValue(rhs, m_compileDesign)) {
              rhs = m_helper.expandPatternAssignment(tps, (UHDM::expr*)rhs, mod,
                                                     m_compileDesign,
                                                     netlist->getParent());
            }
          }
          rhs = (UHDM::expr*)m_helper.defaultPatternAssignment(
              tps, (UHDM::expr*)rhs, mod, m_compileDesign,
              netlist->getParent());

          assign->Rhs((UHDM::expr*)rhs);
          m_helper.reorderAssignmentPattern(mod, lhs, (UHDM::expr*)rhs,
                                            m_compileDesign,
                                            netlist->getParent(), 0);
          simplified = true;
        }
      } else if (rhs->UhdmType() == uhdmoperation) {
        operation* op = (operation*)rhs;
        if (const typespec* tps = op->Typespec()) {
          UHDM::ExprEval eval(true);
          expr* tmp = eval.flattenPatternAssignments(s, tps, (expr*)rhs);
          if (tmp->UhdmType() == uhdmoperation) {
            if (cloned == false) {
              ElaboratorListener listener(&s, false, true);
              assign = (cont_assign*)UHDM::clone_tree(assign, s, &listener);
              lhs = assign->Lhs();
              rhs = assign->Rhs();
              delay = assign->Delay();
              tps = lhs->Typespec();
              cloned = true;
            }
            ((operation*)rhs)->Operands(((operation*)tmp)->Operands());
            simplified = true;
          }
        }
      }
      if (simplified == false) {
        bool invalidValue = false;
        FileSystem* const fileSystem = FileSystem::getInstance();
        m_helper.checkForLoops(true);
        any* res = m_helper.reduceExpr(
            (expr*)rhs, invalidValue, mod, m_compileDesign,
            netlist->getParent(),
            fileSystem->toPathId(
                rhs->VpiFile(),
                m_compileDesign->getCompiler()->getSymbolTable()),
            rhs->VpiLineNo(), assign, true);
        m_helper.checkForLoops(false);
        if (invalidValue == false) {
          if (res && (res->UhdmType() == uhdmconstant)) {
            if (cloned == false) {
              ElaboratorListener listener(&s, false, true);
              assign = (cont_assign*)UHDM::clone_tree(assign, s, &listener);
              lhs = assign->Lhs();
              cloned = true;
              res = m_helper.adjustSize(tps, mod, m_compileDesign,
                                        netlist->getParent(), (constant*)res,
                                        true);
              res->VpiParent(assign);
            }
            assign->Rhs((constant*)res);
          }
        }
      }
      if (simplified == false && cloned == false) {
        DetectUnsizedConstant detector;
        vpiHandle h_rhs = NewVpiHandle(rhs);
        detector.listenAny(h_rhs);
        vpi_free_object(h_rhs);
        if (detector.unsizedDetected()) {
          ElaboratorListener listener(&s, false, true);
          assign = (cont_assign*)UHDM::clone_tree(assign, s, &listener);
          cloned = true;
        }
      }
      assigns->push_back(assign);
    }
  }
}

bool UhdmWriter::writeElabGenScope(Serializer& s, ModuleInstance* instance,
                                   gen_scope* m, ExprBuilder& exprBuilder) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  Netlist* netlist = instance->getNetlist();
  ComponentMap componentMap;
  ModuleDefinition* mod =
      valuedcomponenti_cast<ModuleDefinition*>(instance->getDefinition());
  if (mod) {
    // Let decls
    if (!mod->getLetStmts().empty()) {
      VectorOflet_decl* decls = s.MakeLet_declVec();
      m->Let_decls(decls);
      for (auto stmt : mod->getLetStmts()) {
        decls->push_back((let_decl*)stmt.second->Decl());
      }
    }
    // Typepecs
    VectorOftypespec* typespecs = s.MakeTypespecVec();
    m->Typespecs(typespecs);
    writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, true);
    for (auto item : mod->getImportedSymbols()) {
      typespecs->push_back(item);
    }
    // System elab tasks
    m->Elab_tasks((std::vector<UHDM::tf_call*>*)&mod->getElabSysCalls());
    // Assertions
    if (mod->getAssertions()) {
      m->Assertions(mod->getAssertions());
    }
  }
  if (netlist) {
    m->Nets(netlist->nets());
    if (netlist->nets()) {
      for (auto obj : *netlist->nets()) {
        obj->VpiParent(m);
      }
    }

    if (netlist->cont_assigns()) {
      std::vector<cont_assign*>* assigns = m->Cont_assigns();
      if (assigns == nullptr) {
        m->Cont_assigns(s.MakeCont_assignVec());
        assigns = m->Cont_assigns();
      }
      writeCont_assign(netlist, s, mod, m, assigns);
      for (auto obj : *assigns) {
        obj->VpiParent(m);
      }
    }

    // Processes
    m->Process(netlist->process_stmts());
    if (m->Process()) {
      for (auto ps : *m->Process()) {
        ps->VpiParent(m);
      }
    }

    std::vector<gen_scope_array*>* gen_scope_arrays = netlist->gen_scopes();
    if (gen_scope_arrays) {
      writeElabParameters(s, instance, m, exprBuilder);

      // Loop indexes
      for (auto& param : instance->getMappedValues()) {
        const std::string_view name = param.first;
        Value* val = param.second.first;
        VectorOfany* params = nullptr;
        params = m->Parameters();
        if (params == nullptr) {
          params = s.MakeAnyVec();
        }
        m->Parameters(params);
        bool found = false;
        for (auto p : *params) {
          if (p->VpiName() == name) {
            found = true;
            break;
          }
        }
        if (!found) {
          parameter* p = s.MakeParameter();
          p->VpiName(name);
          if (val && val->isValid()) p->VpiValue(val->uhdmValue());
          p->VpiFile(fileSystem->toPath(instance->getFileId()));
          p->VpiLineNo(param.second.second);
          p->VpiParent(m);
          p->VpiLocalParam(true);
          int_typespec* ts = s.MakeInt_typespec();
          p->Typespec(ts);
          params->push_back(p);
        }
      }
    }

    m->Variables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->VpiParent(m);
      }
    }
    m->Array_vars(netlist->array_vars());
    if (netlist->array_vars()) {
      for (auto obj : *netlist->array_vars()) {
        obj->VpiParent(m);
      }
    }
    m->Named_events(netlist->named_events());
    if (netlist->named_events()) {
      for (auto obj : *netlist->named_events()) {
        obj->VpiParent(m);
      }
    }
    m->Array_nets(netlist->array_nets());
    if (netlist->array_nets()) {
      for (auto obj : *netlist->array_nets()) {
        obj->VpiParent(m);
      }
    }
  }

  DesignComponent* def = instance->getDefinition();
  if (def->getTask_funcs()) {
    // Function and tasks
    UHDM::VectorOftask_func* target = m->Task_funcs();
    if (target == nullptr) {
      m->Task_funcs(s.MakeTask_funcVec());
      target = m->Task_funcs();
    }
    for (auto tf : *def->getTask_funcs()) {
      target->push_back(tf);
      if (tf->VpiParent() == nullptr) tf->VpiParent(m);
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
        VectorOfclocking_block* cblocks = m->Clocking_blocks();
        if (cblocks == nullptr) {
          m->Clocking_blocks(s.MakeClocking_blockVec());
          cblocks = m->Clocking_blocks();
        }
        cblocks->push_back(cblock.getActual());
        break;
      }
      default:
        break;
    }
  }

  if (mod) {
    lateTypedefBinding(s, mod, m, componentMap);
    lateBinding(s, mod, m, componentMap);
  }

  return true;
}

void UhdmWriter::lateTypedefBinding(UHDM::Serializer& s, DesignComponent* mod,
                                    scope* m, ComponentMap& componentMap) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  for (UHDM::any* var : mod->getLateTypedefBinding()) {
    const typespec* orig = nullptr;
    if (expr* ex = any_cast<expr*>(var)) {
      orig = ex->Typespec();
    } else if (typespec_member* ex = any_cast<typespec_member*>(var)) {
      orig = ex->Typespec();
    } else if (parameter* ex = any_cast<parameter*>(var)) {
      orig = ex->Typespec();
    } else if (type_parameter* ex = any_cast<type_parameter*>(var)) {
      orig = ex->Typespec();
    } else if (io_decl* ex = any_cast<io_decl*>(var)) {
      orig = ex->Typespec();
    }
    if (orig && (orig->UhdmType() == uhdmunsupported_typespec)) {
      std::string_view name = StringUtils::trim(orig->VpiName());
      const typespec* tps = nullptr;
      bool found = false;

      if (name.find("::") != std::string::npos) {
        std::vector<std::string_view> res;
        StringUtils::tokenizeMulti(name, "::", res);
        if (res.size() > 1) {
          const std::string_view packName = res[0];
          const std::string_view typeName = res[1];
          Package* pack =
              m_compileDesign->getCompiler()->getDesign()->getPackage(packName);
          if (pack) {
            const auto& itr = componentMap.find(pack);
            if (itr != componentMap.end()) {
              package* p = (package*)itr->second;
              if (p->Typespecs()) {
                for (auto n : *p->Typespecs()) {
                  if (n->VpiName() == typeName) {
                    found = true;
                    tps = n;
                    break;
                  }
                  const std::string pname =
                      StrCat(m->VpiName(), "::", typeName);
                  if (n->VpiName() == pname) {
                    found = true;
                    tps = n;
                    break;
                  }
                }
              }
            }
          }
        }
      }

      const any* parent = var->VpiParent();
      while (parent) {
        if (parent->UhdmType() == uhdmfunction) {
          function* func = (function*)parent;
          if (parent->VpiName() == name) {
            if (const any* ret = func->Return()) {
              variables* var = (variables*)ret;
              found = true;
              tps = var->Typespec();
            }
            break;
          }
          if (auto decls = func->Io_decls()) {
            for (auto decl : *decls) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                tps = decl->Typespec();
                break;
              }
            }
          }
          if (auto vars = func->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                tps = decl->Typespec();
                break;
              }
            }
          }
          if (auto params = func->Parameters()) {
            for (auto decl : *params) {
              if (decl->VpiName() == name) {
                found = true;
                if (decl->UhdmType() == uhdmparameter) {
                  tps = ((parameter*)decl)->Typespec();
                } else {
                  tps = ((type_parameter*)decl)->Typespec();
                }
                break;
              }
            }
          }
          if (const UHDM::instance* inst = func->Instance()) {
            if (inst->UhdmType() == uhdmpackage) {
              package* pack = (package*)inst;
              if (pack->Variables()) {
                for (auto n : *pack->Variables()) {
                  if (n->VpiName() == name) {
                    if (n->UhdmType() == uhdmref_var) continue;
                    if (n->UhdmType() == uhdmref_obj) continue;
                    found = true;
                    tps = n->Typespec();
                    break;
                  }
                  const std::string pname = StrCat(m->VpiName(), "::", name);
                  if (n->VpiName() == pname) {
                    if (n->UhdmType() == uhdmref_var) continue;
                    if (n->UhdmType() == uhdmref_obj) continue;
                    found = true;
                    tps = n->Typespec();
                    break;
                  }
                }
              }
            }
          }
          if (found) break;
        } else if (parent->UhdmType() == uhdmtask) {
          task* ta = (task*)parent;
          if (auto decls = ta->Io_decls()) {
            for (auto decl : *decls) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                tps = decl->Typespec();
                break;
              }
            }
          }
          if (auto vars = ta->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                tps = decl->Typespec();
                break;
              }
            }
          }
          if (const UHDM::instance* inst = ta->Instance()) {
            if (inst->UhdmType() == uhdmpackage) {
              package* pack = (package*)inst;
              if (pack->Variables()) {
                for (auto n : *pack->Variables()) {
                  if (n->VpiName() == name) {
                    if (n->UhdmType() == uhdmref_var) continue;
                    if (n->UhdmType() == uhdmref_obj) continue;
                    found = true;
                    tps = n->Typespec();
                    break;
                  }
                  const std::string pname = StrCat(m->VpiName(), "::", name);
                  if (n->VpiName() == pname) {
                    if (n->UhdmType() == uhdmref_var) continue;
                    if (n->UhdmType() == uhdmref_obj) continue;
                    found = true;
                    tps = n->Typespec();
                    break;
                  }
                }
              }
            }
          }
          if (found) break;
        } else if (parent->UhdmType() == uhdmfor_stmt) {
          for_stmt* f = (for_stmt*)parent;
          VectorOfany* inits = f->VpiForInitStmts();
          if (inits) {
            for (auto init : *inits) {
              if (init->UhdmType() == uhdmassign_stmt) {
                assign_stmt* as = (assign_stmt*)init;
                const expr* lhs = as->Lhs();
                if (lhs->VpiName() == name) {
                  if (lhs->UhdmType() == uhdmref_var) continue;
                  if (lhs->UhdmType() == uhdmref_obj) continue;
                  found = true;
                  tps = lhs->Typespec();
                  break;
                }
              }
            }
          }
        } else if (parent->UhdmType() == uhdmforeach_stmt) {
          foreach_stmt* f = (foreach_stmt*)parent;
          VectorOfany* vars = f->VpiLoopVars();
          if (vars) {
            for (auto var : *vars) {
              if (var->VpiName() == name) {
                if (var->UhdmType() == uhdmref_var) continue;
                if (var->UhdmType() == uhdmref_obj) continue;
                found = true;
                tps = ((variables*)var)->Typespec();
                break;
              }
            }
          }
        } else if (parent->UhdmType() == uhdmmodule_inst) {
          module_inst* m = (module_inst*)parent;
          if (auto vars = m->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                tps = decl->Typespec();
                break;
              }
            }
          }
          if (found) break;
          if (auto params = m->Parameters()) {
            for (auto decl : *params) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmparameter) {
                  tps = ((parameter*)decl)->Typespec();
                  found = true;
                } else {
                  tps = ((type_parameter*)decl)->Typespec();
                  found = true;
                }
                break;
              }
            }
          }
          if (found) break;
          VectorOfport* ports = m->Ports();
          if (ports) {
            for (auto port : *ports) {
              if (port->VpiName() == name) {
                found = true;
                tps = port->Typespec();
                break;
              }
            }
          }
          if (found) break;
          VectorOfnet* nets = m->Nets();
          if (nets) {
            for (auto net : *nets) {
              if (net->VpiName() == name) {
                found = true;
                tps = net->Typespec();
              }
            }
          }
          if (found) break;
        } else if (parent->UhdmType() == uhdmbegin) {
          begin* b = (begin*)parent;
          if (auto vars = b->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                tps = decl->Typespec();
                break;
              }
            }
          }
          if (found) break;
          if (auto params = b->Parameters()) {
            for (auto decl : *params) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmparameter) {
                  tps = ((parameter*)decl)->Typespec();
                } else {
                  tps = ((type_parameter*)decl)->Typespec();
                }
                break;
              }
            }
          }
          if (found) break;
          VectorOfany* stmts = b->Stmts();
          if (stmts) {
            for (auto init : *stmts) {
              if (init->UhdmType() == uhdmassign_stmt) {
                assign_stmt* as = (assign_stmt*)init;
                const expr* lhs = as->Lhs();
                if (lhs->VpiName() == name) {
                  if (lhs->UhdmType() == uhdmref_var) continue;
                  if (lhs->UhdmType() == uhdmref_obj) continue;
                  found = true;
                  tps = lhs->Typespec();
                  break;
                }
              }
            }
          }
        } else if (parent->UhdmType() == uhdmnamed_begin) {
          named_begin* b = (named_begin*)parent;
          if (auto vars = b->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                tps = decl->Typespec();
                break;
              }
            }
          }
          if (found) break;
          if (auto params = b->Parameters()) {
            for (auto decl : *params) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmparameter) {
                  tps = ((parameter*)decl)->Typespec();
                } else {
                  tps = ((type_parameter*)decl)->Typespec();
                }
                break;
              }
            }
          }
          if (found) break;
          VectorOfany* stmts = b->Stmts();
          if (stmts) {
            for (auto init : *stmts) {
              if (init->UhdmType() == uhdmassign_stmt) {
                assign_stmt* as = (assign_stmt*)init;
                const expr* lhs = as->Lhs();
                if (lhs->VpiName() == name) {
                  if (lhs->UhdmType() == uhdmref_var) continue;
                  if (lhs->UhdmType() == uhdmref_obj) continue;
                  found = true;
                  tps = lhs->Typespec();
                  break;
                }
              }
            }
          }
        } else if (parent->UhdmType() == uhdmfork_stmt) {
          fork_stmt* b = (fork_stmt*)parent;
          if (auto vars = b->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                tps = decl->Typespec();
                break;
              }
            }
          }
          if (found) break;
          if (auto params = b->Parameters()) {
            for (auto decl : *params) {
              if (decl->VpiName() == name) {
                found = true;
                if (decl->UhdmType() == uhdmparameter) {
                  tps = ((parameter*)decl)->Typespec();
                } else {
                  tps = ((type_parameter*)decl)->Typespec();
                }
                break;
              }
            }
          }
          if (found) break;
          VectorOfany* stmts = b->Stmts();
          if (stmts) {
            for (auto init : *stmts) {
              if (init->UhdmType() == uhdmassign_stmt) {
                assign_stmt* as = (assign_stmt*)init;
                const expr* lhs = as->Lhs();
                if (lhs->VpiName() == name) {
                  if (lhs->UhdmType() == uhdmref_var) continue;
                  if (lhs->UhdmType() == uhdmref_obj) continue;
                  found = true;
                  tps = lhs->Typespec();
                  break;
                }
              }
            }
          }
        } else if (parent->UhdmType() == uhdmnamed_fork) {
          named_fork* b = (named_fork*)parent;
          if (auto vars = b->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                tps = decl->Typespec();
                break;
              }
            }
          }
          if (found) break;
          if (auto params = b->Parameters()) {
            for (auto decl : *params) {
              if (decl->VpiName() == name) {
                found = true;
                if (decl->UhdmType() == uhdmparameter) {
                  tps = ((parameter*)decl)->Typespec();
                } else {
                  tps = ((type_parameter*)decl)->Typespec();
                }
                break;
              }
            }
          }
          if (found) break;
          VectorOfany* stmts = b->Stmts();
          if (stmts) {
            for (auto init : *stmts) {
              if (init->UhdmType() == uhdmassign_stmt) {
                assign_stmt* as = (assign_stmt*)init;
                const expr* lhs = as->Lhs();
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                if (lhs->VpiName() == name) {
                  found = true;
                  tps = lhs->Typespec();
                  break;
                }
              }
            }
          }
        }
        if (found) break;
        parent = parent->VpiParent();
      }

      // Foreach-loop, implicit loop var declaration fixup
      if (found == false) {
        const any* parent = var->VpiParent();
        if (parent && (parent->UhdmType() == uhdmforeach_stmt)) {
          foreach_stmt* for_stmt = (foreach_stmt*)parent;
          if (VectorOfany* loopvars = for_stmt->VpiLoopVars()) {
            for (any*& tmp : *loopvars) {
              if (tmp->VpiName() == name) {
                if (var->UhdmType() == uhdmref_var) {
                  ref_var* ref = (ref_var*)var;
                  const typespec* tp = ref->Typespec();
                  if (tp && tp->UhdmType() == uhdmunsupported_typespec) {
                    const typespec* indexTypespec = nullptr;
                    if (for_stmt->Variables()) {
                      for (auto var : *for_stmt->Variables()) {
                        if (var->UhdmType() == uhdmhier_path) {
                          PathId parentFileId = fileSystem->toPathId(
                              parent->VpiFile(),
                              m_compileDesign->getCompiler()->getSymbolTable());
                          bool invalidValue = false;
                          indexTypespec = (typespec*)m_helper.decodeHierPath(
                              (hier_path*)var, invalidValue, mod,
                              m_compileDesign, nullptr, parentFileId,
                              parent->VpiLineNo(), (any*)parent, true,
                              true /*mute for now*/, true);
                        }
                      }
                    } else if (const variables* var = for_stmt->Variable()) {
                      if (var->UhdmType() == uhdmhier_path) {
                        PathId parentFileId = fileSystem->toPathId(
                            parent->VpiFile(),
                            m_compileDesign->getCompiler()->getSymbolTable());
                        bool invalidValue = false;
                        indexTypespec = (typespec*)m_helper.decodeHierPath(
                            (hier_path*)var, invalidValue, mod, m_compileDesign,
                            nullptr, parentFileId, parent->VpiLineNo(),
                            (any*)parent, true, true /*mute for now*/, true);
                      } else if (var->UhdmType() == uhdmref_var) {
                        bool invalidValue = false;
                        hier_path* path = s.MakeHier_path();
                        VectorOfany* elems = s.MakeAnyVec();
                        path->Path_elems(elems);
                        ref_obj* ref = s.MakeRef_obj();
                        elems->push_back(ref);
                        ref->VpiName(var->VpiName());
                        path->VpiFullName(var->VpiName());
                        PathId parentFileId = fileSystem->toPathId(
                            parent->VpiFile(),
                            m_compileDesign->getCompiler()->getSymbolTable());
                        indexTypespec = (typespec*)m_helper.decodeHierPath(
                            path, invalidValue, mod, m_compileDesign, nullptr,
                            parentFileId, parent->VpiLineNo(), (any*)parent,
                            true, true /*mute for now*/, true);
                      }
                    }
                    variables* swapVar = nullptr;
                    if (indexTypespec) {
                      swapVar = m_helper.getSimpleVarFromTypespec(
                          (typespec*)indexTypespec, nullptr, m_compileDesign);
                    } else {
                      int_var* ivar = s.MakeInt_var();
                      ivar->Typespec(s.MakeInt_typespec());
                      swapVar = ivar;
                    }
                    if (swapVar) {
                      swapVar->VpiName(ref->VpiName());
                      swapVar->VpiFile(ref->VpiFile());
                      swapVar->VpiLineNo(ref->VpiLineNo());
                      swapVar->VpiColumnNo(ref->VpiColumnNo());
                      swapVar->VpiEndLineNo(ref->VpiEndLineNo());
                      swapVar->VpiEndColumnNo(ref->VpiEndColumnNo());
                      tmp = swapVar;
                    }
                    break;
                  }
                }
              }
            }
          }
        }
      }

      if ((name.empty()) && (found == false)) {
        // Port .op({\op[1] ,\op[0] })
        if (operation* op = any_cast<operation*>(var)) {
          const typespec* baseTypespec = nullptr;
          uint64_t size = 0;
          for (any* oper : *op->Operands()) {
            if (oper->UhdmType() == uhdmref_obj) {
              ref_obj* ref = (ref_obj*)oper;
              const any* actual = ref->Actual_group();
              if (const expr* ex = any_cast<const expr*>(actual)) {
                const typespec* tps = ex->Typespec();
                if (tps) {
                  baseTypespec = tps;
                }
              }
            }
            size++;
          }
          if (baseTypespec) {
            array_typespec* arr = s.MakeArray_typespec();
            tps = arr;
            found = true;
            arr->Elem_typespec((typespec*)baseTypespec);
            VectorOfrange* ranges = s.MakeRangeVec();
            range* ra = s.MakeRange();
            ranges->push_back(ra);
            constant* l = s.MakeConstant();
            l->VpiValue("UINT:" + std::to_string(size - 1));
            ra->Left_expr(l);
            constant* r = s.MakeConstant();
            r->VpiValue("UINT:0");
            ra->Right_expr(r);
            arr->Ranges(ranges);
          }
        }
      }
      if (found == true) {
        if (expr* ex = any_cast<expr*>(var)) {
          ex->Typespec((typespec*)tps);
        } else if (typespec_member* ex = any_cast<typespec_member*>(var)) {
          ex->Typespec((typespec*)tps);
        } else if (parameter* ex = any_cast<parameter*>(var)) {
          ex->Typespec((typespec*)tps);
        } else if (type_parameter* ex = any_cast<type_parameter*>(var)) {
          ex->Typespec((typespec*)tps);
        } else if (io_decl* ex = any_cast<io_decl*>(var)) {
          ex->Typespec((typespec*)tps);
        }
      }
    }
  }
  for (const auto& itr : mod->getLateResolutionFunction()) {
    std::string_view funcName = itr.first;
    std::pair<task_func*, DesignComponent*> ret =
        m_helper.getTaskFunc(funcName, mod, m_compileDesign, nullptr, nullptr);
    task_func* tf = ret.first;
    function* resolution_func = any_cast<function*>(tf);
    typespec* ts = itr.second;
    if (resolution_func) {
      if (ts->UhdmType() == uhdmbit_typespec) {
        bit_typespec* btps = (bit_typespec*)ts;
        btps->Resolution_func(resolution_func);
      } else if (ts->UhdmType() == uhdmlogic_typespec) {
        logic_typespec* btps = (logic_typespec*)ts;
        btps->Resolution_func(resolution_func);
      } else if (ts->UhdmType() == uhdmstruct_typespec) {
        struct_typespec* btps = (struct_typespec*)ts;
        btps->Resolution_func(resolution_func);
      } else if (ts->UhdmType() == uhdmreal_typespec) {
        real_typespec* btps = (real_typespec*)ts;
        btps->Resolution_func(resolution_func);
      } else if (ts->UhdmType() == uhdmarray_typespec) {
        array_typespec* btps = (array_typespec*)ts;
        btps->Resolution_func(resolution_func);
      } else if (ts->UhdmType() == uhdmpacked_array_typespec) {
        packed_array_typespec* btps = (packed_array_typespec*)ts;
        btps->Resolution_func(resolution_func);
      }
    }
  }
}

void UhdmWriter::lateBinding(UHDM::Serializer& s, DesignComponent* mod,
                             scope* m, ComponentMap& componentMap) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  for (UHDM::ref_obj* ref : mod->getLateBinding()) {
    if (ref->Actual_group()) continue;
    std::string_view name = ref->VpiName();
    name = StringUtils::trim(name);
    if (name.find("::") != std::string::npos) {
      std::vector<std::string_view> res;
      StringUtils::tokenizeMulti(name, "::", res);
      if (res.size() > 1) {
        const std::string_view packName = res[0];
        const std::string_view typeName = res[1];
        Package* pack =
            m_compileDesign->getCompiler()->getDesign()->getPackage(packName);
        if (pack) {
          const auto& itr = componentMap.find(pack);
          if (itr != componentMap.end()) {
            package* p = (package*)itr->second;
            if (p->Parameters()) {
              for (auto n : *p->Parameters()) {
                if (n->VpiName() == typeName) {
                  if (n->UhdmType() == uhdmref_var) continue;
                  if (n->UhdmType() == uhdmref_obj) continue;
                  ref->Actual_group(n);
                  break;
                }
                const std::string pname = StrCat(m->VpiName(), "::", typeName);
                if (n->VpiName() == pname) {
                  if (n->UhdmType() == uhdmref_var) continue;
                  if (n->UhdmType() == uhdmref_obj) continue;
                  ref->Actual_group(n);
                  break;
                }
              }
            }
            if (p->Variables()) {
              for (auto n : *p->Variables()) {
                if (n->VpiName() == typeName) {
                  if (n->UhdmType() == uhdmref_var) continue;
                  if (n->UhdmType() == uhdmref_obj) continue;
                  ref->Actual_group(n);
                  break;
                }
                const std::string pname = StrCat(m->VpiName(), "::", typeName);
                if (n->VpiName() == pname) {
                  if (n->UhdmType() == uhdmref_var) continue;
                  if (n->UhdmType() == uhdmref_obj) continue;
                  ref->Actual_group(n);
                  break;
                }
              }
            }
          }
        }
      }

      continue;
    }

    const any* parent = ref->VpiParent();
    while (parent) {
      if (parent->UhdmType() == uhdmfunction) {
        function* func = (function*)parent;
        if (parent->VpiName() == name) {
          if (const any* ret = func->Return()) {
            ElaboratorListener listener(&s, false, true);
            any* pclone = UHDM::clone_tree(ret, s, &listener);
            variables* var = (variables*)pclone;
            var->VpiName(name);
            ref->Actual_group(pclone);
          }
          break;
        }
        if (auto decls = func->Io_decls()) {
          for (auto decl : *decls) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (auto vars = func->Variables()) {
          for (auto decl : *vars) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (auto params = func->Parameters()) {
          for (auto decl : *params) {
            if (decl->VpiName() == name) {
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (const UHDM::instance* inst = func->Instance()) {
          if (inst->UhdmType() == uhdmpackage) {
            package* pack = (package*)inst;
            if (pack->Variables()) {
              for (auto n : *pack->Variables()) {
                if (n->VpiName() == name) {
                  if (n->UhdmType() == uhdmref_var) continue;
                  if (n->UhdmType() == uhdmref_obj) continue;
                  ref->Actual_group(n);
                  break;
                }
                const std::string pname = StrCat(m->VpiName(), "::", name);
                if (n->VpiName() == pname) {
                  if (n->UhdmType() == uhdmref_var) continue;
                  if (n->UhdmType() == uhdmref_obj) continue;
                  ref->Actual_group(n);
                  break;
                }
              }
            }
          }
        }
        if (ref->Actual_group()) break;
      } else if (parent->UhdmType() == uhdmtask) {
        task* ta = (task*)parent;
        if (auto decls = ta->Io_decls()) {
          for (auto decl : *decls) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (auto vars = ta->Variables()) {
          for (auto decl : *vars) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (const UHDM::instance* inst = ta->Instance()) {
          if (inst->UhdmType() == uhdmpackage) {
            package* pack = (package*)inst;
            if (pack->Variables()) {
              for (auto n : *pack->Variables()) {
                if (n->VpiName() == name) {
                  if (n->UhdmType() == uhdmref_var) continue;
                  if (n->UhdmType() == uhdmref_obj) continue;
                  ref->Actual_group(n);
                  break;
                }
                const std::string pname = StrCat(m->VpiName(), "::", name);
                if (n->VpiName() == pname) {
                  if (n->UhdmType() == uhdmref_var) continue;
                  if (n->UhdmType() == uhdmref_obj) continue;
                  ref->Actual_group(n);
                  break;
                }
              }
            }
          }
        }
        if (ref->Actual_group()) break;
      } else if (parent->UhdmType() == uhdmfor_stmt) {
        for_stmt* f = (for_stmt*)parent;
        VectorOfany* inits = f->VpiForInitStmts();
        if (inits) {
          for (auto init : *inits) {
            if (init->UhdmType() == uhdmassign_stmt) {
              assign_stmt* as = (assign_stmt*)init;
              const expr* lhs = as->Lhs();
              if (lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            }
          }
        }
      } else if (parent->UhdmType() == uhdmforeach_stmt) {
        foreach_stmt* f = (foreach_stmt*)parent;
        VectorOfany* vars = f->VpiLoopVars();
        if (vars) {
          for (auto var : *vars) {
            if (var->VpiName() == name) {
              if (var->UhdmType() == uhdmref_var) continue;
              if (var->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group((expr*)var);
              break;
            }
          }
        }
      } else if (parent->UhdmType() == uhdmbegin) {
        begin* b = (begin*)parent;
        if (auto vars = b->Variables()) {
          for (auto decl : *vars) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        if (auto params = b->Parameters()) {
          for (auto decl : *params) {
            if (decl->VpiName() == name) {
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        VectorOfany* stmts = b->Stmts();
        if (stmts) {
          for (auto init : *stmts) {
            if (init->UhdmType() == uhdmassign_stmt) {
              assign_stmt* as = (assign_stmt*)init;
              const expr* lhs = as->Lhs();
              if (lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            }
          }
        }
      } else if (parent->UhdmType() == uhdmnamed_begin) {
        named_begin* b = (named_begin*)parent;
        if (auto vars = b->Variables()) {
          for (auto decl : *vars) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        if (auto params = b->Parameters()) {
          for (auto decl : *params) {
            if (decl->VpiName() == name) {
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        VectorOfany* stmts = b->Stmts();
        if (stmts) {
          for (auto init : *stmts) {
            if (init->UhdmType() == uhdmassign_stmt) {
              assign_stmt* as = (assign_stmt*)init;
              const expr* lhs = as->Lhs();
              if (lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            }
          }
        }
      } else if (parent->UhdmType() == uhdmfork_stmt) {
        fork_stmt* b = (fork_stmt*)parent;
        if (auto vars = b->Variables()) {
          for (auto decl : *vars) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        if (auto params = b->Parameters()) {
          for (auto decl : *params) {
            if (decl->VpiName() == name) {
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        VectorOfany* stmts = b->Stmts();
        if (stmts) {
          for (auto init : *stmts) {
            if (init->UhdmType() == uhdmassign_stmt) {
              assign_stmt* as = (assign_stmt*)init;
              const expr* lhs = as->Lhs();
              if (lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            }
          }
        }
      } else if (parent->UhdmType() == uhdmnamed_fork) {
        named_fork* b = (named_fork*)parent;
        if (auto vars = b->Variables()) {
          for (auto decl : *vars) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        if (auto params = b->Parameters()) {
          for (auto decl : *params) {
            if (decl->VpiName() == name) {
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        VectorOfany* stmts = b->Stmts();
        if (stmts) {
          for (auto init : *stmts) {
            if (init->UhdmType() == uhdmassign_stmt) {
              assign_stmt* as = (assign_stmt*)init;
              const expr* lhs = as->Lhs();
              if (lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            }
          }
        }
      }
      if (ref->Actual_group()) break;
      parent = parent->VpiParent();
    }
    if (ref->Actual_group()) continue;

    if (m->UhdmType() == uhdmmodule_inst ||
        m->UhdmType() == uhdminterface_inst || m->UhdmType() == uhdmprogram) {
      instance* inst = (instance*)m;
      if (inst->Nets()) {
        for (auto n : *inst->Nets()) {
          if (n->VpiName() == name) {
            ref->Actual_group(n);
            break;
          }
        }
        if (ref->Actual_group()) continue;
      }
      if (inst->Array_nets()) {
        for (auto n : *inst->Array_nets()) {
          if (n->VpiName() == name) {
            ref->Actual_group(n);
            break;
          }
        }
        if (ref->Actual_group()) continue;
      }
    }
    if (m->Variables()) {
      for (auto n : *m->Variables()) {
        if (n->VpiName() == name) {
          ref->Actual_group(n);
          break;
        }
        const std::string pname = StrCat(m->VpiName(), "::", name);
        if (n->VpiName() == pname) {
          ref->Actual_group(n);
          break;
        }
      }
      if (ref->Actual_group()) continue;
    }

    if (m->Param_assigns()) {
      bool isParam = false;
      for (auto p : *m->Param_assigns()) {
        const any* lhs = p->Lhs();
        if (lhs->VpiName() == name) {
          // Do not bind blindly here, let the uhdmelab do this correctly
          // ref->Actual_group((any*)p->Rhs());
          isParam = true;
          break;
        }
      }
      if (isParam) continue;
    }
    if (m->Parameters()) {
      bool isParam = false;
      for (auto p : *m->Parameters()) {
        if (p->VpiName() == name) {
          isParam = true;
          break;
        }
      }
      if (isParam) continue;
    }

    if (m->Typespecs()) {
      bool isTypespec = false;
      std::vector<std::string> importedPackages;
      for (auto n : *m->Typespecs()) {
        if (n->UhdmType() == uhdmimport_typespec) {
          importedPackages.emplace_back(n->VpiName());
        }
      }

      for (auto n : *m->Typespecs()) {
        if (n->UhdmType() == uhdmenum_typespec) {
          enum_typespec* tps = any_cast<enum_typespec*>(n);
          if (tps && tps->Enum_consts()) {
            for (auto c : *tps->Enum_consts()) {
              if (c->VpiName() == name) {
                ref->Actual_group(c);
                break;
              }
            }
          }
        }
        for (const auto& imp : importedPackages) {
          if (n->VpiName() == StrCat(imp, "::", name)) {
            isTypespec = true;
            break;
          }
        }
        if (n->VpiName() == name) {
          isTypespec = true;
          break;
        }
        if (ref->Actual_group()) break;
      }
      if (isTypespec) continue;
      if (ref->Actual_group()) continue;
    }
    const FileContent* fC = mod->getFileContents()[0];
    for (const auto& td : fC->getTypeDefMap()) {
      const DataType* dt = td.second;
      while (dt) {
        typespec* n = dt->getTypespec();
        if (n && (n->UhdmType() == uhdmenum_typespec)) {
          enum_typespec* tps = any_cast<enum_typespec*>(n);
          if (tps && tps->Enum_consts()) {
            for (auto c : *tps->Enum_consts()) {
              if (c->VpiName() == name) {
                ref->Actual_group(c);
                break;
              }
            }
          }
        }
        dt = dt->getDefinition();
        if (ref->Actual_group()) break;
      }
      if (ref->Actual_group()) break;
    }

    if (m->Variables()) {
      for (auto var : *m->Variables()) {
        if (var->UhdmType() == uhdmenum_var) {
          const enum_typespec* tps =
              any_cast<const enum_typespec*>(var->Typespec());
          if (tps && tps->Enum_consts()) {
            for (auto c : *tps->Enum_consts()) {
              if (c->VpiName() == name) {
                ref->Actual_group(c);
                break;
              }
            }
          }
        }
        if (ref->Actual_group()) break;
      }
    }
    if (!ref->Actual_group()) {
      if (mod) {
        if (auto elem = mod->getDesignElement()) {
          if (elem->m_defaultNetType == VObjectType::slNoType) {
            Location loc(fileSystem->toPathId(
                             ref->VpiFile(),
                             m_compileDesign->getCompiler()->getSymbolTable()),
                         ref->VpiLineNo(), ref->VpiColumnNo(),
                         m_compileDesign->getCompiler()
                             ->getSymbolTable()
                             ->registerSymbol(name));
            Error err(ErrorDefinition::ELAB_ILLEGAL_IMPLICIT_NET, loc);
            m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
            m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
                m_compileDesign->getCompiler()
                    ->getCommandLineParser()
                    ->muteStdout());
          } else {
            if (m->UhdmType() == uhdmmodule_inst ||
                m->UhdmType() == uhdminterface_inst ||
                m->UhdmType() == uhdmprogram) {
              instance* inst = (instance*)m;
              logic_net* net = s.MakeLogic_net();
              net->VpiName(name);
              net->VpiNetType(
                  UhdmWriter::getVpiNetType(elem->m_defaultNetType));
              ref->Actual_group(net);
              VectorOfnet* nets = inst->Nets();
              if (nets == nullptr) {
                inst->Nets(s.MakeNetVec());
                nets = inst->Nets();
              }
              nets->push_back(net);
            }
          }
        }
      }
    }
  }
}

bool UhdmWriter::writeElabModule(Serializer& s, ModuleInstance* instance,
                                 module_inst* m, ExprBuilder& exprBuilder) {
  Netlist* netlist = instance->getNetlist();
  if (netlist == nullptr) return true;
  m->Ports(netlist->ports());
  ComponentMap componentMap;
  DesignComponent* mod = instance->getDefinition();
  if (mod) {
    // Let decls
    if (!mod->getLetStmts().empty()) {
      VectorOflet_decl* decls = s.MakeLet_declVec();
      m->Let_decls(decls);
      for (auto stmt : mod->getLetStmts()) {
        decls->push_back((let_decl*)stmt.second->Decl());
      }
    }
    // Typepecs
    VectorOftypespec* typespecs = s.MakeTypespecVec();
    m->Typespecs(typespecs);
    writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, false);
    for (auto item : mod->getImportedSymbols()) {
      typespecs->push_back(item);
    }
    // System elab tasks
    m->Elab_tasks((std::vector<UHDM::tf_call*>*)&mod->getElabSysCalls());
    // Assertions
    if (mod->getAssertions()) {
      m->Assertions(mod->getAssertions());
    }
  }

  writeElabParameters(s, instance, m, exprBuilder);
  if (netlist) {
    if (netlist->ports()) {
      for (auto obj : *netlist->ports()) {
        obj->VpiParent(m);
      }
    }
    m->Nets(netlist->nets());
    if (netlist->nets()) {
      for (auto obj : *netlist->nets()) {
        obj->VpiParent(m);
      }
    }
    m->Gen_scope_arrays(netlist->gen_scopes());
    if (netlist->gen_scopes()) {
      for (auto obj : *netlist->gen_scopes()) {
        obj->VpiParent(m);
      }
    }
    m->Variables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->VpiParent(m);
      }
    }
    m->Array_vars(netlist->array_vars());
    if (netlist->array_vars()) {
      for (auto obj : *netlist->array_vars()) {
        obj->VpiParent(m);
      }
    }
    m->Named_events(netlist->named_events());
    if (netlist->named_events()) {
      for (auto obj : *netlist->named_events()) {
        obj->VpiParent(m);
      }
    }
    m->Array_nets(netlist->array_nets());
    if (netlist->array_nets()) {
      for (auto obj : *netlist->array_nets()) {
        obj->VpiParent(m);
      }
    }

    if (netlist->cont_assigns()) {
      std::vector<cont_assign*>* assigns = m->Cont_assigns();
      if (assigns == nullptr) {
        m->Cont_assigns(s.MakeCont_assignVec());
        assigns = m->Cont_assigns();
      }
      writeCont_assign(netlist, s, mod, m, assigns);
    }

    // Processes
    m->Process(netlist->process_stmts());
  }

  if (mod) {
    // ClockingBlocks
    ModuleDefinition* def = (ModuleDefinition*)mod;
    for (const auto& ctupple : def->getClockingBlockMap()) {
      const ClockingBlock& cblock = ctupple.second;
      switch (cblock.getType()) {
        case ClockingBlock::Type::Default: {
          m->Default_clocking(cblock.getActual());
          break;
        }
        case ClockingBlock::Type::Global: {
          m->Global_clocking(cblock.getActual());
          break;
        }
        case ClockingBlock::Type::Regular: {
          VectorOfclocking_block* cblocks = m->Clocking_blocks();
          if (cblocks == nullptr) {
            m->Clocking_blocks(s.MakeClocking_blockVec());
            cblocks = m->Clocking_blocks();
          }
          cblocks->push_back(cblock.getActual());
          break;
        }
      }
    }
  }

  if (mod) {
    if (auto from = mod->getTask_funcs()) {
      UHDM::VectorOftask_func* target = m->Task_funcs();
      if (target == nullptr) {
        m->Task_funcs(s.MakeTask_funcVec());
        target = m->Task_funcs();
      }
      for (auto tf : *from) {
        target->push_back(tf);
        if (tf->VpiParent() == nullptr) tf->VpiParent(m);
        if (tf->Instance() == nullptr) tf->Instance(m);
      }
    }
  }

  if (mod) {
    lateTypedefBinding(s, mod, m, componentMap);
    lateBinding(s, mod, m, componentMap);
    lateTypedefBinding(s, mod, m, componentMap);
  }

  return true;
}

bool UhdmWriter::writeElabInterface(Serializer& s, ModuleInstance* instance,
                                    interface_inst* m,
                                    ExprBuilder& exprBuilder) {
  Netlist* netlist = instance->getNetlist();
  ComponentMap componentMap;
  DesignComponent* mod = instance->getDefinition();
  if (mod) {
    // Let decls
    if (!mod->getLetStmts().empty()) {
      VectorOflet_decl* decls = s.MakeLet_declVec();
      m->Let_decls(decls);
      for (auto stmt : mod->getLetStmts()) {
        decls->push_back((let_decl*)stmt.second->Decl());
      }
    }
    // Typepecs
    VectorOftypespec* typespecs = s.MakeTypespecVec();
    m->Typespecs(typespecs);
    writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, false);
    for (auto item : mod->getImportedSymbols()) {
      typespecs->push_back(item);
    }
    // System elab tasks
    m->Elab_tasks((std::vector<UHDM::tf_call*>*)&mod->getElabSysCalls());
    // Assertions
    if (mod->getAssertions()) {
      m->Assertions(mod->getAssertions());
    }
  }

  writeElabParameters(s, instance, m, exprBuilder);
  if (netlist) {
    m->Ports(netlist->ports());
    if (netlist->ports()) {
      for (auto obj : *netlist->ports()) {
        obj->VpiParent(m);
      }
    }
    m->Nets(netlist->nets());
    if (netlist->nets()) {
      for (auto obj : *netlist->nets()) {
        obj->VpiParent(m);
      }
    }
    m->Gen_scope_arrays(netlist->gen_scopes());
    if (netlist->gen_scopes()) {
      for (auto obj : *netlist->gen_scopes()) {
        obj->VpiParent(m);
      }
    }
    m->Variables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->VpiParent(m);
      }
    }
    m->Array_vars(netlist->array_vars());
    if (netlist->array_vars()) {
      for (auto obj : *netlist->array_vars()) {
        obj->VpiParent(m);
      }
    }
    m->Named_events(netlist->named_events());
    if (netlist->named_events()) {
      for (auto obj : *netlist->named_events()) {
        obj->VpiParent(m);
      }
    }
    m->Array_nets(netlist->array_nets());
    if (netlist->array_nets()) {
      for (auto obj : *netlist->array_nets()) {
        obj->VpiParent(m);
      }
    }
  }

  if (netlist) {
    if (netlist->cont_assigns()) {
      std::vector<cont_assign*>* assigns = m->Cont_assigns();
      if (assigns == nullptr) {
        m->Cont_assigns(s.MakeCont_assignVec());
        assigns = m->Cont_assigns();
      }
      writeCont_assign(netlist, s, mod, m, assigns);
    }

    // Processes
    m->Process(netlist->process_stmts());
  }

  // Modports
  ModuleDefinition* module = (ModuleDefinition*)mod;
  ModuleDefinition::ModPortSignalMap& orig_modports =
      module->getModPortSignalMap();
  VectorOfmodport* dest_modports = s.MakeModportVec();
  for (auto& orig_modport : orig_modports) {
    modport* dest_modport = s.MakeModport();
    dest_modport->Interface_inst(m);
    dest_modport->VpiName(orig_modport.first);
    dest_modport->VpiParent(m);
    const FileContent* orig_fC = orig_modport.second.getFileContent();
    const NodeId orig_nodeId = orig_modport.second.getNodeId();
    orig_fC->populateCoreMembers(orig_nodeId, orig_nodeId, dest_modport);
    VectorOfio_decl* ios = s.MakeIo_declVec();
    for (auto& sig : orig_modport.second.getPorts()) {
      const FileContent* fC = sig.getFileContent();
      io_decl* io = s.MakeIo_decl();
      io->VpiName(sig.getName());
      NodeId id = sig.getNodeId();
      fC->populateCoreMembers(id, id, io);
      if (NodeId Expression = fC->Sibling(id)) {
        m_helper.checkForLoops(true);
        any* exp =
            m_helper.compileExpression(mod, fC, Expression, m_compileDesign,
                                       nullptr, instance, true, true);
        m_helper.checkForLoops(false);
        io->Expr(exp);
      }
      unsigned int direction = UhdmWriter::getVpiDirection(sig.getDirection());
      io->VpiDirection(direction);
      io->VpiParent(dest_modport);
      ios->push_back(io);
    }
    dest_modport->Io_decls(ios);
    dest_modports->push_back(dest_modport);
  }
  m->Modports(dest_modports);

  if (mod) {
    // ClockingBlocks
    ModuleDefinition* def = (ModuleDefinition*)mod;
    for (const auto& ctupple : def->getClockingBlockMap()) {
      const ClockingBlock& cblock = ctupple.second;
      switch (cblock.getType()) {
        case ClockingBlock::Type::Default: {
          m->Default_clocking(cblock.getActual());
          break;
        }
        case ClockingBlock::Type::Global: {
          m->Global_clocking(cblock.getActual());
          break;
        }
        case ClockingBlock::Type::Regular: {
          VectorOfclocking_block* cblocks = m->Clocking_blocks();
          if (cblocks == nullptr) {
            m->Clocking_blocks(s.MakeClocking_blockVec());
            cblocks = m->Clocking_blocks();
          }
          cblocks->push_back(cblock.getActual());
          break;
        }
      }
    }
  }

  if (mod) {
    if (auto from = mod->getTask_funcs()) {
      UHDM::VectorOftask_func* target = m->Task_funcs();
      if (target == nullptr) {
        m->Task_funcs(s.MakeTask_funcVec());
        target = m->Task_funcs();
      }
      for (auto tf : *from) {
        target->push_back(tf);
        if (tf->VpiParent() == nullptr) tf->VpiParent(m);
        if (tf->Instance() == nullptr) tf->Instance(m);
      }
    }
  }

  if (mod) {
    lateTypedefBinding(s, mod, m, componentMap);
    lateBinding(s, mod, m, componentMap);
  }

  return true;
}

void writePrimTerms(ModuleInstance* instance, primitive* prim, int vpiGateType,
                    Serializer& s) {
  Netlist* netlist = instance->getNetlist();
  VectorOfprim_term* terms = s.MakePrim_termVec();
  prim->Prim_terms(terms);
  if (netlist->ports()) {
    unsigned int index = 0;
    VectorOfport* ports = netlist->ports();
    for (auto port : *ports) {
      prim_term* term = s.MakePrim_term();
      terms->push_back(term);
      expr* hconn = (expr*)port->High_conn();
      hconn->VpiParent(prim);
      term->Expr(hconn);
      term->VpiFile(port->VpiFile());
      term->VpiLineNo(port->VpiLineNo());
      term->VpiColumnNo(port->VpiColumnNo());
      term->VpiEndLineNo(port->VpiEndLineNo());
      term->VpiEndColumnNo(port->VpiEndColumnNo());
      term->VpiDirection(port->VpiDirection());
      term->VpiParent(prim);
      term->VpiTermIndex(index);
      if (vpiGateType == vpiBufPrim || vpiGateType == vpiNotPrim) {
        if (index < ports->size() - 1) {
          term->VpiDirection(vpiOutput);
        } else {
          term->VpiDirection(vpiInput);
        }
      } else if (vpiGateType == vpiTranif1Prim ||
                 vpiGateType == vpiTranif0Prim ||
                 vpiGateType == vpiRtranif1Prim ||
                 vpiGateType == vpiRtranif0Prim || vpiGateType == vpiTranPrim ||
                 vpiGateType == vpiRtranPrim) {
        if (index < ports->size() - 1) {
          term->VpiDirection(vpiInout);
        } else {
          term->VpiDirection(vpiInput);
        }
      } else {
        if (index == 0) {
          term->VpiDirection(vpiOutput);
        } else {
          term->VpiDirection(vpiInput);
        }
      }
      index++;
    }
  }
}

void UhdmWriter::writeInstance(ModuleDefinition* mod, ModuleInstance* instance,
                               any* m, CompileDesign* compileDesign,
                               UhdmWriter::ComponentMap& componentMap,
                               UhdmWriter::ModPortMap& modPortMap,
                               UhdmWriter::InstanceMap& instanceMap,
                               ExprBuilder& exprBuilder) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  Serializer& s = compileDesign->getSerializer();
  VectorOfmodule_inst* subModules = nullptr;
  VectorOfprogram* subPrograms = nullptr;
  VectorOfinterface_inst* subInterfaces = nullptr;
  VectorOfprimitive* subPrimitives = nullptr;
  VectorOfprimitive_array* subPrimitiveArrays = nullptr;
  VectorOfgen_scope_array* subGenScopeArrays = nullptr;

  if (m->UhdmType() == uhdmmodule_inst) {
    writeElabModule(s, instance, (module_inst*)m, exprBuilder);
  } else if (m->UhdmType() == uhdmgen_scope) {
    writeElabGenScope(s, instance, (gen_scope*)m, exprBuilder);
  } else if (m->UhdmType() == uhdminterface_inst) {
    writeElabInterface(s, instance, (interface_inst*)m, exprBuilder);
  }
  Netlist* netlist = instance->getNetlist();
  if (netlist) {
    if (VectorOfinterface_array* subInterfaceArrays =
            netlist->interface_arrays()) {
      UHDM_OBJECT_TYPE utype = m->UhdmType();
      if (utype == uhdmmodule_inst) {
        ((module_inst*)m)->Interface_arrays(subInterfaceArrays);
        for (interface_array* array : *subInterfaceArrays) {
          array->VpiParent(m);
        }
      } else if (utype == uhdmgen_scope) {
        ((gen_scope*)m)->Interface_arrays(subInterfaceArrays);
        for (interface_array* array : *subInterfaceArrays) {
          array->VpiParent(m);
        }
      } else if (utype == uhdminterface_inst) {
        ((interface_inst*)m)->Interface_arrays(subInterfaceArrays);
        for (interface_array* array : *subInterfaceArrays) {
          array->VpiParent(m);
        }
      }
    }
    if (VectorOfinterface_inst* subInterfaces = netlist->interfaces()) {
      UHDM_OBJECT_TYPE utype = m->UhdmType();
      if (utype == uhdmmodule_inst) {
        ((module_inst*)m)->Interfaces(subInterfaces);
        for (interface_inst* interf : *subInterfaces) {
          interf->VpiParent(m);
        }
      } else if (utype == uhdmgen_scope) {
        ((gen_scope*)m)->Interfaces(subInterfaces);
        for (interface_inst* interf : *subInterfaces) {
          interf->VpiParent(m);
        }
      } else if (utype == uhdminterface_inst) {
        ((interface_inst*)m)->Interfaces(subInterfaces);
        for (interface_inst* interf : *subInterfaces) {
          interf->VpiParent(m);
        }
      }
    }
  }
  std::map<ModuleInstance*, module_inst*> tempInstanceMap;
  for (unsigned int i = 0; i < instance->getNbChildren(); i++) {
    ModuleInstance* child = instance->getChildren(i);
    DesignComponent* childDef = child->getDefinition();
    if (ModuleDefinition* mm =
            valuedcomponenti_cast<ModuleDefinition*>(childDef)) {
      VObjectType insttype = child->getType();
      if (insttype == VObjectType::slModule_instantiation) {
        if (subModules == nullptr) subModules = s.MakeModule_instVec();
        module_inst* sm = s.MakeModule_inst();
        tempInstanceMap.emplace(child, sm);
        if (childDef && !childDef->getFileContents().empty() &&
            compileDesign->getCompiler()->isLibraryFile(
                childDef->getFileContents()[0]->getFileId())) {
          sm->VpiCellInstance(true);
        }
        sm->VpiName(child->getInstanceName());
        sm->VpiDefName(child->getModuleName());
        sm->VpiFullName(child->getFullPathName());
        const FileContent* defFile = mm->getFileContents()[0];
        sm->VpiDefFile(fileSystem->toPath(defFile->getFileId()));
        sm->VpiDefLineNo(defFile->Line(mm->getNodeIds()[0]));
        child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                     child->getNodeId(), sm);
        subModules->push_back(sm);
        if (m->UhdmType() == uhdmmodule_inst) {
          ((module_inst*)m)->Modules(subModules);
          sm->Instance((module_inst*)m);
          sm->Module_inst((module_inst*)m);
          sm->VpiParent(m);
        } else if (m->UhdmType() == uhdmgen_scope) {
          ((gen_scope*)m)->Modules(subModules);
          sm->VpiParent(m);
        }
        writeInstance(mm, child, sm, compileDesign, componentMap, modPortMap,
                      instanceMap, exprBuilder);
      } else if (insttype == VObjectType::slConditional_generate_construct ||
                 insttype == VObjectType::slLoop_generate_construct ||
                 insttype == VObjectType::slGenerate_block ||
                 insttype == VObjectType::slGenerate_item ||
                 insttype == VObjectType::slGenerate_region ||
                 insttype == VObjectType::slGenerate_module_loop_statement ||
                 insttype ==
                     VObjectType::slGenerate_module_conditional_statement ||
                 insttype == VObjectType::slGenerate_module_block ||
                 insttype == VObjectType::slGenerate_module_item ||
                 insttype == VObjectType::slGenerate_module_named_block ||
                 insttype == VObjectType::slGenerate_module_block ||
                 insttype == VObjectType::slGenerate_module_item ||
                 insttype == VObjectType::slGenerate_interface_loop_statement ||
                 insttype ==
                     VObjectType::slGenerate_interface_conditional_statement ||
                 insttype == VObjectType::slGenerate_interface_block ||
                 insttype == VObjectType::slGenerate_interface_item ||
                 insttype == VObjectType::slGenerate_interface_named_block ||
                 insttype == VObjectType::slGenerate_interface_block ||
                 insttype == VObjectType::slGenerate_interface_item) {
        if (subGenScopeArrays == nullptr)
          subGenScopeArrays = s.MakeGen_scope_arrayVec();
        gen_scope_array* sm = s.MakeGen_scope_array();
        sm->VpiName(child->getInstanceName());
        sm->VpiFullName(child->getFullPathName());
        child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                     child->getNodeId(), sm);
        subGenScopeArrays->push_back(sm);
        gen_scope* a_gen_scope = s.MakeGen_scope();
        sm->Gen_scopes(s.MakeGen_scopeVec());
        sm->Gen_scopes()->push_back(a_gen_scope);
        a_gen_scope->VpiParent(sm);
        UHDM_OBJECT_TYPE utype = m->UhdmType();
        if (utype == uhdmmodule_inst) {
          ((module_inst*)m)->Gen_scope_arrays(subGenScopeArrays);
          sm->VpiParent(m);
        } else if (utype == uhdmgen_scope) {
          ((gen_scope*)m)->Gen_scope_arrays(subGenScopeArrays);
          sm->VpiParent(m);
        } else if (utype == uhdminterface_inst) {
          ((interface_inst*)m)->Gen_scope_arrays(subGenScopeArrays);
          sm->VpiParent(m);
        }
        writeInstance(mm, child, a_gen_scope, compileDesign, componentMap,
                      modPortMap, instanceMap, exprBuilder);

      } else if (insttype == VObjectType::slInterface_instantiation) {
        if (subInterfaces == nullptr) subInterfaces = s.MakeInterface_instVec();
        interface_inst* sm = s.MakeInterface_inst();
        sm->VpiName(child->getInstanceName());
        sm->VpiDefName(child->getModuleName());
        sm->VpiFullName(child->getFullPathName());
        child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                     child->getNodeId(), sm);
        const FileContent* defFile = mm->getFileContents()[0];
        sm->VpiDefFile(fileSystem->toPath(defFile->getFileId()));
        sm->VpiDefLineNo(defFile->Line(mm->getNodeIds()[0]));
        subInterfaces->push_back(sm);
        UHDM_OBJECT_TYPE utype = m->UhdmType();
        if (utype == uhdmmodule_inst) {
          ((module_inst*)m)->Interfaces(subInterfaces);
          sm->Instance((module_inst*)m);
          sm->VpiParent(m);
        } else if (utype == uhdmgen_scope) {
          ((gen_scope*)m)->Interfaces(subInterfaces);
          sm->VpiParent(m);
        } else if (utype == uhdminterface_inst) {
          ((interface_inst*)m)->Interfaces(subInterfaces);
          sm->VpiParent(m);
        }
        writeInstance(mm, child, sm, compileDesign, componentMap, modPortMap,
                      instanceMap, exprBuilder);

      } else if ((insttype == VObjectType::slUdp_instantiation) ||
                 (insttype == VObjectType::slCmos_switch_instance) ||
                 (insttype == VObjectType::slEnable_gate_instance) ||
                 (insttype == VObjectType::slMos_switch_instance) ||
                 (insttype == VObjectType::slN_input_gate_instance) ||
                 (insttype == VObjectType::slN_output_gate_instance) ||
                 (insttype == VObjectType::slPass_enable_switch_instance) ||
                 (insttype == VObjectType::slPass_switch_instance) ||
                 (insttype == VObjectType::slPull_gate_instance)) {
        UHDM::primitive* gate = nullptr;
        UHDM::primitive_array* gate_array = nullptr;
        const FileContent* fC = child->getFileContent();
        NodeId gatenode = fC->Child(fC->Parent(child->getNodeId()));
        VObjectType gatetype = fC->Type(gatenode);
        int vpiGateType = getBuiltinType(gatetype);
        if (insttype == VObjectType::slUdp_instantiation) {
          UHDM::udp* udp = s.MakeUdp();
          gate = udp;
          if (ModuleDefinition* mm =
                  valuedcomponenti_cast<ModuleDefinition*>(childDef)) {
            udp->Udp_defn(mm->getUdpDefn());
          }
          if (UHDM::VectorOfrange* ranges = child->getNetlist()->ranges()) {
            gate_array = s.MakeUdp_array();
            VectorOfprimitive* prims = s.MakePrimitiveVec();
            gate_array->Primitives(prims);
            gate_array->Ranges(ranges);
            prims->push_back(gate);
            if (subPrimitiveArrays == nullptr)
              subPrimitiveArrays = s.MakePrimitive_arrayVec();
            subPrimitiveArrays->push_back(gate_array);
          } else {
            if (subPrimitives == nullptr) subPrimitives = s.MakePrimitiveVec();
            subPrimitives->push_back(gate);
          }
        } else if (vpiGateType == vpiPmosPrim || vpiGateType == vpiRpmosPrim ||
                   vpiGateType == vpiNmosPrim || vpiGateType == vpiRnmosPrim ||
                   vpiGateType == vpiCmosPrim || vpiGateType == vpiRcmosPrim ||
                   vpiGateType == vpiTranif1Prim ||
                   vpiGateType == vpiTranif0Prim ||
                   vpiGateType == vpiRtranif1Prim ||
                   vpiGateType == vpiRtranif0Prim ||
                   vpiGateType == vpiTranPrim || vpiGateType == vpiRtranPrim) {
          gate = s.MakeSwitch_tran();
          if (UHDM::VectorOfrange* ranges = child->getNetlist()->ranges()) {
            gate_array = s.MakeSwitch_array();
            VectorOfprimitive* prims = s.MakePrimitiveVec();
            gate_array->Primitives(prims);
            gate_array->Ranges(ranges);
            prims->push_back(gate);
            if (subPrimitiveArrays == nullptr)
              subPrimitiveArrays = s.MakePrimitive_arrayVec();
            subPrimitiveArrays->push_back(gate_array);
          } else {
            if (subPrimitives == nullptr) subPrimitives = s.MakePrimitiveVec();
            subPrimitives->push_back(gate);
          }
          gate->VpiPrimType(vpiGateType);
        } else {
          gate = s.MakeGate();
          if (UHDM::VectorOfrange* ranges = child->getNetlist()->ranges()) {
            gate_array = s.MakeGate_array();
            gate_array->VpiName(child->getInstanceName());
            gate_array->VpiFullName(child->getFullPathName());
            child->getFileContent()->populateCoreMembers(
                child->getNodeId(), child->getNodeId(), gate_array);
            VectorOfprimitive* prims = s.MakePrimitiveVec();
            gate_array->Primitives(prims);
            gate_array->Ranges(ranges);
            prims->push_back(gate);
            if (subPrimitiveArrays == nullptr)
              subPrimitiveArrays = s.MakePrimitive_arrayVec();
            subPrimitiveArrays->push_back(gate_array);
          } else {
            if (subPrimitives == nullptr) subPrimitives = s.MakePrimitiveVec();
            subPrimitives->push_back(gate);
          }
          gate->VpiPrimType(vpiGateType);
        }
        if (UHDM::VectorOfexpr* delays = child->getNetlist()->delays()) {
          if (delays->size() == 1) {
            gate->Delay((*delays)[0]);
          }
        }

        gate->VpiName(child->getInstanceName());
        gate->VpiDefName(child->getModuleName());
        gate->VpiFullName(child->getFullPathName());
        child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                     child->getNodeId(), gate);
        UHDM_OBJECT_TYPE utype = m->UhdmType();
        if (utype == uhdmmodule_inst) {
          ((module_inst*)m)->Primitives(subPrimitives);
          ((module_inst*)m)->Primitive_arrays(subPrimitiveArrays);
          gate->VpiParent(m);
        } else if (utype == uhdmgen_scope) {
          ((gen_scope*)m)->Primitives(subPrimitives);
          ((gen_scope*)m)->Primitive_arrays(subPrimitiveArrays);
          gate->VpiParent(m);
        }
        writePrimTerms(child, gate, vpiGateType, s);
      } else {
        // Unknown object type
      }
    } else if (Program* prog = valuedcomponenti_cast<Program*>(childDef)) {
      if (subPrograms == nullptr) subPrograms = s.MakeProgramVec();
      program* sm = s.MakeProgram();
      sm->VpiName(child->getInstanceName());
      sm->VpiDefName(child->getModuleName());
      sm->VpiFullName(child->getFullPathName());
      child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                   child->getNodeId(), sm);
      const FileContent* defFile = prog->getFileContents()[0];
      sm->VpiDefFile(fileSystem->toPath(defFile->getFileId()));
      sm->VpiDefLineNo(defFile->Line(prog->getNodeIds()[0]));
      subPrograms->push_back(sm);
      UHDM_OBJECT_TYPE utype = m->UhdmType();
      if (utype == uhdmmodule_inst) {
        ((module_inst*)m)->Programs(subPrograms);
        sm->Instance((module_inst*)m);
        sm->VpiParent(m);
      } else if (utype == uhdmgen_scope) {
        ((gen_scope*)m)->Programs(subPrograms);
        sm->VpiParent(m);
      }
      writeElabProgram(s, child, sm);
    } else {
      // Undefined module
      if (subModules == nullptr) subModules = s.MakeModule_instVec();
      module_inst* sm = s.MakeModule_inst();
      sm->VpiName(child->getInstanceName());
      sm->VpiDefName(child->getModuleName());
      sm->VpiFullName(child->getFullPathName());
      child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                   child->getNodeId(), sm);
      subModules->push_back(sm);
      UHDM_OBJECT_TYPE utype = m->UhdmType();
      if (utype == uhdmmodule_inst) {
        ((module_inst*)m)->Modules(subModules);
        sm->Instance((module_inst*)m);
        sm->Module_inst((module_inst*)m);
        sm->VpiParent(m);
      } else if (utype == uhdmgen_scope) {
        ((gen_scope*)m)->Modules(subModules);
        sm->VpiParent(m);
      }
      writeInstance(mm, child, sm, compileDesign, componentMap, modPortMap,
                    instanceMap, exprBuilder);
    }
  }

  if (m->UhdmType() == uhdmmodule_inst) {
    const auto& moduleArrayModuleInstancesMap =
        instance->getModuleArrayModuleInstancesMap();
    if (!moduleArrayModuleInstancesMap.empty()) {
      ((module_inst*)m)->Module_arrays(s.MakeModule_arrayVec());
      std::vector<UHDM::module_array*> moduleArrays;
      std::transform(
          moduleArrayModuleInstancesMap.begin(),
          moduleArrayModuleInstancesMap.end(), std::back_inserter(moduleArrays),
          [](ModuleInstance::ModuleArrayModuleInstancesMap::const_reference
                 pair) { return pair.first; });
      std::sort(
          moduleArrays.begin(), moduleArrays.end(),
          [](const UHDM::module_array* lhs, const UHDM::module_array* rhs) {
            return lhs->UhdmId() < rhs->UhdmId();
          });
      for (UHDM::module_array* modArray : moduleArrays) {
        const auto& modInstances =
            moduleArrayModuleInstancesMap.find(modArray)->second;
        if (!modInstances.empty()) {
          modArray->Modules(s.MakeModule_instVec());
          modArray->VpiParent(m);
          ((module_inst*)m)->Module_arrays()->push_back(modArray);
          for (ModuleInstance* modInst : modInstances) {
            auto it = tempInstanceMap.find(modInst);
            if (it != tempInstanceMap.end()) {
              modArray->Modules()->push_back(it->second);
            }
          }
        }
      }
    }
  }
}

vpiHandle UhdmWriter::write(PathId uhdmFileId) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  ComponentMap componentMap;
  ModPortMap modPortMap;
  InstanceMap instanceMap;
  /*ModuleMap moduleMap;*/
  Serializer& s = m_compileDesign->getSerializer();
  ExprBuilder exprBuilder;
  exprBuilder.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());

  Location loc(uhdmFileId);
  Error err(ErrorDefinition::UHDM_CREATING_MODEL, loc);
  m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
  m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
      m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());

  vpiHandle designHandle = 0;
  std::vector<vpiHandle> designs;
  design* d = nullptr;
  if (m_design) {
    d = s.MakeDesign();
    designHandle = reinterpret_cast<vpiHandle>(new uhdm_handle(uhdmdesign, d));
    std::string designName = "unnamed";
    auto topLevelModules = m_design->getTopLevelModuleInstances();
    for (auto inst : topLevelModules) {
      designName = inst->getModuleName();
      break;
    }
    d->VpiName(designName);
    designs.push_back(designHandle);

    // ---------------------------
    // Include File Info

    VectorOfinclude_file_info* fileInfos = s.MakeInclude_file_infoVec();
    d->Include_file_infos(fileInfos);
    for (const CompileSourceFile* sourceFile :
         m_compileDesign->getCompiler()->getCompileSourceFiles()) {
      const PreprocessFile* const pf = sourceFile->getPreprocessor();
      for (const IncludeFileInfo& ifi : pf->getIncludeFileInfo()) {
        if ((ifi.m_context == IncludeFileInfo::Context::INCLUDE) &&
            (ifi.m_action == IncludeFileInfo::Action::PUSH)) {
          include_file_info* const pifi = s.MakeInclude_file_info();
          pifi->VpiFile(fileSystem->toPath(pf->getRawFileId()));
          pifi->VpiIncludedFile(fileSystem->toPath(ifi.m_sectionFileId));
          pifi->VpiLineNo(ifi.m_originalStartLine);
          pifi->VpiColumnNo(ifi.m_originalStartColumn);
          pifi->VpiEndLineNo(ifi.m_originalEndLine);
          pifi->VpiEndColumnNo(ifi.m_originalEndColumn);
          fileInfos->push_back(pifi);
        }
      }
    }

    // -------------------------------
    // Non-Elaborated Model

    // FileContent
    VectorOftypespec* typespecs = s.MakeTypespecVec();
    d->Typespecs(typespecs);
    for (auto& fileIdContent : m_design->getAllFileContents()) {
      // Typepecs
      writeDataTypes(fileIdContent.second->getDataTypeMap(), d, typespecs, s,
                     true);

      // Function and tasks
      if (auto from = fileIdContent.second->getTask_funcs()) {
        UHDM::VectorOftask_func* target = d->Task_funcs();
        if (target == nullptr) {
          d->Task_funcs(s.MakeTask_funcVec());
          target = d->Task_funcs();
        }
        for (auto tf : *from) {
          target->push_back(tf);
          if (tf->VpiParent() == nullptr) tf->VpiParent(d);
        }
      }

      // Parameters
      if (auto from = fileIdContent.second->getParameters()) {
        UHDM::VectorOfany* target = d->Parameters();
        if (target == nullptr) {
          d->Parameters(s.MakeAnyVec());
          target = d->Parameters();
        }
        for (auto tf : *from) {
          target->push_back(tf);
          if (tf->VpiParent() == nullptr) tf->VpiParent(d);
        }
      }

      // Param assigns
      if (auto from = fileIdContent.second->getParam_assigns()) {
        UHDM::VectorOfparam_assign* target = d->Param_assigns();
        if (target == nullptr) {
          d->Param_assigns(s.MakeParam_assignVec());
          target = d->Param_assigns();
        }
        for (auto tf : *from) {
          target->push_back(tf);
          if (tf->VpiParent() == nullptr) tf->VpiParent(d);
        }
      }
      lateTypedefBinding(s, fileIdContent.second, nullptr, componentMap);
    }

    // Packages
    SURELOG::PackageDefinitionVec packages =
        m_design->getOrderedPackageDefinitions();
    for (auto& pack : m_design->getPackageDefinitions()) {
      if (pack.first == "builtin") {
        if (pack.second) packages.insert(packages.begin(), pack.second);
        break;
      }
    }

    VectorOfpackage* v2 = s.MakePackageVec();
    for (Package* pack : packages) {
      if (!pack) continue;
      if (!pack->getFileContents().empty() &&
          pack->getType() == VObjectType::slPackage_declaration) {
        const FileContent* fC = pack->getFileContents()[0];
        package* p = (package*)pack->getUhdmInstance();
        componentMap.emplace(pack, p);
        p->VpiParent(d);
        p->VpiTop(true);
        p->VpiDefName(pack->getName());
        p->Attributes(pack->Attributes());
        writePackage(pack, p, s, componentMap, true);
        if (fC) {
          // Builtin package has no file
          const NodeId modId = pack->getNodeIds()[0];
          const NodeId startId = fC->sl_collect(modId, VObjectType::slPackage);
          fC->populateCoreMembers(startId, modId, p);
        }
        v2->push_back(p);
      }
    }
    d->TopPackages(v2);

    VectorOfpackage* v3 = s.MakePackageVec();
    d->AllPackages(v3);
    for (Package* pack : packages) {
      if (!pack) continue;
      if (!pack->getFileContents().empty() &&
          pack->getType() == VObjectType::slPackage_declaration) {
        const FileContent* fC = pack->getFileContents()[0];
        package* p = s.MakePackage();
        p->VpiName(pack->getName());
        p->VpiParent(d);
        p->VpiDefName(pack->getName());
        p->Attributes(pack->Attributes());
        v3->push_back(p);
        writePackage(pack->getUnElabPackage(), p, s, componentMap, false);
        if (fC) {
          // Builtin package has no file
          const NodeId modId = pack->getNodeIds()[0];
          const NodeId startId = fC->sl_collect(modId, VObjectType::slPackage);
          fC->populateCoreMembers(startId, modId, p);
        }
      }
    }

    // Programs
    auto programs = m_design->getProgramDefinitions();
    VectorOfprogram* uhdm_programs = s.MakeProgramVec();
    for (const auto& progNamePair : programs) {
      Program* prog = progNamePair.second;
      if (!prog->getFileContents().empty() &&
          prog->getType() == VObjectType::slProgram_declaration) {
        const FileContent* fC = prog->getFileContents()[0];
        program* p = s.MakeProgram();
        componentMap.emplace(prog, p);
        p->VpiParent(d);
        p->VpiDefName(prog->getName());
        const NodeId modId = prog->getNodeIds()[0];
        const NodeId startId = fC->sl_collect(modId, VObjectType::slProgram);
        fC->populateCoreMembers(startId, modId, p);
        p->Attributes(prog->Attributes());
        writeProgram(prog, p, s, componentMap, modPortMap);
        uhdm_programs->push_back(p);
      }
    }
    d->AllPrograms(uhdm_programs);

    // Interfaces
    auto modules = m_design->getModuleDefinitions();
    VectorOfinterface_inst* uhdm_interfaces = s.MakeInterface_instVec();
    for (const auto& modNamePair : modules) {
      ModuleDefinition* mod = modNamePair.second;
      if (mod->getFileContents().empty()) {
        // Built-in primitive
      } else if (mod->getType() == VObjectType::slInterface_declaration) {
        const FileContent* fC = mod->getFileContents()[0];
        interface_inst* m = s.MakeInterface_inst();
        componentMap.emplace(mod, m);
        m->VpiParent(d);
        m->VpiDefName(mod->getName());
        const NodeId modId = mod->getNodeIds()[0];
        const NodeId startId = fC->sl_collect(modId, VObjectType::slInterface);
        fC->populateCoreMembers(startId, modId, m);
        m->Attributes(mod->Attributes());
        uhdm_interfaces->push_back(m);
        writeInterface(mod, m, s, componentMap, modPortMap);
      }
    }
    d->AllInterfaces(uhdm_interfaces);

    // Modules
    VectorOfmodule_inst* uhdm_modules = s.MakeModule_instVec();
    // Udps
    VectorOfudp_defn* uhdm_udps = s.MakeUdp_defnVec();
    for (const auto& modNamePair : modules) {
      ModuleDefinition* mod = modNamePair.second;
      if (mod->getFileContents().empty()) {
        // Built-in primitive
      } else if (mod->getType() == VObjectType::slModule_declaration) {
        const FileContent* fC = mod->getFileContents()[0];
        module_inst* m = s.MakeModule_inst();
        if (m_compileDesign->getCompiler()->isLibraryFile(
                mod->getFileContents()[0]->getFileId())) {
          m->VpiCellInstance(true);
        }
        componentMap.emplace(mod, m);
        // moduleMap.emplace(mod->getName(), m);
        m->VpiParent(d);
        m->VpiDefName(mod->getName());
        m->Attributes(mod->Attributes());
        const NodeId modId = mod->getNodeIds()[0];
        const NodeId startId =
            fC->sl_collect(modId, VObjectType::slModule_keyword);
        fC->populateCoreMembers(startId, modId, m);
        uhdm_modules->push_back(m);
        writeModule(mod, m, s, componentMap, /*moduleMap,*/ modPortMap);
      } else if (mod->getType() == VObjectType::slUdp_declaration) {
        const FileContent* fC = mod->getFileContents()[0];
        UHDM::udp_defn* defn = mod->getUdpDefn();
        if (defn) {
          defn->VpiParent(d);
          defn->VpiDefName(mod->getName());
          const NodeId modId = mod->getNodeIds()[0];
          const NodeId startId =
              fC->sl_collect(modId, VObjectType::slPrimitive);
          fC->populateCoreMembers(startId, modId, defn);
          defn->Attributes(mod->Attributes());
          uhdm_udps->push_back(defn);
        }
      }
    }
    d->AllModules(uhdm_modules);
    d->AllUdps(uhdm_udps);

    // Classes
    auto classes = m_design->getClassDefinitions();
    VectorOfclass_defn* v4 = s.MakeClass_defnVec();
    for (const auto& classNamePair : classes) {
      ClassDefinition* classDef = classNamePair.second;
      if (!classDef->getFileContents().empty() &&
          classDef->getType() == VObjectType::slClass_declaration) {
        class_defn* c = classDef->getUhdmDefinition();
        if (!c->VpiParent()) {
          writeClass(classDef, v4, s, componentMap, d);
        }
      }
    }
    d->AllClasses(v4);

    // -------------------------------
    // Elaborated Model (Folded)

    // Top-level modules
    VectorOfmodule_inst* uhdm_top_modules = s.MakeModule_instVec();
    for (ModuleInstance* inst : topLevelModules) {
      DesignComponent* component = inst->getDefinition();
      ModuleDefinition* mod =
          valuedcomponenti_cast<ModuleDefinition*>(component);
      const auto& itr = componentMap.find(mod);
      module_inst* m = s.MakeModule_inst();
      m->VpiTopModule(true);
      m->VpiTop(true);
      module_inst* def = (module_inst*)itr->second;
      m->VpiDefName(def->VpiDefName());
      m->VpiName(def->VpiDefName());  // Top's instance name is module name
      m->VpiFullName(
          def->VpiDefName());  // Top's full instance name is module name
      m->VpiFile(def->VpiFile());
      m->VpiLineNo(def->VpiLineNo());
      m->VpiColumnNo(def->VpiColumnNo());
      m->VpiEndLineNo(def->VpiEndLineNo());
      m->VpiEndColumnNo(def->VpiEndColumnNo());
      writeInstance(mod, inst, m, m_compileDesign, componentMap, modPortMap,
                    instanceMap, exprBuilder);
      uhdm_top_modules->push_back(m);
    }
    d->TopModules(uhdm_top_modules);
  }

  if (m_compileDesign->getCompiler()->getCommandLineParser()->getUhdmStats()) {
    s.PrintStats(std::cerr, "Non-Elaborated Model");
  }

  // ----------------------------------
  // Lint only the elaborated model
  UhdmLint* linter = new UhdmLint(&s, d);
  linter->listenDesigns(designs);
  delete linter;

  if (m_compileDesign->getCompiler()
          ->getCommandLineParser()
          ->reportNonSynthesizable()) {
    std::set<const any*> nonSynthesizableObjects;
    SynthSubset* annotate =
        new SynthSubset(&s, nonSynthesizableObjects, true,
                        m_compileDesign->getCompiler()
                            ->getCommandLineParser()
                            ->reportNonSynthesizableWithFormal());
    annotate->listenDesigns(designs);
    delete annotate;
  }

  // ----------------------------------
  // Fully elaborated model
  if (m_compileDesign->getCompiler()->getCommandLineParser()->getElabUhdm()) {
    Error err(ErrorDefinition::UHDM_ELABORATION, loc);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
        m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());

    ElaboratorListener* listener = new ElaboratorListener(&s, false, false);
    listener->uniquifyTypespec(false);
    listener->listenDesigns(designs);
    delete listener;

    if (m_compileDesign->getCompiler()
            ->getCommandLineParser()
            ->getUhdmStats()) {
      s.PrintStats(std::cerr, "Elaborated Model");
    }
  }

  UhdmAdjuster* adjuster = new UhdmAdjuster(&s, d);
  adjuster->listenDesigns(designs);
  delete adjuster;

  const fs::path uhdmFile = fileSystem->toPlatformAbsPath(uhdmFileId);
  if (m_compileDesign->getCompiler()->getCommandLineParser()->writeUhdm()) {
    Error err(ErrorDefinition::UHDM_WRITE_DB, loc);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
        m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());
    s.Save(uhdmFile);
  }

  if (m_compileDesign->getCompiler()->getCommandLineParser()->getDebugUhdm() ||
      m_compileDesign->getCompiler()->getCommandLineParser()->getCoverUhdm()) {
    // Check before restore
    Location loc(fileSystem->getCheckerHtmlFile(
        uhdmFileId, m_compileDesign->getCompiler()->getSymbolTable()));
    Error err(ErrorDefinition::UHDM_WRITE_HTML_COVERAGE, loc);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
        m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());

    UhdmChecker* uhdmchecker = new UhdmChecker(m_compileDesign, m_design);
    uhdmchecker->check(uhdmFileId);
    delete uhdmchecker;
  }
  if (m_compileDesign->getCompiler()->getCommandLineParser()->getDebugUhdm()) {
    if (m_compileDesign->getCompiler()->getCommandLineParser()->writeUhdm()) {
      Location loc((SymbolId)uhdmFileId);
      Error err1(ErrorDefinition::UHDM_LOAD_DB, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err1);
      m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
          m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());
      const std::vector<vpiHandle>& restoredDesigns =
          s.Restore(uhdmFile.string());

      Error err2(ErrorDefinition::UHDM_VISITOR, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err2);
      m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
          m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());

      std::cout << "====== UHDM =======\n";
      if (!restoredDesigns.empty()) {
        designHandle = restoredDesigns[0];
      }
      vpi_show_ids(
          m_compileDesign->getCompiler()->getCommandLineParser()->showVpiIds());
      visit_designs(restoredDesigns, std::cout);
      std::cout << "===================\n";
    } else {
      Location loc(
          m_compileDesign->getCompiler()->getSymbolTable()->registerSymbol(
              "in-memory uhdm"));
      Error err2(ErrorDefinition::UHDM_VISITOR, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err2);
      m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
          m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());
      std::cout << "====== UHDM =======\n";
      vpi_show_ids(
          m_compileDesign->getCompiler()->getCommandLineParser()->showVpiIds());
      visit_designs({designHandle}, std::cout);
      std::cout << "===================\n";
    }
  }
  m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
      m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());
  return designHandle;
}
}  // namespace SURELOG
