/*
 Copyright 2020 Alain Dargelas

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
 * File:   NetlistElaboration.cpp
 * Author: alain
 *
 * Created on Mar 1, 2020, 6:36 PM
 */

#include "Surelog/DesignCompile/NetlistElaboration.h"

#include <uhdm/BaseClass.h>
#include <uhdm/expr.h>
#include <uhdm/uhdm_types.h>

#include <algorithm>
#include <cstdint>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Design/DataType.h"
#include "Surelog/Design/DesignComponent.h"
#include "Surelog/Design/DesignElement.h"
#include "Surelog/Design/DummyType.h"
#include "Surelog/Design/Enum.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/Modport.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Netlist.h"
#include "Surelog/Design/ParamAssign.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/Design/SimpleType.h"
#include "Surelog/Design/Struct.h"
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
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/sv_vpi_user.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_user.h>

#include <algorithm>

namespace SURELOG {

using namespace uhdm;  // NOLINT (using a bunch of these)

NetlistElaboration::NetlistElaboration(Session* session,
                                       CompileDesign* compileDesign)
    : TestbenchElaboration(session, compileDesign) {}

bool NetlistElaboration::elaboratePackages() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  // Packages
  auto& packageDefs = design->getPackageDefinitions();
  for (auto& packageDef : packageDefs) {
    Package* p = packageDef.second;
    Reduce reduce = Reduce::No;
    for (Package* pack : {p->getUnElabPackage(), p}) {
      if (pack->getNetlist() == nullptr) {
        Netlist* netlist = new Netlist(nullptr);
        pack->setNetlist(netlist);
      }
      Netlist* netlist = pack->getNetlist();
      // Variables and nets in Packages
      std::set<Signal*> notSignals;
      for (Signal* sig : pack->getSignals()) {
        if (!elabSignal(sig, nullptr, nullptr, nullptr, netlist, pack, "",
                        false, reduce)) {
          notSignals.insert(sig);
        }
      }
      for (auto sig : notSignals) pack->removeSignal(sig);
      reduce = Reduce::Yes;
    }
  }
  return true;
}

bool NetlistElaboration::elaborateInstance(ModuleInstance* instance) {
  return elaborate_(instance, false);
}

bool NetlistElaboration::elaborate() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  elaboratePackages();

  // Top level modules
  const std::vector<ModuleInstance*>& topModules =
      design->getTopLevelModuleInstances();
  return std::all_of(
      topModules.begin(), topModules.end(),
      [this](ModuleInstance* inst) { return elaborate_(inst, true); });
}

bool NetlistElaboration::elab_parameters_(ModuleInstance* instance,
                                          bool param_port) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  CommandLineParser* const clp = m_session->getCommandLineParser();
  uhdm::Serializer& s = m_compileDesign->getSerializer();
  if (!instance) return true;
  Netlist* netlist = instance->getNetlist();
  if (netlist == nullptr) return true;
  bool en_replay = clp->replay();
  ModuleDefinition* mod =
      valuedcomponenti_cast<ModuleDefinition*>(instance->getDefinition());
  uhdm::ParamAssignCollection* assigns = netlist->param_assigns();
  if (!mod) {
    if (param_port) return true;
    for (const auto& mv : instance->getMappedValues()) {
      if (assigns == nullptr) {
        netlist->param_assigns(s.makeCollection<uhdm::ParamAssign>());
        assigns = netlist->param_assigns();
      }
      const std::string& paramName = mv.first;
      Value* value = mv.second.first;
      uint32_t line = mv.second.second;
      const FileContent* instfC = instance->getFileContent();
      if (value && value->isValid()) {
        uhdm::ParamAssign* inst_assign = s.make<uhdm::ParamAssign>();
        inst_assign->setOverriden(instance->isOverridenParam(paramName));
        uhdm::Parameter* p = s.make<uhdm::Parameter>();
        p->setName(paramName);
        p->setParent(inst_assign);
        uhdm::Constant* c = s.make<uhdm::Constant>();
        c->setValue(value->uhdmValue());
        c->setDecompile(value->decompiledValue());
        c->setFile(fileSystem->toPath(instfC->getFileId()));
        c->setSize(value->getSize());
        c->setConstType(value->vpiValType());
        c->setStartLine(line);
        c->setEndLine(line);
        inst_assign->setLhs(p);
        inst_assign->setRhs(c);
        assigns->push_back(inst_assign);
      }
    }
    return true;
  }
  if (mod->getParameters() != nullptr) {
    // Type params
    for (const auto& nameParam : mod->getParameterMap()) {
      Parameter* sit = nameParam.second;
      elabTypeParameter_(mod, sit, instance);
    }
  }
  // Regular
  bool isMultidimensional = false;
  for (ParamAssign* assign : mod->getParamAssignVec()) {
    if (param_port ^ assign->isPortParam()) {
      continue;
    }
    if (assigns == nullptr) {
      netlist->param_assigns(s.makeCollection<uhdm::ParamAssign>());
      assigns = netlist->param_assigns();
    }
    uhdm::ParamAssign* mod_assign = assign->getUhdmParamAssign();
    isMultidimensional = assign->isMultidimensional();
    const std::string_view paramName =
        assign->getFileContent()->SymName(assign->getParamId());
    if (mod_assign) {
      const uhdm::Any* rhs = mod_assign->getRhs();
      uhdm::Expr* complexVal = instance->getComplexValue(paramName);
      if (complexVal) {
        rhs = complexVal;
      }
      bool isOverriden = instance->isOverridenParam(paramName);
      if ((!isOverriden) || complexVal) {
        // Complex value(default or overriden), no simple value
        if (rhs && rhs->getUhdmType() == uhdm::UhdmType::Operation) {
          uhdm::Operation* op = (uhdm::Operation*)rhs;
          int32_t opType = op->getOpType();
          if (opType == vpiCastOp || (opType == vpiMultiConcatOp) ||
              (opType == vpiConditionOp)) {
            isMultidimensional = false;
          }

          // Don't reduce these operations
          if (opType == vpiAssignmentPatternOp ||
              opType == vpiMultiAssignmentPatternOp) {
            uhdm::ElaboratorContext elaboratorContext(&s, false, true);
            uhdm::ParamAssign* pclone = (uhdm::ParamAssign*)uhdm::clone_tree(
                mod_assign, &elaboratorContext);
            pclone->setParent((uhdm::Any*)mod_assign->getParent());
            pclone->setOverriden(instance->isOverridenParam(paramName));
            const uhdm::Any* lhs = pclone->getLhs();
            uhdm::Any* rhs = (uhdm::Any*)pclone->getRhs();
            if (complexVal) {
              rhs = uhdm::clone_tree(complexVal, &elaboratorContext);
              rhs->setParent(pclone);
            }
            const uhdm::Typespec* ts = nullptr;
            if (lhs->getUhdmType() == uhdm::UhdmType::Parameter) {
              if (const uhdm::RefTypespec* rt =
                      ((uhdm::Parameter*)lhs)->getTypespec()) {
                ts = rt->getActual();
              }
            }
            if (m_helper.substituteAssignedValue(rhs, m_compileDesign)) {
              rhs = m_helper.expandPatternAssignment(ts, (uhdm::Expr*)rhs, mod,
                                                     m_compileDesign,
                                                     Reduce::Yes, instance);
            }
            rhs = (uhdm::Expr*)m_helper.defaultPatternAssignment(
                ts, rhs, mod, m_compileDesign, Reduce::Yes, instance);
            pclone->setRhs(rhs);
            m_helper.reorderAssignmentPattern(mod, lhs, rhs, m_compileDesign,
                                              instance, 0);

            if (lhs->getUhdmType() == uhdm::UhdmType::Parameter) {
              uhdm::Parameter* p = (uhdm::Parameter*)lhs;
              const uhdm::Typespec* tps = nullptr;
              if (const uhdm::RefTypespec* rt = p->getTypespec()) {
                tps = rt->getActual();
              }
              if (tps) {
                uhdm::ExprEval eval;
                if (uhdm::Expr* tmp = eval.flattenPatternAssignments(
                        s, tps, (uhdm::Expr*)rhs)) {
                  if (tmp->getUhdmType() == uhdm::UhdmType::Operation) {
                    ((uhdm::Operation*)rhs)
                        ->setOperands(((uhdm::Operation*)tmp)->getOperands());
                  }
                }
              } else if (rhs->getUhdmType() == uhdm::UhdmType::Operation) {
                uhdm::Operation* op = (uhdm::Operation*)rhs;
                if (const uhdm::RefTypespec* rt = op->getTypespec()) {
                  if (const uhdm::Typespec* tps = rt->getActual()) {
                    uhdm::ExprEval eval;
                    if (uhdm::Expr* tmp = eval.flattenPatternAssignments(
                            s, tps, (uhdm::Expr*)rhs)) {
                      if (tmp->getUhdmType() == uhdm::UhdmType::Operation) {
                        ((uhdm::Operation*)rhs)
                            ->setOperands(
                                ((uhdm::Operation*)tmp)->getOperands());
                      }
                    }
                  }
                }
              }
            }
            assigns->push_back(pclone);
            continue;
          }
        }
      }
    }

    uhdm::ParamAssign* inst_assign = s.make<uhdm::ParamAssign>();
    inst_assign->setOverriden(instance->isOverridenParam(paramName));
    inst_assign->setFile(mod_assign->getFile());
    inst_assign->setStartLine(mod_assign->getStartLine());
    inst_assign->setStartColumn(mod_assign->getStartColumn());
    inst_assign->setEndLine(mod_assign->getEndLine());
    inst_assign->setEndColumn(mod_assign->getEndColumn());
    inst_assign->setLhs((uhdm::Any*)mod_assign->getLhs());

    bool overriden = false;
    for (Parameter* tpm :
         instance->getTypeParams()) {  // for parameters that do not resolve to
                                       // scalars (complex structs)
      if (tpm->getName() == paramName) {
        overriden = true;
        if (ModuleInstance* pinst = instance->getParent()) {
          ModuleDefinition* pmod =
              valuedcomponenti_cast<ModuleDefinition*>(pinst->getDefinition());
          m_helper.checkForLoops(true);
          uhdm::Expr* rhs = (uhdm::Expr*)m_helper.compileExpression(
              pmod, tpm->getFileContent(), tpm->getNodeId(), m_compileDesign,
              isMultidimensional ? Reduce::No : Reduce::Yes, nullptr, pinst);
          m_helper.checkForLoops(false);
          if (en_replay && m_helper.errorOnNegativeConstant(
                               pmod, rhs, m_compileDesign, pinst)) {
            bool replay = false;
            // GDB: p replay=true
            if (replay) {
              m_helper.compileExpression(
                  pmod, tpm->getFileContent(), tpm->getNodeId(),
                  m_compileDesign,
                  isMultidimensional ? Reduce::No : Reduce::Yes, nullptr,
                  pinst);
            }
          }

          // If it is a complex expression (! constant)...
          if ((!rhs) ||
              (rhs && (rhs->getUhdmType() != uhdm::UhdmType::Constant))) {
            // But if this value can be reduced to a constant then take the
            // constant
            m_helper.checkForLoops(true);
            uhdm::Expr* crhs = (uhdm::Expr*)m_helper.compileExpression(
                mod, assign->getFileContent(), assign->getAssignId(),
                m_compileDesign, Reduce::Yes, nullptr, instance);
            m_helper.checkForLoops(false);
            if (crhs && crhs->getUhdmType() == uhdm::UhdmType::Constant) {
              if (en_replay && m_helper.errorOnNegativeConstant(
                                   mod, crhs, m_compileDesign, instance)) {
                bool replay = false;
                // GDB: p replay=true
                if (replay) {
                  m_helper.compileExpression(
                      mod, assign->getFileContent(), assign->getAssignId(),
                      m_compileDesign, Reduce::Yes, nullptr, instance);
                }
              }

              uhdm::Constant* ccrhs = (uhdm::Constant*)crhs;
              const std::string_view s = ccrhs->getValue();
              Value* v1 = m_exprBuilder.fromVpiValue(s, ccrhs->getSize());
              Value* v2 = m_exprBuilder.fromVpiValue("INT:0", 64);
              if (*v1 > *v2) {
                rhs = crhs;
              }
            }
          }
          inst_assign->setRhs(rhs);
          break;
        }
      }
    }
    if ((overriden == false) && (!isMultidimensional)) {
      Value* value = instance->getValue(paramName, m_exprBuilder);
      if (value && value->isValid()) {
        uhdm::Constant* c = s.make<uhdm::Constant>();
        const uhdm::Any* orig_p = mod_assign->getLhs();
        if (orig_p->getUhdmType() == uhdm::UhdmType::Parameter) {
          if (uhdm::RefTypespec* rt =
                  ((uhdm::Parameter*)orig_p)->getTypespec()) {
            if (uhdm::Typespec* ag = rt->getActual()) {
              uhdm::RefTypespec* crt = s.make<uhdm::RefTypespec>();
              crt->setParent(c);
              crt->setActual(ag);
              c->setTypespec(crt);
            }
          }
        } else {
          if (uhdm::RefTypespec* rt =
                  ((uhdm::TypeParameter*)orig_p)->getTypespec()) {
            if (uhdm::Typespec* ag = rt->getActual()) {
              uhdm::RefTypespec* crt = s.make<uhdm::RefTypespec>();
              crt->setParent(c);
              crt->setActual(ag);
              c->setTypespec(crt);
            }
          }
        }
        c->setValue(value->uhdmValue());
        c->setDecompile(value->decompiledValue());
        c->setSize(value->getSize());
        c->setConstType(value->vpiValType());
        c->setParent(inst_assign);
        if (const uhdm::Typespec* ts = value->getTypespec()) {
          if (c->getTypespec() == nullptr) {
            uhdm::RefTypespec* tsRef = s.make<uhdm::RefTypespec>();
            tsRef->setParent(c);
            c->setTypespec(tsRef);
          }
          c->getTypespec()->setActual((uhdm::Typespec*)ts);
        }
        assign->getFileContent()->populateCoreMembers(assign->getAssignId(),
                                                      assign->getAssignId(), c);
        inst_assign->setRhs(c);
        const uhdm::Typespec* tps = nullptr;
        if (const uhdm::RefTypespec* rt = c->getTypespec()) {
          tps = rt->getActual();
        }
        m_helper.adjustSize(tps, instance->getDefinition(), m_compileDesign,
                            instance, c);
        if (en_replay && m_helper.errorOnNegativeConstant(
                             mod, c, m_compileDesign, instance)) {
          bool replay = false;
          // GDB: p replay=true
          if (replay) {
            instance->getValue(paramName, m_exprBuilder);
          }
        }

        overriden = true;
      }
    }
    if (overriden == false) {
      uhdm::Expr* exp = instance->getComplexValue(paramName);
      if (exp) {
        if (!isMultidimensional) {
          bool invalidValue = false;
          m_helper.checkForLoops(true);
          if (uhdm::Expr* tmp = m_helper.reduceExpr(
                  exp, invalidValue, mod, m_compileDesign, instance,
                  fileSystem->toPathId(exp->getFile(), symbols),
                  exp->getStartLine(), nullptr, true)) {
            if (!invalidValue) exp = tmp;
          }
          m_helper.checkForLoops(false);
        }
        exp->setParent(inst_assign);
        inst_assign->setRhs(exp);

        if (en_replay && m_helper.errorOnNegativeConstant(
                             mod, exp, m_compileDesign, instance)) {
          bool replay = false;
          // GDB: p replay=true
          if (replay) {
            uhdm::Expr* exp = instance->getComplexValue(paramName);
            if (exp) {
              if (!isMultidimensional) {
                bool invalidValue = false;
                m_helper.checkForLoops(true);
                if (uhdm::Expr* tmp = m_helper.reduceExpr(
                        exp, invalidValue, mod, m_compileDesign, instance,
                        fileSystem->toPathId(exp->getFile(), symbols),
                        exp->getStartLine(), nullptr, true)) {
                  if (!invalidValue) exp = tmp;
                }
                m_helper.checkForLoops(false);
              }
            }
          }
        }
        overriden = true;
      } else if (instance->isOverridenParam(paramName)) {
        // simple value
        Value* value = instance->getValue(paramName, m_exprBuilder);
        if (value && value->isValid()) {
          uhdm::Constant* c = s.make<uhdm::Constant>();
          const uhdm::Any* orig_p = mod_assign->getLhs();
          if (orig_p->getUhdmType() == uhdm::UhdmType::Parameter) {
            if (uhdm::RefTypespec* rt =
                    ((uhdm::Parameter*)orig_p)->getTypespec()) {
              if (uhdm::Typespec* ag = rt->getActual()) {
                uhdm::RefTypespec* crt = s.make<uhdm::RefTypespec>();
                crt->setParent(c);
                crt->setActual(ag);
                c->setTypespec(crt);
              }
            }
          } else {
            if (uhdm::RefTypespec* rt =
                    ((uhdm::TypeParameter*)orig_p)->getTypespec()) {
              if (uhdm::Typespec* ag = rt->getActual()) {
                uhdm::RefTypespec* crt = s.make<uhdm::RefTypespec>();
                crt->setParent(c);
                crt->setActual(ag);
                c->setTypespec(crt);
              }
            }
          }
          c->setValue(value->uhdmValue());
          c->setDecompile(value->decompiledValue());
          c->setSize(value->getSize());
          c->setConstType(value->vpiValType());
          assign->getFileContent()->populateCoreMembers(
              assign->getAssignId(), assign->getAssignId(), c);
          inst_assign->setRhs(c);
          overriden = true;
        }
      }
    }
    if (overriden == false) {
      // Default
      if (assign->getAssignId()) {
        m_helper.checkForLoops(true);
        uhdm::Expr* rhs = (uhdm::Expr*)m_helper.compileExpression(
            mod, assign->getFileContent(), assign->getAssignId(),
            m_compileDesign, isMultidimensional ? Reduce::No : Reduce::Yes,
            inst_assign, instance);
        m_helper.checkForLoops(false);
        inst_assign->setRhs(rhs);
      }
    }
    if (inst_assign->getRhs() &&
        m_helper.isOverloaded(inst_assign->getRhs(), m_compileDesign,
                              instance)) {
      inst_assign->setOverriden(true);
    }
    if (const uhdm::Any* lhs = inst_assign->getLhs()) {
      const uhdm::Typespec* tps = nullptr;
      if (lhs->getUhdmType() == uhdm::UhdmType::Parameter) {
        if (const uhdm::RefTypespec* rt =
                ((uhdm::Parameter*)lhs)->getTypespec()) {
          tps = rt->getActual();
        }
      } else {
        if (const uhdm::RefTypespec* rt =
                ((uhdm::TypeParameter*)lhs)->getTypespec()) {
          tps = rt->getActual();
        }
      }
      if (tps) {
        if (m_helper.isOverloaded(tps, m_compileDesign, instance)) {
          inst_assign->setOverriden(true);
        }
        const uhdm::Any* rhs = inst_assign->getRhs();
        if (rhs && rhs->getUhdmType() == uhdm::UhdmType::Constant) {
          uhdm::Constant* c = (uhdm::Constant*)rhs;
          m_helper.adjustSize(tps, instance->getDefinition(), m_compileDesign,
                              instance, c);
        }
      }
    }
    if (inst_assign) assigns->push_back(inst_assign);
  }
  return true;
}

bool NetlistElaboration::elaborate_(ModuleInstance* instance, bool recurse) {
  if (instance->isElaborated()) return true;
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  uhdm::Serializer& s = m_compileDesign->getSerializer();
  instance->setElaborated();
  Netlist* netlist = instance->getNetlist();
  bool elabPortsNets = false;
  VObjectType insttype = instance->getType();
  if ((insttype != VObjectType::paInterface_instantiation) &&
      (insttype != VObjectType::paConditional_generate_construct) &&
      (insttype != VObjectType::paLoop_generate_construct) &&
      (insttype != VObjectType::paGenerate_item) &&
      (insttype != VObjectType::paGenerate_region) &&
      (insttype != VObjectType::paGenerate_module_conditional_statement) &&
      (insttype != VObjectType::paGenerate_interface_conditional_statement) &&
      (insttype != VObjectType::paGenerate_module_loop_statement) &&
      (insttype != VObjectType::paGenerate_interface_loop_statement) &&
      (insttype != VObjectType::paGenerate_module_named_block) &&
      (insttype != VObjectType::paGenerate_interface_named_block) &&
      (insttype != VObjectType::paGenerate_module_block) &&
      (insttype != VObjectType::paGenerate_interface_block) &&
      (insttype != VObjectType::paGenerate_module_item) &&
      (insttype != VObjectType::paGenerate_interface_item) &&
      (insttype != VObjectType::paGenerate_begin_end_block)) {
    elabPortsNets = true;
  }

  if (netlist == nullptr) {
    netlist = new Netlist(instance);
    instance->setNetlist(netlist);
  }

  elab_parameters_(instance, true);
  if (elabPortsNets) {
    elab_ports_nets_(instance, true);
  }
  elab_parameters_(instance, false);

  DesignComponent* childDef = instance->getDefinition();
  if (ModuleDefinition* mm =
          valuedcomponenti_cast<ModuleDefinition*>(childDef)) {
    VObjectType insttype = instance->getType();
    if (insttype == VObjectType::paInterface_instantiation) {
      elab_interface_(instance->getParent(), instance,
                      instance->getInstanceName(), instance->getModuleName(),
                      mm, fileSystem->copy(instance->getFileId(), symbols),
                      instance->getLineNb(), nullptr, "");
    }
  }

  elab_generates_(instance);

  if (elabPortsNets) {
    elab_ports_nets_(instance, false);
  }

  high_conn_(instance);

  DesignComponent* component = instance->getDefinition();
  if (component) {
    if (uhdm::ContAssignCollection* cassigns = component->getContAssigns()) {
      std::vector<uhdm::ContAssign*>* assigns = netlist->cont_assigns();
      if (assigns == nullptr) {
        netlist->cont_assigns(s.makeCollection<uhdm::ContAssign>());
        assigns = netlist->cont_assigns();
      }
      for (uhdm::ContAssign* assign : *cassigns) {
        assigns->push_back(assign);
      }
    }
    netlist->process_stmts(component->getProcesses());
  }

  if (recurse) {
    for (uint32_t i = 0; i < instance->getNbChildren(); i++) {
      elaborate_(instance->getChildren(i), recurse);
    }
  }
  return true;
}

ModuleInstance* NetlistElaboration::getInterfaceInstance_(
    ModuleInstance* instance, std::string_view portName) {
  ModuleInstance* parent = instance->getParent();
  const FileContent* fC = instance->getFileContent();
  NodeId Udp_instantiation = instance->getNodeId();
  VObjectType inst_type = fC->Type(Udp_instantiation);

  if ((inst_type == VObjectType::paUdp_instantiation) ||
      (inst_type == VObjectType::paModule_instantiation) ||
      (inst_type == VObjectType::paProgram_instantiation) ||
      (inst_type == VObjectType::paInterface_instantiation) ||
      (inst_type == VObjectType::paCmos_switch_instance) ||
      (inst_type == VObjectType::paEnable_gate_instance) ||
      (inst_type == VObjectType::paMos_switch_instance) ||
      (inst_type == VObjectType::paN_input_gate_instance) ||
      (inst_type == VObjectType::paN_output_gate_instance) ||
      (inst_type == VObjectType::paPass_enable_switch_instance) ||
      (inst_type == VObjectType::paPass_switch_instance) ||
      (inst_type == VObjectType::paPull_gate_instance)) {
    NodeId modId = fC->Child(Udp_instantiation);
    NodeId Udp_instance = fC->Sibling(modId);
    if (fC->Type(Udp_instance) == VObjectType::paParameter_value_assignment) {
      Udp_instance = fC->Sibling(Udp_instance);
    } else if (fC->Type(Udp_instance) == VObjectType::paDelay2 ||
               fC->Type(Udp_instance) == VObjectType::paDelay3) {
      Udp_instance = fC->Sibling(Udp_instance);
      if (Udp_instance == InvalidNodeId) {
        Udp_instance = fC->Child(Udp_instance);
      }
    }
    NodeId Net_lvalue;
    if (const NodeId Name_of_instance = fC->Child(Udp_instance);
        fC->Type(Name_of_instance) == VObjectType::paName_of_instance) {
      Net_lvalue = fC->Sibling(Name_of_instance);
    } else {
      Net_lvalue = Name_of_instance;
    }
    if (fC->Type(Net_lvalue) == VObjectType::paNet_lvalue) {
      while (Net_lvalue) {
        std::string sigName;
        NodeId sigId;
        if (fC->Type(Net_lvalue) == VObjectType::paNet_lvalue) {
          NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
          if (fC->Type(fC->Child(Hierarchical_identifier)) ==
              VObjectType::paHierarchical_identifier) {
            Hierarchical_identifier =
                fC->Child(fC->Child(Hierarchical_identifier));
          } else if (fC->Type(Hierarchical_identifier) !=
                     VObjectType::paPs_or_hierarchical_identifier) {
            Hierarchical_identifier = Net_lvalue;
          }
          sigId = Hierarchical_identifier;
          if (fC->Type(fC->Child(sigId)) == VObjectType::slStringConst) {
            sigId = fC->Child(sigId);
          }
          sigName = fC->SymName(sigId);
        } else if (fC->Type(Net_lvalue) == VObjectType::paExpression) {
          NodeId Primary = fC->Child(Net_lvalue);
          NodeId Primary_literal = fC->Child(Primary);
          sigId = fC->Child(Primary_literal);
          sigName = fC->SymName(sigId);
        }
        Net_lvalue = fC->Sibling(Net_lvalue);
      }
    } else if (fC->Type(Net_lvalue) ==
               VObjectType::paList_of_port_connections) {
      NodeId Named_port_connection = fC->Child(Net_lvalue);
      bool orderedConnection = false;
      if (fC->Type(Named_port_connection) ==
          VObjectType::paOrdered_port_connection) {
        orderedConnection = true;
      }

      NodeId MemNamed_port_connection = Named_port_connection;
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (fC->Type(formalId) == VObjectType::paDOTSTAR) {
          // .* connection
          break;
        }
        Named_port_connection = fC->Sibling(Named_port_connection);
      }

      Named_port_connection = MemNamed_port_connection;
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (!formalId) break;
        if (fC->Type(formalId) == VObjectType::paDOTSTAR) {
          // .* connection
          Named_port_connection = fC->Sibling(Named_port_connection);
          continue;
        }

        std::string_view formalName = fC->SymName(formalId);
        NodeId Expression = fC->Sibling(formalId);
        if (orderedConnection) {
          Expression = formalId;
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          NodeId formalNameId = fC->Child(Primary_literal);
          formalName = fC->SymName(formalNameId);
        } else {
          NodeId tmp = Expression;
          if (fC->Type(tmp) == VObjectType::paOPEN_PARENS) {
            tmp = fC->Sibling(tmp);
            if (fC->Type(tmp) ==
                VObjectType::paCLOSE_PARENS) {  // .p()  explicit disconnect
              Named_port_connection = fC->Sibling(Named_port_connection);
              continue;
            } else if (fC->Type(tmp) ==
                       VObjectType::paExpression) {  // .p(s) connection by name
              formalId = tmp;
              Expression = tmp;
            }
          }  // else .p implicit connection
        }
        NodeId sigId = formalId;
        if (fC->Type(Expression) == VObjectType::paAttribute_instance) {
          while (fC->Type(Expression) == VObjectType::paAttribute_instance)
            Expression = fC->Sibling(Expression);
        }
        if (Expression) {
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          sigId = fC->Child(Primary_literal);
        }
        std::string sigName;
        if (sigId && fC->Name(sigId)) sigName = fC->SymName(sigId);
        std::string baseName = sigName;
        std::string selectName;
        if (NodeId subId = fC->Sibling(sigId)) {
          if (fC->Name(subId)) {
            selectName = fC->SymName(subId);
            sigName += std::string(".") + selectName;
          }
        }
        if (formalName == portName) {
          for (auto inst : parent->getAllSubInstances()) {
            if (inst->getInstanceName() == sigName) {
              return inst;
            }
          }
        }
        Named_port_connection = fC->Sibling(Named_port_connection);
      }
    }
  }
  return nullptr;
}

bool NetlistElaboration::high_conn_(ModuleInstance* instance) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errors = m_session->getErrorContainer();
  ModuleInstance* parent = instance->getParent();
  DesignComponent* parent_comp = nullptr;
  if (parent) parent_comp = parent->getDefinition();
  const FileContent* fC = instance->getFileContent();
  NodeId Udp_instantiation = instance->getNodeId();
  uhdm::Serializer& s = m_compileDesign->getSerializer();
  Netlist* netlist = instance->getNetlist();
  VObjectType inst_type = fC->Type(Udp_instantiation);
  std::vector<uhdm::Port*>* ports = netlist->ports();
  DesignComponent* comp = instance->getDefinition();
  const std::vector<Signal*>* signals = nullptr;
  std::string instName = instance->getInstanceName();
  bool instanceArray = false;
  int32_t instanceArrayIndex = 0;
  {
    std::string indexS;
    bool inValue = false;
    if (!instName.empty()) {
      for (uint64_t i = instName.size() - 1; i > 1; i--) {
        char c = instName[i];
        if (c == '[') {
          break;
        }
        if (inValue) {
          indexS += c;
        }
        if (c == ']') {
          instanceArray = true;
          inValue = true;
        }
      }
    }
    if (!indexS.empty()) {
      std::reverse(indexS.begin(), indexS.end());
      instanceArrayIndex = std::atoll(indexS.c_str());
    }
  }
  if (comp) {
    signals = &comp->getPorts();
  }
  std::map<std::string_view, Signal*> allSignals;
  std::map<std::string_view, Signal*> allSignalsConst;
  if (signals) {
    for (Signal* s : *signals) {
      allSignals.emplace(s->getName(), s);
      allSignalsConst.emplace(s->getName(), s);
    }
  }
  if ((inst_type == VObjectType::paUdp_instantiation) ||
      (inst_type == VObjectType::paModule_instantiation) ||
      (inst_type == VObjectType::paProgram_instantiation) ||
      (inst_type == VObjectType::paInterface_instantiation) ||
      (inst_type == VObjectType::paCmos_switch_instance) ||
      (inst_type == VObjectType::paEnable_gate_instance) ||
      (inst_type == VObjectType::paMos_switch_instance) ||
      (inst_type == VObjectType::paN_input_gate_instance) ||
      (inst_type == VObjectType::paN_output_gate_instance) ||
      (inst_type == VObjectType::paPass_enable_switch_instance) ||
      (inst_type == VObjectType::paPass_switch_instance) ||
      (inst_type == VObjectType::paPull_gate_instance)) {
    /*
    n<DUT> u<178> t<StringConst> p<191> s<190> l<20>
    n<dut> u<179> t<StringConst> p<180> l<20>
    n<> u<180> t<Name_of_instance> p<190> c<179> s<185> l<20>
    n<i> u<181> t<StringConst> p<182> l<20>
    n<> u<182> t<Ps_or_hierarchical_identifier> p<185> c<181> s<184> l<20>
    n<> u<183> t<Constant_bit_select> p<184> l<20>
    n<> u<184> t<Constant_select> p<185> c<183> l<20>
    n<> u<185> t<Net_lvalue> p<190> c<182> s<189> l<20>
    n<o> u<186> t<StringConst> p<187> l<20>
    n<> u<187> t<Primary_literal> p<188> c<186> l<20>
    n<> u<188> t<Primary> p<189> c<187> l<20>
    n<> u<189> t<Expression> p<190> c<188> l<20>
    n<> u<190> t<Udp_instance> p<191> c<180> l<20>
    n<> u<191> t<Udp_instantiation> p<192> c<178> l<20>
    */
    NodeId modId = fC->Child(Udp_instantiation);
    NodeId Udp_instance = fC->Sibling(modId);
    if ((inst_type == VObjectType::paCmos_switch_instance) ||
        (inst_type == VObjectType::paEnable_gate_instance) ||
        (inst_type == VObjectType::paMos_switch_instance) ||
        (inst_type == VObjectType::paN_input_gate_instance) ||
        (inst_type == VObjectType::paN_output_gate_instance) ||
        (inst_type == VObjectType::paPass_enable_switch_instance) ||
        (inst_type == VObjectType::paPass_switch_instance) ||
        (inst_type == VObjectType::paPull_gate_instance)) {
      modId = fC->Child(fC->Parent(Udp_instantiation));
      Udp_instance = Udp_instantiation;
      // In the case of single instance, point to the delay or parameter
      NodeId tmp = fC->Sibling(modId);
      if ((fC->Type(tmp) == VObjectType::paParameter_value_assignment) ||
          (fC->Type(tmp) == VObjectType::paDelay2) ||
          (fC->Type(tmp) == VObjectType::paDelay3)) {
        Udp_instance = tmp;
      }
    }
    if (fC->Type(Udp_instance) == VObjectType::paParameter_value_assignment) {
      Udp_instance = fC->Sibling(Udp_instance);
    } else if (fC->Type(Udp_instance) == VObjectType::paDelay2 ||
               fC->Type(Udp_instance) == VObjectType::paDelay3) {
      m_helper.checkForLoops(true);
      uhdm::Expr* delay_expr = (uhdm::Expr*)m_helper.compileExpression(
          parent_comp, fC, Udp_instance, m_compileDesign, Reduce::Yes, nullptr,
          parent);
      m_helper.checkForLoops(false);
      uhdm::ExprCollection* delays = s.makeCollection<uhdm::Expr>();
      netlist->delays(delays);
      delays->push_back(delay_expr);
      Udp_instance = fC->Sibling(Udp_instance);
    }
    NodeId Net_lvalue;
    if (const NodeId Name_of_instance = fC->Child(Udp_instance);
        fC->Type(Name_of_instance) == VObjectType::paName_of_instance) {
      Net_lvalue = fC->Sibling(Name_of_instance);
      NodeId Name = fC->Child(Name_of_instance);
      NodeId Unpacked_dimension = fC->Sibling(Name);
      if (Unpacked_dimension) {
        int32_t size;
        m_helper.checkForLoops(true);
        uhdm::RangeCollection* ranges = m_helper.compileRanges(
            comp, fC, Unpacked_dimension, m_compileDesign, Reduce::Yes, nullptr,
            parent, size, false);
        m_helper.checkForLoops(false);
        netlist->ranges(ranges);
      }
    } else {
      Net_lvalue = Name_of_instance;
    }
    if (fC->Type(Net_lvalue) == VObjectType::paNet_lvalue) {
      uint32_t index = 0;
      while (Net_lvalue) {
        std::string sigName;
        NodeId sigId;
        bool bit_or_part_select = false;
        if (fC->Type(Net_lvalue) == VObjectType::paNet_lvalue) {
          NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
          if (fC->Type(fC->Child(Hierarchical_identifier)) ==
              VObjectType::paHierarchical_identifier) {
            Hierarchical_identifier =
                fC->Child(fC->Child(Hierarchical_identifier));
          } else if (fC->Type(Hierarchical_identifier) !=
                     VObjectType::paPs_or_hierarchical_identifier) {
            Hierarchical_identifier = Net_lvalue;
          }
          if (m_helper.isSelected(fC, Hierarchical_identifier))
            bit_or_part_select = true;
          sigId = Hierarchical_identifier;
          if (fC->Type(fC->Child(sigId)) == VObjectType::slStringConst) {
            sigId = fC->Child(sigId);
          }
          sigName = fC->SymName(sigId);
        } else if (fC->Type(Net_lvalue) == VObjectType::paExpression) {
          NodeId Primary = fC->Child(Net_lvalue);
          NodeId Primary_literal = fC->Child(Primary);
          if (fC->Type(Primary_literal) == VObjectType::paComplex_func_call)
            bit_or_part_select = true;
          sigId = fC->Child(Primary_literal);
          sigName = fC->SymName(sigId);
        }
        if (ports) {
          if (index < ports->size()) {
            uhdm::Port* p = (*ports)[index];

            if ((!bit_or_part_select) &&
                (fC->Type(sigId) == VObjectType::slStringConst)) {
              bool bitBlast = false;
              uhdm::Any* net = nullptr;
              if (parent) {
                net = bind_net_(fC, sigId, parent,
                                instance->getInstanceBinding(), sigName);
              }
              if (instanceArray) {
                if (parent) {
                  if (net) {
                    uhdm::UhdmType ntype = net->getUhdmType();
                    if (ntype == uhdm::UhdmType::LogicNet) {
                      uhdm::LogicNet* lnet = (uhdm::LogicNet*)net;
                      if (const uhdm::RefTypespec* rt = lnet->getTypespec()) {
                        if (const uhdm::LogicTypespec* tps =
                                rt->getActual<uhdm::LogicTypespec>()) {
                          if (tps->getRanges()) bitBlast = true;
                        }
                      }
                    } else if (ntype == uhdm::UhdmType::ArrayNet) {
                      uhdm::ArrayNet* lnet = (uhdm::ArrayNet*)net;
                      if (const uhdm::RefTypespec* rt = lnet->getTypespec()) {
                        if (const uhdm::ArrayTypespec* tps =
                                rt->getActual<uhdm::ArrayTypespec>()) {
                          if (tps->getRanges()) bitBlast = true;
                        }
                      }
                    }
                  }
                }
              }
              if (bitBlast) {
                uhdm::BitSelect* sel = s.make<uhdm::BitSelect>();
                sel->setName(sigName);
                uhdm::Constant* c = s.make<uhdm::Constant>();
                c->setValue("UINT:" + std::to_string(instanceArrayIndex));
                c->setDecompile(std::to_string(instanceArrayIndex));
                c->setSize(64);
                fC->populateCoreMembers(sigId, sigId, c);
                sel->setIndex(c);
                sel->setParent(p);
                p->setHighConn(sel);
                fC->populateCoreMembers(sigId, sigId, sel);
                sel->setActual(net);
              } else {
                uhdm::RefObj* ref = s.make<uhdm::RefObj>();
                fC->populateCoreMembers(sigId, sigId, ref);
                p->setHighConn(ref);
                ref->setParent(p);
                ref->setName(sigName);
                if (parent) {
                  ref->setFullName(parent->getFullPathName() + "." + sigName);
                  ref->setActual(net);
                }
              }
            } else {
              uhdm::Any* exp = nullptr;
              if (fC->Type(Net_lvalue) == VObjectType::paNet_lvalue) {
                NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
                if (fC->Type(fC->Child(Hierarchical_identifier)) ==
                    VObjectType::paHierarchical_identifier) {
                  Hierarchical_identifier =
                      fC->Child(fC->Child(Hierarchical_identifier));
                } else if (fC->Type(Hierarchical_identifier) !=
                           VObjectType::paPs_or_hierarchical_identifier) {
                  Hierarchical_identifier = Net_lvalue;
                }
                m_helper.checkForLoops(true);
                exp = m_helper.compileExpression(
                    parent_comp, fC, Hierarchical_identifier, m_compileDesign,
                    Reduce::Yes, p, parent);
                m_helper.checkForLoops(false);
              } else {
                m_helper.checkForLoops(true);
                exp = m_helper.compileExpression(parent_comp, fC, Net_lvalue,
                                                 m_compileDesign, Reduce::Yes,
                                                 p, parent);
                m_helper.checkForLoops(false);
              }
              if (exp != nullptr) {
                p->setHighConn(exp);
                exp->setParent(p);
              }
            }
          }
        }
        if ((inst_type == VObjectType::paCmos_switch_instance) ||
            (inst_type == VObjectType::paEnable_gate_instance) ||
            (inst_type == VObjectType::paMos_switch_instance) ||
            (inst_type == VObjectType::paN_input_gate_instance) ||
            (inst_type == VObjectType::paN_output_gate_instance) ||
            (inst_type == VObjectType::paPass_enable_switch_instance) ||
            (inst_type == VObjectType::paPass_switch_instance) ||
            (inst_type == VObjectType::paPull_gate_instance) ||
            (inst_type == VObjectType::paUdp_instantiation)) {
          uhdm::Port* p = s.make<uhdm::Port>();
          if (ports == nullptr) {
            ports = s.makeCollection<uhdm::Port>();
            netlist->ports(ports);
          }
          fC->populateCoreMembers(Net_lvalue, Net_lvalue, p);
          if ((fC->Type(sigId) == VObjectType::slStringConst) &&
              (!bit_or_part_select)) {
            uhdm::RefObj* ref = s.make<uhdm::RefObj>();
            fC->populateCoreMembers(sigId, sigId, ref);
            p->setHighConn(ref);
            ref->setName(sigName);
            ref->setParent(p);
            if (parent) {
              ref->setFullName(parent->getFullPathName() + "." + sigName);
              if (uhdm::Any* net =
                      bind_net_(fC, sigId, parent,
                                instance->getInstanceBinding(), sigName)) {
                ref->setActual(net);
              }
            }
          } else {
            NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
            if (fC->Type(fC->Child(Hierarchical_identifier)) ==
                VObjectType::paHierarchical_identifier) {
              Hierarchical_identifier =
                  fC->Child(fC->Child(Hierarchical_identifier));
            } else if (fC->Type(Hierarchical_identifier) !=
                       VObjectType::paPs_or_hierarchical_identifier) {
              Hierarchical_identifier = Net_lvalue;
            }
            m_helper.checkForLoops(true);
            uhdm::Any* exp = m_helper.compileExpression(
                parent_comp, fC, Hierarchical_identifier, m_compileDesign,
                Reduce::Yes, nullptr, parent);
            m_helper.checkForLoops(false);
            p->setHighConn(exp);
            exp->setParent(p);
            if (exp->getUhdmType() == uhdm::UhdmType::RefObj) {
              uhdm::RefObj* ref = (uhdm::RefObj*)exp;
              const std::string_view n = ref->getName();
              if (uhdm::Any* net =
                      bind_net_(fC, Hierarchical_identifier, parent,
                                instance->getInstanceBinding(), n)) {
                ref->setActual(net);
              }
            }
          }
          ports->push_back(p);
        }
        Net_lvalue = fC->Sibling(Net_lvalue);
        index++;
      }
    } else if (fC->Type(Net_lvalue) ==
               VObjectType::paList_of_port_connections) {
      /*
      n<TESTBENCH> u<195> t<StringConst> p<212> s<211> l<21>
      n<tb> u<196> t<StringConst> p<197> l<21>
      n<> u<197> t<Name_of_instance> p<211> c<196> s<210> l<21>
      n<observe> u<198> t<StringConst> p<203> s<202> l<21>
      n<o> u<199> t<StringConst> p<200> l<21>
      n<> u<200> t<Primary_literal> p<201> c<199> l<21>
      n<> u<201> t<Primary> p<202> c<200> l<21>
      n<> u<202> t<Expression> p<203> c<201> l<21>
      n<> u<203> t<Named_port_connection> p<210> c<198> s<209> l<21>
      n<drive> u<204> t<StringConst> p<209> s<208> l<21>
      n<i> u<205> t<StringConst> p<206> l<21>
      n<> u<206> t<Primary_literal> p<207> c<205> l<21>
      n<> u<207> t<Primary> p<208> c<206> l<21>
      n<> u<208> t<Expression> p<209> c<207> l<21>
      n<> u<209> t<Named_port_connection> p<210> c<204> l<21>
      n<> u<210> t<List_of_port_connections> p<211> c<203> l<21>
      n<> u<211> t<Hierarchical_instance> p<212> c<197> l<21>
      n<> u<212> t<Module_instantiation> p<213> c<195> l<21>
      */
      NodeId Named_port_connection = fC->Child(Net_lvalue);
      uint32_t index = 0;
      bool orderedConnection = false;
      if (fC->Type(Named_port_connection) ==
          VObjectType::paOrdered_port_connection) {
        orderedConnection = true;
      }

      bool wildcard = false;
      NodeId MemNamed_port_connection = Named_port_connection;
      uint32_t wildcardLineNumber = 0;
      uint16_t wildcardColumnNumber = 0;
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (fC->Type(formalId) == VObjectType::paDOTSTAR) {
          // .* connection
          wildcard = true;
          wildcardLineNumber = fC->Line(formalId);
          wildcardColumnNumber = fC->Column(formalId);
          break;
        }
        Named_port_connection = fC->Sibling(Named_port_connection);
      }

      Named_port_connection = MemNamed_port_connection;
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (!formalId) {
          Named_port_connection = fC->Sibling(Named_port_connection);
          index++;
          continue;
        }
        uhdm::AttributeCollection* attributes = nullptr;
        if (fC->Type(formalId) == VObjectType::paAttribute_instance) {
          attributes = m_helper.compileAttributes(parent_comp, fC, formalId,
                                                  m_compileDesign, nullptr);
          while (fC->Type(formalId) == VObjectType::paAttribute_instance) {
            formalId = fC->Sibling(formalId);
          }
        }
        if (fC->Type(formalId) == VObjectType::paDOTSTAR) {
          // .* connection
          Named_port_connection = fC->Sibling(Named_port_connection);
          continue;
        }

        NodeId sigId = formalId;
        std::string_view formalName = fC->SymName(formalId);
        NodeId Expression = fC->Sibling(formalId);
        if (orderedConnection) {
          Expression = formalId;
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          NodeId formalNameId = fC->Child(Primary_literal);
          formalName = fC->SymName(formalNameId);
        } else {
          NodeId tmp = Expression;
          if (fC->Type(tmp) == VObjectType::paOPEN_PARENS) {
            tmp = fC->Sibling(tmp);
            if (fC->Type(tmp) ==
                VObjectType::paCLOSE_PARENS) {  // .p()  explicit disconnect
              Named_port_connection = fC->Sibling(Named_port_connection);
              uhdm::Port* p = nullptr;
              if (ports) {
                if (index < ports->size()) {
                  if (orderedConnection) {
                    formalName = ((*signals)[index])->getName();
                    p = (*ports)[index];
                  } else {
                    for (uhdm::Port* pItr : *ports) {
                      if (pItr->getName() == formalName) {
                        p = pItr;
                        break;
                      }
                    }
                    if (p == nullptr) p = (*ports)[index];
                  }
                } else {
                  p = s.make<uhdm::Port>();
                  ports->push_back(p);
                  p->setName(formalName);
                  fC->populateCoreMembers(formalId, formalId, p);
                  if (!allSignalsConst.empty()) {
                    auto found = allSignalsConst.find(p->getName());
                    if (found == allSignalsConst.end()) {
                      Location loc(fileSystem->toPathId(p->getFile(), symbols),
                                   p->getStartLine(), p->getStartColumn(),
                                   symbols->registerSymbol(p->getName()));
                      Error err(ErrorDefinition::ELAB_UNKNOWN_PORT, loc);
                      errors->addError(err);
                    }
                  }
                }
              } else {
                ports = s.makeCollection<uhdm::Port>();
                netlist->ports(ports);
                p = s.make<uhdm::Port>();
                ports->push_back(p);
                p->setName(formalName);
                fC->populateCoreMembers(formalId, formalId, p);
              }
              uhdm::Operation* op = s.make<uhdm::Operation>();
              op->setOpType(vpiNullOp);
              fC->populateCoreMembers(tmp, tmp, op);
              op->setParent(p);
              p->setHighConn(op);
              index++;
              continue;
            } else if (fC->Type(tmp) ==
                       VObjectType::paExpression) {  // .p(s) connection by name
              sigId = tmp;
              Expression = tmp;
              if (!allSignalsConst.empty()) {
                auto found = allSignalsConst.find(formalName);
                if (found == allSignalsConst.end()) {
                  Location loc(fC->getFileId(formalId), fC->Line(formalId),
                               fC->Column(formalId),
                               symbols->registerSymbol(formalName));
                  Error err(ErrorDefinition::ELAB_UNKNOWN_PORT, loc);
                  errors->addError(err);
                }
              }
            }
          }  // else .p implicit connection
        }
        uhdm::Expr* hexpr = nullptr;
        if (fC->Type(Expression) == VObjectType::paAttribute_instance) {
          attributes = m_helper.compileAttributes(comp, fC, Expression,
                                                  m_compileDesign, nullptr);
          while (fC->Type(Expression) == VObjectType::paAttribute_instance)
            Expression = fC->Sibling(Expression);
        }
        if (Expression) {
          m_helper.checkForLoops(true);
          hexpr = (uhdm::Expr*)m_helper.compileExpression(
              parent_comp, fC, Expression, m_compileDesign, Reduce::Yes,
              nullptr, parent);
          m_helper.checkForLoops(false);
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          sigId = fC->Child(Primary_literal);
        }
        std::string sigName;
        bool modPort = true;
        if (hexpr && hexpr->getUhdmType() == uhdm::UhdmType::HierPath) {
          uhdm::HierPath* hier = (uhdm::HierPath*)hexpr;
          for (auto p : *hier->getPathElems()) {
            if (p->getUhdmType() != uhdm::UhdmType::RefObj) {
              modPort = false;
              break;
            }
          }
        }
        if (modPort) {
          if (fC->Type(sigId) == VObjectType::slStringConst)
            sigName = fC->SymName(sigId);
        }
        std::string baseName = sigName;
        std::string selectName;
        if (NodeId subId = fC->Sibling(sigId)) {
          if (fC->Name(subId)) {
            selectName = fC->SymName(subId);
            sigName += std::string(".") + selectName;
          }
        }
        uhdm::Port* p = nullptr;
        if (ports) {
          if (index < ports->size()) {
            if (orderedConnection) {
              formalName = ((*signals)[index])->getName();
              p = (*ports)[index];
            } else {
              for (uhdm::Port* pItr : *ports) {
                if (pItr->getName() == formalName) {
                  p = pItr;
                  break;
                }
              }
              if (p == nullptr) p = (*ports)[index];
            }
          } else {
            p = s.make<uhdm::Port>();
            ports->push_back(p);
          }
        } else {
          ports = s.makeCollection<uhdm::Port>();
          netlist->ports(ports);
          p = s.make<uhdm::Port>();
          ports->push_back(p);
        }
        uhdm::Any* net = nullptr;
        if (!sigName.empty()) {
          net = bind_net_(fC, sigId, parent, instance->getInstanceBinding(),
                          sigName);
        }

        if ((!sigName.empty()) && (hexpr == nullptr)) {
          uhdm::RefObj* ref = s.make<uhdm::RefObj>();
          fC->populateCoreMembers(sigId, sigId, ref);
          ref->setName(sigName);
          if (parent) {
            ref->setFullName(parent->getFullPathName() + "." + sigName);
            ref->setParent(p);
            p->setHighConn(ref);
            ref->setActual(net);
          }
        } else if (hexpr != nullptr) {
          if (hexpr && hexpr->getUhdmType() == uhdm::UhdmType::Operation) {
            uhdm::Operation* op = (uhdm::Operation*)hexpr;
            int32_t opType = op->getOpType();
            const uhdm::Typespec* tps = nullptr;
            if (p && p->getTypespec()) {
              tps = p->getTypespec()->getActual();
            }
            if (opType == vpiAssignmentPatternOp) {
              if (m_helper.substituteAssignedValue(hexpr, m_compileDesign)) {
                hexpr = m_helper.expandPatternAssignment(
                    tps, (uhdm::Expr*)hexpr, parent_comp, m_compileDesign,
                    Reduce::Yes, netlist->getParent());
              }
            }
            hexpr = (uhdm::Expr*)m_helper.defaultPatternAssignment(
                tps, (uhdm::Expr*)hexpr, parent_comp, m_compileDesign,
                Reduce::Yes, netlist->getParent());
            if (p) {
              if (const uhdm::Any* lowc = p->getLowConn()) {
                if (lowc->getUhdmType() == uhdm::UhdmType::RefObj) {
                  uhdm::RefObj* ref = (uhdm::RefObj*)lowc;
                  m_helper.reorderAssignmentPattern(
                      parent_comp, ref->getActual(), (uhdm::Expr*)hexpr,
                      m_compileDesign, netlist->getParent(), 0);
                }
              }
            }
          }
          p->setHighConn(hexpr);
          hexpr->setParent(p);
          if (hexpr->getUhdmType() == uhdm::UhdmType::RefObj) {
            ((uhdm::RefObj*)hexpr)->setParent(p);
            ((uhdm::RefObj*)hexpr)->setActual(net);
            if (parent) {
              ((uhdm::RefObj*)hexpr)
                  ->setFullName(StrCat(parent->getFullPathName(), ".",
                                       ((uhdm::RefObj*)hexpr)->getName()));
            }
          }
        }
        p->setName(formalName);
        if (attributes) {
          p->setAttributes(attributes);
          for (auto a : *attributes) a->setParent(p);
        }
        if (p->getStartLine() == 0) {
          fC->populateCoreMembers(formalId, formalId, p);
        }
        bool lowconn_is_nettype = false;
        if (const uhdm::Any* lc = p->getLowConn()) {
          if (lc->getUhdmType() == uhdm::UhdmType::RefObj) {
            uhdm::RefObj* rf = (uhdm::RefObj*)lc;
            fC->populateCoreMembers(formalId, formalId, rf);
            const uhdm::Any* act = rf->getActual();
            if (act && (act->getUhdmType() == uhdm::UhdmType::LogicNet))
              lowconn_is_nettype = true;
          }
        }
        if (net && (net->getUhdmType() == uhdm::UhdmType::Modport) &&
            (lowconn_is_nettype)) {
          Netlist* parentNetlist = parent->getNetlist();
          Netlist::ModportMap::iterator itr;
          uhdm::Modport* mp = nullptr;
          if (orderedConnection) {
            itr = netlist->getModportMap().find(formalName);
            if (itr != netlist->getModportMap().end()) {
              mp = (*itr).second.second;
            }
          } else {
            itr = parentNetlist->getModportMap().find(sigName);
            if (itr != parentNetlist->getModportMap().end()) {
              Modport* orig_modport = (*itr).second.first;
              ModuleDefinition* orig_interf = orig_modport->getParent();

              ModuleInstance* interfaceInstance =
                  new ModuleInstance(m_session, orig_interf, fC, sigId,
                                     instance, sigName, orig_interf->getName());
              Netlist* netlistInterf = new Netlist(interfaceInstance);
              interfaceInstance->setNetlist(netlistInterf);

              mp = elab_modport_(instance, interfaceInstance, formalName,
                                 orig_interf->getName(), orig_interf,
                                 fileSystem->toPathId(p->getFile(), symbols),
                                 p->getStartLine(), selectName, nullptr);
            }
          }
          if (mp) {
            uhdm::RefObj* ref = s.make<uhdm::RefObj>();
            ref->setFile(p->getFile());
            ref->setStartLine(p->getStartLine());
            ref->setStartColumn(p->getStartColumn());
            ref->setEndLine(p->getEndLine());
            ref->setEndColumn(p->getEndColumn());
            ref->setParent(p);
            ref->setActual(mp);
            p->setLowConn(ref);
          }
        } else if (net && (net->getUhdmType() == uhdm::UhdmType::Interface) &&
                   (lowconn_is_nettype)) {
          uhdm::BaseClass* sm = nullptr;
          if (orderedConnection) {
            Netlist::InstanceMap::iterator itr =
                netlist->getInstanceMap().find(formalName);
            if (itr != netlist->getInstanceMap().end()) {
              sm = (*itr).second.second;
            }
          } else {
            Netlist* parentNetlist = parent->getNetlist();
            Netlist::InstanceMap::iterator itr =
                parentNetlist->getInstanceMap().find(sigName);
            if (itr != parentNetlist->getInstanceMap().end()) {
              ModuleInstance* orig_instance = (*itr).second.first;
              ModuleDefinition* orig_interf =
                  (ModuleDefinition*)orig_instance->getDefinition();
              sm = elab_interface_(
                  instance, orig_instance, formalName, orig_interf->getName(),
                  orig_interf, fileSystem->copy(instance->getFileId(), symbols),
                  instance->getLineNb(), nullptr, "");
            }
          }
          if (sm) {
            uhdm::RefObj* ref = s.make<uhdm::RefObj>();
            ref->setParent(p);
            ref->setActual(sm);
            fC->populateCoreMembers(Named_port_connection,
                                    Named_port_connection, ref);
            p->setLowConn(ref);
          }
        }
        auto itr = allSignals.find(formalName);
        if (itr != allSignals.end()) {
          allSignals.erase(itr);
        }
        Named_port_connection = fC->Sibling(Named_port_connection);
        index++;
      }
      if (signals) {
        uint32_t formalSize = 0;
        if (ports) {
          formalSize = ports->size();
        }
        if (wildcard) {
          // Add missing ports
          uhdm::PortCollection* newPorts = s.makeCollection<uhdm::Port>();
          for (Signal* s1 : *signals) {
            const std::string_view sigName = s1->getName();
            bool found = false;
            uhdm::Port* pp = nullptr;
            for (uhdm::Port* p : *ports) {
              if (p->getName() == s1->getName()) {
                newPorts->push_back(p);
                found = true;
                pp = p;
                break;
              }
            }
            if (!found) {
              uhdm::Port* p = s.make<uhdm::Port>();
              p->setName(sigName);
              p->setFile(fileSystem->toPath(fC->getFileId()));
              p->setStartLine(wildcardLineNumber);
              p->setStartColumn(wildcardColumnNumber);
              p->setEndLine(wildcardLineNumber);
              p->setEndColumn(wildcardColumnNumber + 1);
              newPorts->push_back(p);
              pp = p;
            }
            if (pp->getHighConn() == nullptr) {
              uhdm::RefObj* ref = s.make<uhdm::RefObj>();
              ref->setFile(fileSystem->toPath(fC->getFileId()));
              ref->setStartLine(wildcardLineNumber);
              ref->setStartColumn(wildcardColumnNumber);
              ref->setEndLine(wildcardLineNumber);
              ref->setEndColumn(wildcardColumnNumber + 1);
              ref->setName(sigName);
              ref->setParent(pp);
              if (parent) {
                ref->setFullName(
                    StrCat(parent->getFullPathName(), ".", sigName));
                pp->setHighConn(ref);
                if (uhdm::Any* net =
                        bind_net_(fC, InvalidNodeId, parent,
                                  instance->getInstanceBinding(), sigName)) {
                  ref->setActual(net);
                }
              }
            }
          }
          netlist->ports(newPorts);
        } else if (index < formalSize) {
          // Add missing ports
          uhdm::PortCollection* newPorts = s.makeCollection<uhdm::Port>();
          for (Signal* s1 : *signals) {
            const std::string_view sigName = s1->getName();

            auto itr = allSignals.find(sigName);
            if (itr != allSignals.end()) {
              auto pair = (*itr);
              uhdm::Port* p = nullptr;
              for (uhdm::Port* pt : *ports) {
                if (pt->getName() == sigName) {
                  p = pt;
                  newPorts->push_back(p);
                  break;
                }
              }

              if (p) {
                if (NodeId defaultId = pair.second->getDefaultValue()) {
                  m_helper.checkForLoops(true);
                  if (uhdm::Expr* exp = (uhdm::Expr*)m_helper.compileExpression(
                          comp, fC, defaultId, m_compileDesign, Reduce::Yes, p,
                          instance)) {
                    p->setHighConn(exp);
                  }
                  m_helper.checkForLoops(false);
                }
              }
            } else {
              for (uhdm::Port* pt : *ports) {
                if (pt->getName() == sigName) {
                  newPorts->push_back(pt);
                  break;
                }
              }
            }
          }
          netlist->ports(newPorts);
        }
      }
    }
  }
  // Finally any unconnected ports with default value gets assigned the value
  if (ports) {
    for (auto p : *ports) {
      if (p->getHighConn() != nullptr) continue;
      auto found = allSignals.find(p->getName());
      if (found == allSignals.end()) continue;
      if (NodeId defaultId = (*found).second->getDefaultValue()) {
        m_helper.checkForLoops(true);
        if (uhdm::Expr* exp = (uhdm::Expr*)m_helper.compileExpression(
                comp, fC, defaultId, m_compileDesign, Reduce::Yes, p,
                instance)) {
          p->setHighConn(exp);
        }
        m_helper.checkForLoops(false);
      }
    }
  }
  return true;
}

Interface* NetlistElaboration::elab_interface_(
    ModuleInstance* instance, ModuleInstance* interf_instance,
    std::string_view instName, std::string_view defName, ModuleDefinition* mod,
    PathId fileId, uint32_t lineNb, uhdm::InterfaceArray* interf_array,
    std::string_view modPortName) {
  FileSystem* const fileSystem = m_session->getFileSystem();
  Netlist* netlist = instance->getNetlist();
  if (netlist == nullptr) {
    netlist = new Netlist(instance);
    instance->setNetlist(netlist);
  }
  uhdm::Serializer& s = m_compileDesign->getSerializer();
  uhdm::InterfaceCollection* subInterfaces = netlist->interfaces();
  if (subInterfaces == nullptr) {
    subInterfaces = s.makeCollection<uhdm::Interface>();
    netlist->interfaces(subInterfaces);
  }
  uhdm::Interface* sm = s.make<uhdm::Interface>();
  sm->setName(instName);
  sm->setDefName(defName);
  // sm->setFullName(??);
  sm->setFile(fileSystem->toPath(fileId));
  sm->setStartLine(lineNb);
  subInterfaces->push_back(sm);
  if (interf_array) {
    sm->setParent(interf_array);
    interf_array->getInstances()->push_back(sm);
    netlist->getInstanceMap().emplace(
        instName, std::make_pair(interf_instance, interf_array));
    netlist->getSymbolTable().emplace(instName, interf_array);
  } else {
    netlist->getInstanceMap().emplace(instName,
                                      std::make_pair(interf_instance, sm));
    netlist->getSymbolTable().emplace(instName, sm);
  }
  const std::string prefix = StrCat(instName, ".");
  elab_ports_nets_(instance, interf_instance, instance->getNetlist(),
                   interf_instance->getNetlist(), mod, prefix, true);
  elab_ports_nets_(instance, interf_instance, instance->getNetlist(),
                   interf_instance->getNetlist(), mod, prefix, false);
  // Modports
  ModuleDefinition::ModportSignalMap& orig_modports =
      mod->getModportSignalMap();
  uhdm::ModportCollection* dest_modports = s.makeCollection<uhdm::Modport>();
  for (auto& orig_modport : orig_modports) {
    const std::string modportfullname =
        StrCat(instName, ".", orig_modport.first);
    if (!modPortName.empty() && (modportfullname != modPortName)) continue;
    uhdm::Modport* dest_modport = s.make<uhdm::Modport>();
    dest_modport->setInterface(sm);
    dest_modport->setParent(sm);
    const FileContent* orig_fC = orig_modport.second.getFileContent();
    const NodeId orig_nodeId = orig_modport.second.getNodeId();
    orig_fC->populateCoreMembers(orig_nodeId, orig_nodeId, dest_modport);
    netlist->getModportMap().emplace(
        modportfullname, std::make_pair(&orig_modport.second, dest_modport));
    netlist->getSymbolTable().emplace(modportfullname, dest_modport);
    dest_modport->setName(orig_modport.first);
    uhdm::IODeclCollection* ios = s.makeCollection<uhdm::IODecl>();
    for (auto& sig : orig_modport.second.getPorts()) {
      const FileContent* const fC = sig.getFileContent();
      const NodeId nodeId = sig.getNodeId();
      const std::string_view sigName = sig.getName();
      uhdm::IODecl* io = s.make<uhdm::IODecl>();
      io->setName(sigName);
      io->setParent(dest_modport);
      uint32_t direction = UhdmWriter::getVpiDirection(sig.getDirection());
      io->setDirection(direction);
      fC->populateCoreMembers(nodeId, nodeId, io);
      uhdm::Any* net = bind_net_(interf_instance, sigName);
      if (net == nullptr) {
        net = bind_net_(instance, sigName);
      }
      if (net && (net->getUhdmType() == uhdm::UhdmType::Interface)) {
        uhdm::RefObj* n = s.make<uhdm::RefObj>();
        n->setName(sigName);
        n->setFullName(StrCat(instance->getFullPathName(), ".", sigName));
        fC->populateCoreMembers(nodeId, nodeId, n);
        if (sigName != instName)  // prevent loop in listener
          n->setActual(net);
        net = n;
        io->setExpr(net);
      } else {
        net->setParent(io);
        io->setExpr(net);
      }
      ios->push_back(io);
    }
    dest_modport->setIODecls(ios);
    dest_modports->push_back(dest_modport);
  }
  sm->setModports(dest_modports);
  if (Netlist* netl = interf_instance->getNetlist()) {
    if (auto vars = netl->variables()) {
      sm->setVariables(vars);
      for (auto v : *vars) {
        v->setParent(sm);
      }
    }
    if (auto vars = netl->ports()) {
      sm->setPorts(vars);
      for (auto v : *vars) {
        v->setParent(sm);
      }
    }
  }
  return sm;
}

uhdm::Modport* NetlistElaboration::elab_modport_(
    ModuleInstance* instance, ModuleInstance* interfaceInstance,
    std::string_view instName, std::string_view defName, ModuleDefinition* mod,
    PathId fileId, uint32_t lineNb, std::string_view modPortName,
    uhdm::InterfaceArray* interf_array) {
  Netlist* netlist = instance->getNetlist();
  std::string fullname = StrCat(instName, ".", modPortName);
  Netlist::ModportMap::iterator itr = netlist->getModportMap().find(fullname);
  if (itr == netlist->getModportMap().end()) {
    elab_interface_(instance, interfaceInstance, instName, defName, mod, fileId,
                    lineNb, interf_array, fullname);
  }
  itr = netlist->getModportMap().find(fullname);
  if (itr != netlist->getModportMap().end()) {
    return (*itr).second.second;
  }
  return nullptr;
}

bool NetlistElaboration::elab_generates_(ModuleInstance* instance) {
  uhdm::Serializer& s = m_compileDesign->getSerializer();
  Netlist* netlist = instance->getNetlist();
  DesignComponent* comp_def = instance->getDefinition();
  if (ModuleDefinition* mm =
          valuedcomponenti_cast<ModuleDefinition*>(comp_def)) {
    VObjectType insttype = instance->getType();
    if (insttype == VObjectType::paConditional_generate_construct ||
        insttype == VObjectType::paLoop_generate_construct ||
        insttype == VObjectType::paGenerate_begin_end_block ||
        insttype == VObjectType::paGenerate_item ||
        insttype == VObjectType::paGenerate_region ||
        insttype == VObjectType::paGenerate_module_conditional_statement ||
        insttype == VObjectType::paGenerate_interface_conditional_statement ||
        insttype == VObjectType::paGenerate_module_loop_statement ||
        insttype == VObjectType::paGenerate_interface_loop_statement ||
        insttype == VObjectType::paGenerate_module_named_block ||
        insttype == VObjectType::paGenerate_interface_named_block ||
        insttype == VObjectType::paGenerate_module_block ||
        insttype == VObjectType::paGenerate_interface_block ||
        insttype == VObjectType::paGenerate_module_item ||
        insttype == VObjectType::paGenerate_interface_item) {
      std::vector<uhdm::GenScopeArray*>* gen_scopes = netlist->gen_scopes();
      if (gen_scopes == nullptr) {
        gen_scopes = s.makeCollection<uhdm::GenScopeArray>();
        netlist->gen_scopes(gen_scopes);
      }

      const FileContent* fC = mm->getFileContents()[0];
      uhdm::GenScopeArray* gen_scope_array = s.make<uhdm::GenScopeArray>();
      uhdm::GenScopeCollection* vec = s.makeCollection<uhdm::GenScope>();
      uhdm::GenScope* gen_scope = s.make<uhdm::GenScope>();
      vec->push_back(gen_scope);
      gen_scope_array->setGenScopes(vec);
      fC->populateCoreMembers(mm->getGenBlockId(), mm->getGenBlockId(),
                              gen_scope);
      gen_scope->setName(instance->getInstanceName());
      fC->populateCoreMembers(mm->getGenBlockId(), mm->getGenBlockId(),
                              gen_scope_array);
      gen_scopes->push_back(gen_scope_array);

      if (mm->getContAssigns()) gen_scope->setContAssigns(mm->getContAssigns());
      if (mm->getProcesses()) gen_scope->setProcess(mm->getProcesses());
      if (mm->getParameters()) gen_scope->setParameters(mm->getParameters());
      if (mm->getParamAssigns())
        gen_scope->setParamAssigns(mm->getParamAssigns());

      elab_ports_nets_(instance, true);
      elab_ports_nets_(instance, false);

      gen_scope->setNets(netlist->nets());
      gen_scope->setRegArrays(netlist->array_vars());
    }
  }
  return true;
}

bool NetlistElaboration::elab_interfaces_(ModuleInstance* instance) {
  for (uint32_t i = 0; i < instance->getNbChildren(); i++) {
    ModuleInstance* child = instance->getChildren(i);
    Netlist* netlist = child->getNetlist();
    if (netlist == nullptr) {
      netlist = new Netlist(child);
      child->setNetlist(netlist);
    }
    DesignComponent* childDef = child->getDefinition();
    if (ModuleDefinition* mm =
            valuedcomponenti_cast<ModuleDefinition*>(childDef)) {
      VObjectType insttype = child->getType();
      if (insttype == VObjectType::paInterface_instantiation) {
        elab_interface_(instance, child, child->getInstanceName(),
                        child->getModuleName(), mm, child->getFileId(),
                        child->getLineNb(), nullptr, "");
      }
    }
  }

  return true;
}

bool NetlistElaboration::elab_ports_nets_(ModuleInstance* instance,
                                          bool ports) {
  Netlist* netlist = instance->getNetlist();
  DesignComponent* comp = instance->getDefinition();
  if (comp == nullptr) {
    return true;
  }
  return elab_ports_nets_(instance, instance, netlist, netlist, comp, "",
                          ports);
}

bool NetlistElaboration::elabSignal(Signal* sig, ModuleInstance* instance,
                                    ModuleInstance* child,
                                    Netlist* parentNetlist, Netlist* netlist,
                                    DesignComponent* comp,
                                    std::string_view prefix, bool signalIsPort,
                                    Reduce reduce) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  ErrorContainer* const errors = m_session->getErrorContainer();
  uhdm::Serializer& s = m_compileDesign->getSerializer();
  std::vector<uhdm::Net*>* nets = netlist->nets();
  std::vector<uhdm::Variables*>* vars = netlist->variables();
  std::vector<uhdm::ArrayNet*>* array_nets = netlist->array_nets();
  const FileContent* fC = sig->getFileContent();
  NodeId id = sig->getNodeId();
  NodeId packedDimension = sig->getPackedDimension();
  NodeId unpackedDimension = sig->getUnpackedDimension();
  // Nets pass
  const DataType* dtype = sig->getDataType();
  VObjectType subnettype = sig->getType();
  uhdm::Typespec* tps = nullptr;
  // Determine if the "signal" is a net or a var
  bool isNet = true;
  if ((dtype && (subnettype == VObjectType::slNoType)) || sig->isConst() ||
      sig->isVar() || (!sig->isStatic()) ||
      (subnettype == VObjectType::paClass_scope) ||
      (subnettype == VObjectType::slStringConst) ||
      (subnettype == VObjectType::paIntegerAtomType_Int) ||
      (subnettype == VObjectType::paIntegerAtomType_Integer) ||
      (subnettype == VObjectType::paIntegerAtomType_Byte) ||
      (subnettype == VObjectType::paIntegerAtomType_LongInt) ||
      (subnettype == VObjectType::paIntegerAtomType_Shortint) ||
      (subnettype == VObjectType::paString_type) ||
      (subnettype == VObjectType::paNonIntType_Real) ||
      (subnettype == VObjectType::paNonIntType_RealTime) ||
      (subnettype == VObjectType::paNonIntType_ShortReal) ||
      (subnettype == VObjectType::paEvent_type) ||
      (subnettype == VObjectType::paChandle_type) ||
      (subnettype == VObjectType::paIntVec_TypeBit) ||
      (subnettype == VObjectType::paEnum_base_type) ||
      ((!sig->isVar()) && (subnettype == VObjectType::paIntVec_TypeLogic))) {
    isNet = false;
  }
  if (sig->getDirection() == VObjectType::paPortDir_Out ||
      sig->getDirection() == VObjectType::paPortDir_Inp ||
      sig->getDirection() == VObjectType::paPortDir_Inout) {
    if ((!sig->isVar()) && (subnettype == VObjectType::paIntVec_TypeLogic)) {
      isNet = true;
    }
  }

  NodeId typeSpecId = sig->getTypespecId();
  if (typeSpecId) {
    m_helper.checkForLoops(true);
    tps = m_helper.compileTypespec(comp, fC, typeSpecId, m_compileDesign,
                                   reduce, nullptr, child, true);
    m_helper.checkForLoops(false);
  }
  if (tps == nullptr) {
    if (sig->getInterfaceTypeNameId()) {
      m_helper.checkForLoops(true);
      tps = m_helper.compileTypespec(comp, fC, sig->getInterfaceTypeNameId(),
                                     m_compileDesign, reduce, nullptr, child,
                                     true);
      m_helper.checkForLoops(false);
    }
  }
  if (tps) {
    uhdm::Typespec* tmp = tps;
    uhdm::UhdmType ttmp = tmp->getUhdmType();
    if (ttmp == uhdm::UhdmType::PackedArrayTypespec) {
      if (uhdm::RefTypespec* ert =
              ((uhdm::PackedArrayTypespec*)tmp)->getElemTypespec()) {
        tmp = ert->getActual();
      }
    } else if (ttmp == uhdm::UhdmType::StructTypespec) {
      uhdm::StructTypespec* the_tps = (uhdm::StructTypespec*)tmp;
      if (the_tps->getMembers()) {
        isNet = true;
        for (uhdm::TypespecMember* member : *the_tps->getMembers()) {
          if (const uhdm::Typespec* mtps = member->getTypespec()->getActual()) {
            uhdm::UhdmType mtype = mtps->getUhdmType();
            if (mtype != uhdm::UhdmType::LogicTypespec &&
                mtype != uhdm::UhdmType::StructTypespec) {
              isNet = false;
              break;
            }
          }
        }
      }
    } else if (ttmp == uhdm::UhdmType::EnumTypespec) {
      isNet = false;
    } else if (ttmp == uhdm::UhdmType::BitTypespec) {
      isNet = false;
    } else if (ttmp == uhdm::UhdmType::ByteTypespec) {
      isNet = false;
    } else if (ttmp == uhdm::UhdmType::RealTypespec) {
      isNet = false;
    } else if (ttmp == uhdm::UhdmType::ClassTypespec) {
      isNet = false;
    } else if (ttmp == uhdm::UhdmType::InterfaceTypespec) {
      if (!signalIsPort) {
        Location loc1(fC->getFileId(), fC->Line(id), fC->Column(id),
                      symbols->registerSymbol(sig->getName()));
        Error err(ErrorDefinition::ELAB_USE_INTERFACE_AS_SIGNAL_TYPE, loc1);
        errors->addError(err);
      }
      // Don't create a signal
      return isNet;
    }
  }

  if (!isNet) {
    if (vars == nullptr) {
      vars = s.makeCollection<uhdm::Variables>();
      netlist->variables(vars);
    }
  }

  const std::string_view signame = sig->getName();
  const std::string parentSymbol = StrCat(prefix, signame);

  // Packed and unpacked ranges
  int32_t packedSize;
  int32_t unpackedSize;
  m_helper.checkForLoops(true);
  std::vector<uhdm::Range*>* packedDimensions =
      m_helper.compileRanges(comp, fC, packedDimension, m_compileDesign, reduce,
                             nullptr, child, packedSize, false);
  m_helper.checkForLoops(false);
  m_helper.checkForLoops(true);
  std::vector<uhdm::Range*>* unpackedDimensions =
      m_helper.compileRanges(comp, fC, unpackedDimension, m_compileDesign,
                             reduce, nullptr, child, unpackedSize, false);
  m_helper.checkForLoops(false);
  uhdm::Any* obj = nullptr;

  // Assignment to a default value
  uhdm::Expr* exp = exprFromAssign_(comp, fC, id, unpackedDimension, child);
  if ((exp == nullptr) && sig->getDefaultValue()) {
    m_helper.checkForLoops(true);
    exp = (uhdm::Expr*)m_helper.compileExpression(
        comp, fC, sig->getDefaultValue(), m_compileDesign, reduce, nullptr,
        child);
    m_helper.checkForLoops(false);
  }
  if (isNet) {
    // Nets
    if (dtype) {
      dtype = dtype->getActual();
      if (const DummyType* en = datatype_cast<const DummyType*>(dtype)) {
        uhdm::Typespec* spec = en->getTypespec();
        if (spec->getUhdmType() == uhdm::UhdmType::LogicTypespec) {
          uhdm::LogicNet* logicn = s.make<uhdm::LogicNet>();
          if (sig->attributes()) {
            logicn->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(logicn);
          }
          logicn->setSigned(sig->isSigned());
          logicn->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
          // Move range to typespec for simple types
          // logicn->setRanges(packedDimensions);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(logicn);
          rt->setActual(spec);
          logicn->setTypespec(rt);
          logicn->setName(signame);
          spec->setParent(logicn);
          obj = logicn;
        } else if (spec->getUhdmType() == uhdm::UhdmType::StructTypespec) {
          uhdm::StructNet* stv = s.make<uhdm::StructNet>();
          if (sig->attributes()) {
            stv->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(stv);
          }
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(stv);
          rt->setActual(spec);
          stv->setTypespec(rt);
          spec->setParent(stv);
          obj = stv;
          if (packedDimensions) {
            uhdm::PackedArrayNet* pnets = s.make<uhdm::PackedArrayNet>();
            pnets->setRanges(packedDimensions);
            pnets->setElements(s.makeCollection<Any>());
            pnets->getElements()->push_back(stv);
            stv->setParent(pnets);
            for (auto r : *packedDimensions) r->setParent(pnets);
            obj = pnets;
          }
        } else if (spec->getUhdmType() == uhdm::UhdmType::EnumTypespec) {
          uhdm::EnumNet* stv = s.make<uhdm::EnumNet>();
          if (sig->attributes()) {
            stv->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(stv);
          }
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(stv);
          rt->setActual(spec);
          stv->setTypespec(rt);
          spec->setParent(stv);
          obj = stv;
          if (packedDimensions) {
            uhdm::PackedArrayNet* pnets = s.make<uhdm::PackedArrayNet>();
            pnets->setRanges(packedDimensions);
            pnets->setElements(s.makeCollection<Any>());
            pnets->getElements()->push_back(stv);
            stv->setParent(pnets);
            for (auto r : *packedDimensions) r->setParent(pnets);
            obj = pnets;
          }
        } else if (spec->getUhdmType() == uhdm::UhdmType::BitTypespec) {
          uhdm::BitVar* logicn = s.make<uhdm::BitVar>();
          if (sig->attributes()) {
            logicn->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(logicn);
          }
          logicn->setSigned(sig->isSigned());
          // Move range to typespec for simple types
          // logicn->setRanges(packedDimensions);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(logicn);
          rt->setActual(spec);
          logicn->setTypespec(rt);
          logicn->setName(signame);
          spec->setParent(logicn);
          obj = logicn;
        } else if (spec->getUhdmType() == uhdm::UhdmType::ByteTypespec) {
          uhdm::ByteVar* logicn = s.make<uhdm::ByteVar>();
          if (sig->attributes()) {
            logicn->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(logicn);
          }
          logicn->setSigned(sig->isSigned());
          logicn->setName(signame);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(logicn);
          rt->setActual(spec);
          logicn->setTypespec(rt);
          spec->setParent(logicn);
          obj = logicn;
        } else {
          uhdm::Variables* var = m_helper.getSimpleVarFromTypespec(
              fC, id, id, spec, packedDimensions, m_compileDesign);
          if (sig->attributes()) {
            var->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(var);
          }
          var->setExpr(exp);
          var->setConstantVariable(sig->isConst());
          var->setSigned(sig->isSigned());
          var->setName(signame);
          exp->setParent(var);
          obj = var;
        }
      } else if (const Enum* en = datatype_cast<const Enum*>(dtype)) {
        uhdm::EnumNet* stv = s.make<uhdm::EnumNet>();
        stv->setName(signame);
        uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
        rt->setParent(stv);
        rt->setActual(en->getTypespec());
        stv->setTypespec(rt);
        if (sig->attributes()) {
          stv->setAttributes(sig->attributes());
          for (auto a : *sig->attributes()) a->setParent(stv);
        }
        obj = stv;
        if (packedDimensions) {
          uhdm::PackedArrayNet* pnets = s.make<uhdm::PackedArrayNet>();
          pnets->setRanges(packedDimensions);
          pnets->setElements(s.makeCollection<Any>());
          pnets->getElements()->push_back(stv);
          stv->setParent(pnets);
          for (auto r : *packedDimensions) r->setParent(pnets);
          obj = pnets;
          pnets->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
        } else {
          stv->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
        }
      } else if (const Struct* st = datatype_cast<const Struct*>(dtype)) {
        uhdm::StructNet* stv = s.make<uhdm::StructNet>();
        stv->setName(signame);
        if (sig->attributes()) {
          stv->setAttributes(sig->attributes());
          for (auto a : *sig->attributes()) a->setParent(stv);
        }
        uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
        rt->setParent(stv);
        rt->setActual(st->getTypespec());
        stv->setTypespec(rt);
        obj = stv;
        if (packedDimensions) {
          uhdm::PackedArrayNet* pnets = s.make<uhdm::PackedArrayNet>();
          pnets->setRanges(packedDimensions);
          pnets->setElements(s.makeCollection<Any>());
          pnets->getElements()->push_back(stv);
          stv->setParent(pnets);
          for (auto r : *packedDimensions) r->setParent(pnets);
          obj = pnets;
          pnets->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
        } else {
          stv->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
        }
      } else if (dtype->getCategory() == DataType::Category::PARAMETER ||
                 dtype->getCategory() == DataType::Category::SIMPLE_TYPEDEF) {
        uhdm::Typespec* spec = nullptr;
        if (dtype->getCategory() == DataType::Category::SIMPLE_TYPEDEF) {
          const SimpleType* sit = datatype_cast<const SimpleType*>(dtype);
          spec = sit->getTypespec();
        } else {
          const Parameter* param = datatype_cast<Parameter>(dtype);
          spec = param->getTypespec();
          if (spec == nullptr) {
            spec = tps;
          }
        }
        if (spec->getUhdmType() == uhdm::UhdmType::LogicTypespec) {
          uhdm::LogicNet* logicn = s.make<uhdm::LogicNet>();
          if (sig->attributes()) {
            logicn->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(logicn);
          }
          logicn->setSigned(sig->isSigned());
          logicn->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
          // Move range to typespec for simple types
          // logicn->setRanges(packedDimensions);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(logicn);
          rt->setActual(spec);
          logicn->setTypespec(rt);
          spec->setParent(logicn);
          logicn->setName(signame);
          obj = logicn;
        } else if (spec->getUhdmType() == uhdm::UhdmType::StructTypespec) {
          uhdm::StructNet* stv = s.make<uhdm::StructNet>();
          stv->setName(signame);
          if (sig->attributes()) {
            stv->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(stv);
          }
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(stv);
          rt->setActual(spec);
          stv->setTypespec(rt);
          spec->setParent(stv);
          obj = stv;
          if (packedDimensions) {
            uhdm::PackedArrayNet* pnets = s.make<uhdm::PackedArrayNet>();
            pnets->setRanges(packedDimensions);
            pnets->setElements(s.makeCollection<Any>());
            pnets->getElements()->push_back(stv);
            stv->setParent(pnets);
            for (auto r : *packedDimensions) r->setParent(pnets);
            obj = pnets;
            pnets->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
          } else {
            stv->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
          }
        } else if (spec->getUhdmType() == uhdm::UhdmType::EnumTypespec) {
          uhdm::EnumNet* stv = s.make<uhdm::EnumNet>();
          stv->setName(signame);
          if (sig->attributes()) {
            stv->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(stv);
          }
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(stv);
          rt->setActual(spec);
          stv->setTypespec(rt);
          spec->setParent(stv);
          obj = stv;
          if (packedDimensions) {
            uhdm::PackedArrayNet* pnets = s.make<uhdm::PackedArrayNet>();
            pnets->setRanges(packedDimensions);
            pnets->setElements(s.makeCollection<Any>());
            pnets->getElements()->push_back(stv);
            stv->setParent(pnets);
            for (auto r : *packedDimensions) r->setParent(pnets);
            obj = pnets;
            pnets->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
          } else {
            stv->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
          }
        } else if (spec->getUhdmType() == uhdm::UhdmType::BitTypespec) {
          uhdm::BitVar* logicn = s.make<uhdm::BitVar>();
          if (sig->attributes()) {
            logicn->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(logicn);
          }
          logicn->setSigned(sig->isSigned());
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(logicn);
          rt->setActual(spec);
          logicn->setTypespec(rt);
          spec->setParent(logicn);
          // Move range to typespec for simple types
          // logicn->setRanges(packedDimensions);
          logicn->setName(signame);
          obj = logicn;
        } else if (spec->getUhdmType() == uhdm::UhdmType::ByteTypespec) {
          uhdm::ByteVar* logicn = s.make<uhdm::ByteVar>();
          if (sig->attributes()) {
            logicn->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(logicn);
          }
          logicn->setSigned(sig->isSigned());
          logicn->setName(signame);
          uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
          rt->setParent(logicn);
          rt->setActual(spec);
          logicn->setTypespec(rt);
          spec->setParent(logicn);
          obj = logicn;
        } else {
          uhdm::Variables* var = m_helper.getSimpleVarFromTypespec(
              fC, id, id, spec, packedDimensions, m_compileDesign);
          if (sig->attributes()) {
            var->setAttributes(sig->attributes());
            for (auto a : *sig->attributes()) a->setParent(var);
          }
          var->setExpr(exp);
          var->setConstantVariable(sig->isConst());
          var->setSigned(sig->isSigned());
          var->setName(signame);
          exp->setParent(var);
          obj = var;
        }
      } else {
        uhdm::LogicNet* logicn = s.make<uhdm::LogicNet>();
        if (sig->attributes()) {
          logicn->setAttributes(sig->attributes());
          for (auto a : *sig->attributes()) a->setParent(logicn);
        }
        logicn->setSigned(sig->isSigned());
        logicn->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
        uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
        rt->setParent(logicn);
        rt->setActual(tps);
        logicn->setTypespec(rt);
        tps->setParent(logicn);
        // Move range to typespec for simple types
        // logicn->setRanges(packedDimensions);
        logicn->setName(signame);
        obj = logicn;
      }

      if (unpackedDimensions) {
        uhdm::ArrayNet* array_net = s.make<uhdm::ArrayNet>();
        array_net->setNets(s.makeCollection<uhdm::Net>());
        array_net->setRanges(unpackedDimensions);
        array_net->setName(signame);
        array_net->setSize(unpackedSize);
        for (auto r : *unpackedDimensions) r->setParent(array_net);
        fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), array_net);
        if (array_nets == nullptr) {
          array_nets = s.makeCollection<uhdm::ArrayNet>();
          netlist->array_nets(array_nets);
        }
        array_nets->push_back(array_net);
        obj->setParent(array_net);
        uhdm::NetCollection* array_n = array_net->getNets();
        array_n->push_back((uhdm::Net*)obj);
      } else {
        if (nets == nullptr) {
          nets = s.makeCollection<uhdm::Net>();
          netlist->nets(nets);
        }
        uhdm::UhdmType nettype = obj->getUhdmType();
        if (nettype == uhdm::UhdmType::EnumNet) {
          ((uhdm::EnumNet*)obj)->setName(signame);
        } else if (nettype == uhdm::UhdmType::StructNet) {
          ((uhdm::StructNet*)obj)->setName(signame);
        } else if (nettype == uhdm::UhdmType::PackedArrayNet) {
          ((uhdm::PackedArrayNet*)obj)->setName(signame);
        }
        nets->push_back((uhdm::Net*)obj);
      }
    } else if (subnettype == VObjectType::paStruct_union) {
      // Implicit type
      uhdm::StructNet* stv = s.make<uhdm::StructNet>();
      stv->setName(signame);
      if (sig->attributes()) {
        stv->setAttributes(sig->attributes());
        for (auto a : *sig->attributes()) a->setParent(stv);
      }
      uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
      rt->setParent(stv);
      rt->setActual(tps);
      stv->setTypespec(rt);
      tps->setParent(stv);
      obj = stv;
      stv->setName(signame);
      if (nets == nullptr) {
        nets = s.makeCollection<uhdm::Net>();
        netlist->nets(nets);
      }
      nets->push_back(stv);
    } else if (tps && tps->getUhdmType() == uhdm::UhdmType::StructTypespec) {
      uhdm::StructNet* stv = s.make<uhdm::StructNet>();
      stv->setName(signame);
      uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
      rt->setParent(stv);
      rt->setActual(tps);
      stv->setTypespec(rt);
      tps->setParent(stv);
      obj = stv;
      if (unpackedDimensions) {
        uhdm::ArrayNet* array_net = s.make<uhdm::ArrayNet>();
        array_net->setNets(s.makeCollection<uhdm::Net>());
        array_net->setRanges(unpackedDimensions);
        array_net->setName(signame);
        array_net->setSize(unpackedSize);
        for (auto r : *unpackedDimensions) r->setParent(array_net);
        fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), array_net);
        if (array_nets == nullptr) {
          array_nets = s.makeCollection<uhdm::ArrayNet>();
          netlist->array_nets(array_nets);
        }
        array_nets->push_back(array_net);
        obj->setParent(array_net);
        uhdm::NetCollection* array_n = array_net->getNets();
        array_n->push_back((uhdm::Net*)obj);
      } else {
        if (nets == nullptr) {
          nets = s.makeCollection<uhdm::Net>();
          netlist->nets(nets);
        }
        if (obj->getUhdmType() == uhdm::UhdmType::EnumNet) {
          ((uhdm::EnumNet*)obj)->setName(signame);
        } else if (obj->getUhdmType() == uhdm::UhdmType::StructNet) {
          ((uhdm::StructNet*)obj)->setName(signame);
        }
        nets->push_back((uhdm::Net*)obj);
      }
    } else {
      uhdm::LogicNet* logicn = s.make<uhdm::LogicNet>();
      logicn->setSigned(sig->isSigned());
      logicn->setNetType(UhdmWriter::getVpiNetType(sig->getType()));
      if (sig->attributes()) {
        logicn->setAttributes(sig->attributes());
        for (auto a : *sig->attributes()) a->setParent(logicn);
      }
      if (tps != nullptr) {
        // Move range to typespec for simple types
        // logicn->setRanges(packedDimensions);
        uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
        rt->setParent(logicn);
        rt->setActual(tps);
        logicn->setTypespec(rt);
        tps->setParent(logicn);
      }
      if (unpackedDimensions) {
        fC->populateCoreMembers(id, id, logicn);
        uhdm::ArrayNet* array_net = s.make<uhdm::ArrayNet>();
        array_net->setNets(s.makeCollection<uhdm::Net>());
        array_net->setRanges(unpackedDimensions);
        array_net->setName(signame);
        array_net->setSize(unpackedSize);
        for (auto r : *unpackedDimensions) r->setParent(array_net);
        fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), array_net);
        if (array_nets == nullptr) {
          array_nets = s.makeCollection<uhdm::ArrayNet>();
          netlist->array_nets(array_nets);
        }
        array_nets->push_back(array_net);
        logicn->setParent(array_net);
        uhdm::NetCollection* array_n = array_net->getNets();
        array_n->push_back(logicn);
        obj = array_net;
        array_net->setAttributes(((Net*)logicn)->getAttributes());
      } else {
        logicn->setName(signame);
        logicn->setSigned(sig->isSigned());
        obj = logicn;
        if (nets == nullptr) {
          nets = s.makeCollection<uhdm::Net>();
          netlist->nets(nets);
        }
        nets->push_back(logicn);
      }
    }
    if (parentNetlist)
      parentNetlist->getSymbolTable().emplace(parentSymbol, obj);
    if (netlist) netlist->getSymbolTable().emplace(signame, obj);

    if (exp && (!signalIsPort)) {
      uhdm::ContAssign* assign = s.make<uhdm::ContAssign>();
      assign->setNetDeclAssign(true);
      fC->populateCoreMembers(id, id, assign);
      assign->setLhs((uhdm::Expr*)obj);
      assign->setRhs(exp);
      obj->setParent(assign);
      exp->setParent(assign);
      if (sig->getDelay()) {
        m_helper.checkForLoops(true);
        if (uhdm::Expr* delay_expr = (uhdm::Expr*)m_helper.compileExpression(
                comp, fC, sig->getDelay(), m_compileDesign, reduce, assign,
                child)) {
          assign->setDelay(delay_expr);
        }
        m_helper.checkForLoops(false);
      }
      std::vector<uhdm::ContAssign*>* assigns = netlist->cont_assigns();
      if (assigns == nullptr) {
        netlist->cont_assigns(s.makeCollection<uhdm::ContAssign>());
        assigns = netlist->cont_assigns();
      }
      assigns->push_back(assign);
    }
  } else {
    // Vars
    obj = makeVar_(comp, sig, packedDimensions, packedSize, unpackedDimensions,
                   unpackedSize, child, vars, exp, tps);
  }

  if (obj) {
    if (obj->getStartLine() == 0) {
      if (unpackedDimension) {
        fC->populateCoreMembers(id, unpackedDimension, obj);
      } else {
        fC->populateCoreMembers(id, id, obj);
      }
    }
    if (parentNetlist)
      parentNetlist->getSymbolTable().emplace(parentSymbol, obj);
    netlist->getSymbolTable().emplace(signame, obj);
  } else {
    // Unsupported type
    Location loc(fC->getFileId(), fC->Line(id), fC->Column(id),
                 symbols->registerSymbol(signame));
    Error err(ErrorDefinition::UHDM_UNSUPPORTED_SIGNAL, loc);
    errors->addError(err);
  }
  return isNet;
}

bool NetlistElaboration::elab_ports_nets_(
    ModuleInstance* instance, ModuleInstance* child, Netlist* parentNetlist,
    Netlist* netlist, DesignComponent* comp, std::string_view prefix,
    bool do_ports) {
  uhdm::Serializer& s = m_compileDesign->getSerializer();
  VObjectType compType = comp->getType();
  std::vector<uhdm::Port*>* ports = netlist->ports();
  std::set<std::string_view> portInterf;
  for (int32_t pass = 0; pass < 3; pass++) {
    const std::vector<Signal*>* signals = nullptr;
    if (compType == VObjectType::paModule_declaration ||
        compType == VObjectType::paConditional_generate_construct ||
        compType == VObjectType::paLoop_generate_construct ||
        compType == VObjectType::paGenerate_item ||
        compType == VObjectType::paGenerate_region ||
        compType == VObjectType::paGenerate_module_conditional_statement ||
        compType == VObjectType::paGenerate_interface_conditional_statement ||
        compType == VObjectType::paGenerate_module_loop_statement ||
        compType == VObjectType::paGenerate_interface_loop_statement ||
        compType == VObjectType::paGenerate_module_named_block ||
        compType == VObjectType::paGenerate_interface_named_block ||
        compType == VObjectType::paGenerate_module_block ||
        compType == VObjectType::paGenerate_interface_block ||
        compType == VObjectType::paGenerate_module_item ||
        compType == VObjectType::paGenerate_interface_item ||
        compType == VObjectType::paGenerate_begin_end_block ||
        compType == VObjectType::paInterface_declaration ||
        compType == VObjectType::paProgram_declaration) {
      if (pass == 1)
        signals = &comp->getSignals();
      else
        signals = &comp->getPorts();
    } else {
      continue;
    }
    int32_t portIndex = 0;
    int32_t lastPortDirection = vpiInout;
    for (Signal* sig : *signals) {
      const FileContent* fC = sig->getFileContent();
      NodeId id = sig->getNodeId();
      if (pass == 0) {
        if (!do_ports) continue;
        // Ports pass
        uhdm::Port* dest_port = s.make<uhdm::Port>();
        if (sig->getDirection() != VObjectType::slNoType) {
          lastPortDirection = UhdmWriter::getVpiDirection(sig->getDirection());
        }
        dest_port->setDirection(lastPortDirection);
        std::string signame;
        VObjectType nodeIdType = fC->Type(sig->getNodeId());
        if (nodeIdType == VObjectType::slStringConst) {
          signame = sig->getName();
          dest_port->setName(signame);
        } else if (nodeIdType == VObjectType::paPort) {
          NodeId PortName = fC->Child(sig->getNodeId());
          signame = fC->SymName(PortName);
          dest_port->setName(signame);
          NodeId Port_expr = fC->Sibling(PortName);
          if (fC->Type(Port_expr) == VObjectType::paPort_expression) {
            m_helper.checkForLoops(true);
            if (uhdm::Any* exp = m_helper.compileExpression(
                    comp, fC, Port_expr, m_compileDesign, Reduce::Yes, nullptr,
                    child, false)) {
              dest_port->setLowConn(exp);
            }
            m_helper.checkForLoops(false);
          }
        }
        fC->populateCoreMembers(id, id, dest_port);
        if (ports == nullptr) {
          ports = s.makeCollection<uhdm::Port>();
          netlist->ports(ports);
        }
        ports->push_back(dest_port);

        NodeId unpackedDimension = sig->getUnpackedDimension();
        int32_t unpackedSize;
        m_helper.checkForLoops(true);
        std::vector<uhdm::Range*>* unpackedDimensions = m_helper.compileRanges(
            comp, fC, unpackedDimension, m_compileDesign, Reduce::Yes, nullptr,
            child, unpackedSize, false);
        m_helper.checkForLoops(false);
        NodeId typeSpecId = sig->getTypespecId();
        if (typeSpecId) {
          uhdm::Typespec* tps = nullptr;
          m_helper.checkForLoops(true);
          tps =
              m_helper.compileTypespec(comp, fC, typeSpecId, m_compileDesign,
                                       Reduce::Yes, dest_port, instance, true);
          m_helper.checkForLoops(false);
          if (tps) {
            if (dest_port->getTypespec() == nullptr) {
              uhdm::RefTypespec* rt = s.make<uhdm::RefTypespec>();
              rt->setParent(dest_port);
              dest_port->setTypespec(rt);
            }
            dest_port->getTypespec()->setActual(tps);
          }
        }

        if (Modport* orig_modport = sig->getModport()) {
          portInterf.emplace(sig->getName());
          uhdm::RefObj* ref = s.make<uhdm::RefObj>();
          ref->setFullName(
              StrCat(instance->getFullPathName(), ".", sig->getName()));
          fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), ref);
          ref->setParent(dest_port);
          dest_port->setLowConn(ref);
          Netlist::ModportMap::iterator itr =
              netlist->getModportMap().find(signame);
          if (itr == netlist->getModportMap().end()) {
            ModuleDefinition* orig_interf = orig_modport->getParent();

            uhdm::InterfaceArray* array_int = nullptr;
            if (unpackedDimensions) {
              array_int = s.make<uhdm::InterfaceArray>();
              uhdm::InstanceCollection* vec =
                  s.makeCollection<uhdm::Instance>();
              array_int->setInstances(vec);
              array_int->setRanges(unpackedDimensions);
              array_int->setName(signame);
              array_int->setSize(unpackedSize);
              fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(),
                                      array_int);

              auto array = netlist->interface_arrays();
              if (array == nullptr) {
                netlist->interface_arrays(
                    s.makeCollection<uhdm::InterfaceArray>());
                array = netlist->interface_arrays();
              }
              array->push_back(array_int);
              ref->setActual(array_int);
            }

            if (unpackedDimensions) {
              for (int32_t index = 0; index < unpackedSize; index++) {
                std::string sigName(sig->getName());

                ModuleInstance* interfaceRefInstance =
                    getInterfaceInstance_(instance, sigName);
                StrAppend(&sigName, "[", index, "]");
                ModuleInstance* interfaceInstance = new ModuleInstance(
                    m_session, orig_interf, sig->getFileContent(),
                    sig->getNodeId(), instance, sigName,
                    orig_interf->getName());
                Netlist* netlistInterf = new Netlist(interfaceInstance);
                interfaceInstance->setNetlist(netlistInterf);
                if (interfaceRefInstance) {
                  for (auto& itr : interfaceRefInstance->getMappedValues()) {
                    interfaceInstance->setValue(itr.first, itr.second.first,
                                                m_exprBuilder,
                                                itr.second.second);
                  }
                }
                instance->addSubInstance(interfaceInstance);
                elab_modport_(instance, interfaceInstance, sigName,
                              orig_interf->getName(), orig_interf,
                              instance->getFileId(), instance->getLineNb(),
                              orig_modport->getName(), array_int);
              }
            } else {
              const std::string_view sigName = sig->getName();
              ModuleInstance* interfaceRefInstance =
                  getInterfaceInstance_(instance, sigName);

              ModuleInstance* interfaceInstance = new ModuleInstance(
                  m_session, orig_interf, sig->getFileContent(),
                  sig->getNodeId(), instance, signame, orig_interf->getName());
              Netlist* netlistInterf = new Netlist(interfaceInstance);
              interfaceInstance->setNetlist(netlistInterf);
              if (interfaceRefInstance) {
                for (auto& itr : interfaceRefInstance->getMappedValues()) {
                  interfaceInstance->setValue(itr.first, itr.second.first,
                                              m_exprBuilder, itr.second.second);
                }
              }

              uhdm::Modport* mp = elab_modport_(
                  instance, interfaceInstance, signame, orig_interf->getName(),
                  orig_interf, instance->getFileId(), instance->getLineNb(),
                  orig_modport->getName(), array_int);
              instance->addSubInstance(interfaceInstance);
              ref->setActual(mp);
            }

          } else {
            ref->setActual((*itr).second.second);
          }
        } else if (ModuleDefinition* orig_interf = sig->getInterfaceDef()) {
          portInterf.emplace(sig->getName());
          uhdm::RefObj* ref = s.make<uhdm::RefObj>();
          ref->setFullName(
              StrCat(instance->getFullPathName(), ".", sig->getName()));
          fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), ref);
          dest_port->setLowConn(ref);
          Netlist::InstanceMap::iterator itr =
              netlist->getInstanceMap().find(signame);
          if (itr == netlist->getInstanceMap().end()) {
            ModuleInstance* interfaceInstance = new ModuleInstance(
                m_session, orig_interf, sig->getFileContent(), sig->getNodeId(),
                instance, signame, orig_interf->getName());
            Netlist* netlistInterf = new Netlist(interfaceInstance);
            interfaceInstance->setNetlist(netlistInterf);

            uhdm::InterfaceArray* array_int = nullptr;
            if (unpackedDimensions) {
              array_int = s.make<uhdm::InterfaceArray>();
              uhdm::InstanceCollection* vec =
                  s.makeCollection<uhdm::Instance>();
              array_int->setInstances(vec);
              array_int->setRanges(unpackedDimensions);
              array_int->setName(signame);
              array_int->setSize(unpackedSize);

              auto array = netlist->interface_arrays();
              if (array == nullptr) {
                netlist->interface_arrays(
                    s.makeCollection<uhdm::InterfaceArray>());
                array = netlist->interface_arrays();
              }
              array->push_back(array_int);
              ref->setActual(array_int);
            }

            uhdm::Interface* sm = elab_interface_(
                instance, interfaceInstance, signame, orig_interf->getName(),
                orig_interf, instance->getFileId(), instance->getLineNb(),
                array_int, "");

            if (unpackedDimensions) {
            } else {
              ref->setActual(sm);

              auto interfs = netlist->interfaces();
              if (interfs == nullptr) {
                netlist->interfaces(s.makeCollection<uhdm::Interface>());
                interfs = netlist->interfaces();
              }
              interfs->push_back(sm);
            }

          } else {
            ref->setActual((*itr).second.second);
          }
        }

      } else if (pass == 1) {
        // Nets pass
        if (do_ports) continue;
        if (fC->Type(sig->getNodeId()) == VObjectType::slStringConst) {
          const std::string_view signame = sig->getName();
          if (portInterf.find(signame) == portInterf.end()) {
            bool sigIsPort = false;
            if (ports) {
              for (auto s : *ports) {
                if (s->getName() == signame) {
                  sigIsPort = true;
                }
              }
            }
            elabSignal(sig, instance, child, parentNetlist, netlist, comp,
                       prefix, sigIsPort, Reduce::Yes);
          }
        }

      } else if (pass == 2) {
        // Port low conn pass
        if (do_ports) continue;
        std::string signame;
        if (fC->Type(sig->getNodeId()) == VObjectType::slStringConst) {
          signame = sig->getName();
        } else {
          portIndex++;
          continue;
        }

        uhdm::Port* dest_port = (*netlist->ports())[portIndex];

        if (sig->getModport() || sig->getInterfaceDef()) {
          // No rebind
        } else {
          if (uhdm::Any* n = bind_net_(netlist->getParent(), signame)) {
            NodeId typeSpecId = sig->getTypespecId();
            if (fC->Type(typeSpecId) == VObjectType::paImplicit_data_type) {
              // interconnect
              if (n->getUhdmType() == uhdm::UhdmType::LogicNet) {
                uhdm::LogicNet* net = (uhdm::LogicNet*)n;
                net->setNetType(vpiNone);
              }
            }
            uhdm::RefObj* ref = s.make<uhdm::RefObj>();
            ref->setName(signame);
            ref->setFullName(netlist->getParent()->getFullPathName() + "." +
                             signame);
            fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), ref);
            ref->setActual(n);
            ref->setParent(dest_port);
            dest_port->setLowConn(ref);
          }
        }
      }
      portIndex++;
    }
  }

  return true;
}

uhdm::Any* NetlistElaboration::bind_net_(const FileContent* origfC, NodeId id,
                                         ModuleInstance* instance,
                                         ModuleInstance* boundInstance,
                                         std::string_view name) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  ErrorContainer* const errors = m_session->getErrorContainer();
  uhdm::Any* result = nullptr;
  if (boundInstance) {
    result = bind_net_(boundInstance, name);
  }
  ModuleInstance* itrInst = instance;
  while (result == nullptr) {
    if (itrInst == nullptr) break;
    const FileContent* fC = itrInst->getFileContent();
    NodeId Udp_instantiation = itrInst->getNodeId();
    VObjectType insttype = fC->Type(Udp_instantiation);

    result = bind_net_(itrInst, name);

    if ((insttype != VObjectType::paConditional_generate_construct) &&
        (insttype != VObjectType::paLoop_generate_construct) &&
        (insttype != VObjectType::paGenerate_item) &&
        (insttype != VObjectType::paGenerate_region) &&
        (insttype != VObjectType::paGenerate_module_conditional_statement) &&
        (insttype != VObjectType::paGenerate_interface_conditional_statement) &&
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
    }
    itrInst = itrInst->getParent();
  }
  if (instance && (result == nullptr)) {
    DesignComponent* component = instance->getDefinition();
    if (component) {
      for (const auto& tp : component->getTypeDefMap()) {
        TypeDef* tpd = tp.second;
        uhdm::Typespec* tps = tpd->getTypespec();
        if (tps && tps->getUhdmType() == uhdm::UhdmType::EnumTypespec) {
          uhdm::EnumTypespec* etps = (uhdm::EnumTypespec*)tps;
          for (auto n : *etps->getEnumConsts()) {
            if (n->getName() == name) {
              return n;
            }
          }
        }
      }
      for (const auto& tp : component->getDataTypeMap()) {
        const DataType* dt = tp.second;
        dt = dt->getActual();
        uhdm::Typespec* tps = dt->getTypespec();
        if (tps && tps->getUhdmType() == uhdm::UhdmType::EnumTypespec) {
          uhdm::EnumTypespec* etps = (uhdm::EnumTypespec*)tps;
          for (auto n : *etps->getEnumConsts()) {
            if (n->getName() == name) {
              return n;
            }
          }
        }
      }
    }
    m_helper.checkForLoops(true);
    result =
        m_helper.getValue(name, instance->getDefinition(), m_compileDesign,
                          Reduce::Yes, instance, BadPathId, 0, nullptr, true);
    m_helper.checkForLoops(false);
  }
  if ((instance != nullptr) && (result == nullptr)) {
    if (Netlist* netlist = instance->getNetlist()) {
      if (name.find('.') == std::string::npos) {  // Not for hierarchical names
        DesignComponent* component = instance->getDefinition();
        VObjectType implicitNetType =
            component->getDesignElement()
                ? component->getDesignElement()->m_defaultNetType
                : VObjectType::paNetType_Wire;
        if (implicitNetType == VObjectType::slNoType) {
          Location loc(origfC->getFileId(),
                       id ? origfC->Line(id) : instance->getLineNb(),
                       id ? origfC->Column(id) : instance->getColumnNb(),
                       symbols->registerSymbol(name));
          Error err(ErrorDefinition::ELAB_ILLEGAL_IMPLICIT_NET, loc);
          errors->addError(err);
        }
        // Implicit net
        uhdm::Serializer& s = m_compileDesign->getSerializer();
        uhdm::LogicNet* net = s.make<uhdm::LogicNet>();
        net->setName(name);
        net->setNetType(UhdmWriter::getVpiNetType(implicitNetType));
        origfC->populateCoreMembers(id, id, net);
        result = net;
        Netlist::SymbolTable& symbols = netlist->getSymbolTable();
        std::vector<uhdm::Net*>* nets = netlist->nets();
        if (nets == nullptr) {
          nets = s.makeCollection<uhdm::Net>();
          netlist->nets(nets);
        }
        nets->push_back(net);
        symbols.emplace(name, result);
      }
    }
  }
  return result;
}

uhdm::Any* NetlistElaboration::bind_net_(ModuleInstance* instance,
                                         std::string_view name) {
  uhdm::Any* result = nullptr;
  Netlist* netlist = instance->getNetlist();
  if (netlist) {
    Netlist::SymbolTable& symbols = netlist->getSymbolTable();
    Netlist::SymbolTable::iterator itr = symbols.find(name);
    if (itr != symbols.end()) {
      return (*itr).second;
    } else {
      std::string_view basename = name;
      std::string_view subname;
      if (basename.find('.') != std::string::npos) {
        subname = basename;
        subname = StringUtils::ltrim_until(subname, '.');
        basename = StringUtils::rtrim_until(basename, '.');
      }
      itr = symbols.find(basename);
      if (itr != symbols.end()) {
        uhdm::BaseClass* baseclass = (*itr).second;
        uhdm::Port* conn = any_cast<uhdm::Port>(baseclass);
        uhdm::RefObj* ref1 = nullptr;
        const uhdm::Interface* interf = nullptr;
        if (conn) {
          ref1 = any_cast<uhdm::RefObj>((uhdm::BaseClass*)conn->getLowConn());
        }
        if (ref1) {
          interf =
              any_cast<uhdm::Interface>((uhdm::BaseClass*)ref1->getActual());
        }
        if (interf == nullptr) {
          interf = any_cast<uhdm::Interface>(baseclass);
        }
        if ((interf == nullptr) && ref1) {
          uhdm::Modport* mport =
              any_cast<uhdm::Modport>((uhdm::BaseClass*)ref1->getActual());
          if (mport) {
            interf = mport->getInterface();
          }
        }
        if (interf) {
          uhdm::NetCollection* nets = interf->getNets();
          if (nets) {
            for (uhdm::Net* p : *nets) {
              if (p->getName() == subname) {
                return p;
              }
            }
          }
        } else {
          uhdm::Modport* mport = any_cast<uhdm::Modport>(baseclass);
          if (mport) {
            uhdm::IODeclCollection* ios = mport->getIODecls();
            if (ios) {
              for (uhdm::IODecl* decl : *ios) {
                if (decl->getName() == subname) {
                  return (uhdm::Any*)decl->getExpr();
                }
              }
            }
          }
        }
      } else {
        if (netlist->variables()) {
          for (uhdm::Variables* var : *netlist->variables()) {
            if (var->getName() == name) {
              return var;
            }
          }
        }
        if (netlist->array_vars()) {
          for (uhdm::Variables* var : *netlist->array_vars()) {
            if (var->getName() == name) {
              return var;
            }
          }
        }
        if (netlist->interfaces()) {
          for (uhdm::Interface* var : *netlist->interfaces()) {
            if (var->getName() == name) {
              return var;
            }
          }
          for (uhdm::Interface* var : *netlist->interfaces()) {
            std::string_view basename =
                StringUtils::rtrim_until(var->getName(), '[');
            if (basename == name) {
              return var;
            }
          }
        }
      }
    }
  }
  return result;
}
}  // namespace SURELOG
