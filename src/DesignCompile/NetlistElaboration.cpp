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

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Design/DesignComponent.h>
#include <Surelog/Design/DesignElement.h>
#include <Surelog/Design/DummyType.h>
#include <Surelog/Design/Enum.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/ModPort.h>
#include <Surelog/Design/ModuleDefinition.h>
#include <Surelog/Design/ModuleInstance.h>
#include <Surelog/Design/Netlist.h>
#include <Surelog/Design/ParamAssign.h>
#include <Surelog/Design/Parameter.h>
#include <Surelog/Design/SimpleType.h>
#include <Surelog/Design/Struct.h>
#include <Surelog/Design/Union.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/NetlistElaboration.h>
#include <Surelog/DesignCompile/UhdmWriter.h>
#include <Surelog/Package/Package.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Testbench/TypeDef.h>
#include <Surelog/Utils/StringUtils.h>

#include <algorithm>

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/uhdm.h>

namespace SURELOG {

namespace fs = std::filesystem;

using namespace UHDM;  // NOLINT (using a bunch of these)

NetlistElaboration::NetlistElaboration(CompileDesign* compileDesign)
    : TestbenchElaboration(compileDesign) {
  m_exprBuilder.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
  m_exprBuilder.setDesign(m_compileDesign->getCompiler()->getDesign());
  m_helper.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
  m_symbols = m_compileDesign->getCompiler()->getSymbolTable();
  m_errors = m_compileDesign->getCompiler()->getErrorContainer();
}

NetlistElaboration::~NetlistElaboration() {}

bool NetlistElaboration::elaboratePackages() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  // Packages
  auto& packageDefs = design->getPackageDefinitions();
  for (auto& packageDef : packageDefs) {
    Package* p = packageDef.second;
    for (Package* pack : {p->getUnElabPackage(), p}) {
      if (pack->getNetlist() == nullptr) {
        Netlist* netlist = new Netlist(nullptr);
        pack->setNetlist(netlist);
      }
      Netlist* netlist = pack->getNetlist();
      // Variables and nets in Packages
      std::set<Signal*> notSignals;
      TypespecCache tscache;
      for (Signal* sig : pack->getSignals()) {
        if (!elabSignal(sig, nullptr, nullptr, nullptr, netlist, pack, "",
                        false, tscache)) {
          notSignals.insert(sig);
        }
      }
      for (auto sig : notSignals) {
        for (std::vector<Signal*>::iterator itr = pack->getSignals().begin();
             itr != pack->getSignals().end(); itr++) {
          if ((*itr) == sig) {
            pack->getSignals().erase(itr);
            break;
          }
        }
      }
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
  Serializer& s = m_compileDesign->getSerializer();
  if (!instance) return true;
  Netlist* netlist = instance->getNetlist();
  if (netlist == nullptr) return true;
  bool en_replay =
      m_compileDesign->getCompiler()->getCommandLineParser()->replay();
  ModuleDefinition* mod =
      valuedcomponenti_cast<ModuleDefinition*>(instance->getDefinition());
  VectorOfparam_assign* assigns = netlist->param_assigns();
  if (!mod) {
    if (param_port) return true;
    for (const auto& mv : instance->getMappedValues()) {
      if (assigns == nullptr) {
        netlist->param_assigns(s.MakeParam_assignVec());
        assigns = netlist->param_assigns();
      }
      const std::string& paramName = mv.first;
      Value* value = mv.second.first;
      unsigned int line = mv.second.second;
      const FileContent* instfC = instance->getFileContent();
      if (value && value->isValid()) {
        parameter* p = s.MakeParameter();
        p->VpiName(paramName);
        param_assign* inst_assign = s.MakeParam_assign();
        inst_assign->VpiOverriden(instance->isOverridenParam(paramName));
        constant* c = s.MakeConstant();
        c->VpiValue(value->uhdmValue());
        c->VpiDecompile(value->decompiledValue());
        c->VpiFile(instfC->getFileName());
        c->VpiSize(value->getSize());
        c->VpiConstType(value->vpiValType());
        c->VpiLineNo(line);
        c->VpiEndLineNo(line);
        inst_assign->Lhs(p);
        inst_assign->Rhs(c);
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
      netlist->param_assigns(s.MakeParam_assignVec());
      assigns = netlist->param_assigns();
    }
    param_assign* mod_assign = assign->getUhdmParamAssign();
    isMultidimensional = assign->isMultidimensional();
    const std::string& paramName =
        assign->getFileContent()->SymName(assign->getParamId());
    if (mod_assign) {
      const any* rhs = mod_assign->Rhs();
      expr* complexVal = instance->getComplexValue(paramName);
      if (complexVal) {
        rhs = complexVal;
      }
      bool isOverriden = instance->isOverridenParam(paramName);
      if ((!isOverriden) || complexVal) {
        // Complex value(default or overriden), no simple value
        if (rhs && rhs->UhdmType() == uhdmoperation) {
          operation* op = (operation*)rhs;
          int opType = op->VpiOpType();
          if (opType == vpiCastOp || (opType == vpiMultiConcatOp) ||
              (opType == vpiConditionOp)) {
            isMultidimensional = false;
          }

          // Don't reduce these operations
          if (opType == vpiAssignmentPatternOp ||
              opType == vpiMultiAssignmentPatternOp) {
            ElaboratorListener listener(&s);
            param_assign* pclone =
                (param_assign*)UHDM::clone_tree(mod_assign, s, &listener);
            pclone->VpiParent((any*)mod_assign->VpiParent());
            pclone->VpiOverriden(instance->isOverridenParam(paramName));
            if (opType == vpiAssignmentPatternOp) {
              const any* lhs = pclone->Lhs();
              any* rhs = (any*)pclone->Rhs();
              if (complexVal) {
                rhs = UHDM::clone_tree(complexVal, s, &listener);
                rhs->VpiParent(pclone);
              }
              const typespec* ts = nullptr;
              if (lhs->UhdmType() == uhdmparameter) {
                ts = ((parameter*)lhs)->Typespec();
              }
              rhs = m_helper.expandPatternAssignment(ts, (expr*)rhs, mod,
                                                     m_compileDesign, instance);
              pclone->Rhs(rhs);
              m_helper.reorderAssignmentPattern(mod, lhs, rhs, m_compileDesign,
                                                instance, 0);

              if (lhs->UhdmType() == uhdmparameter) {
                parameter* p = (parameter*)lhs;
                if (const typespec* tps = p->Typespec()) {
                  UHDM::ExprEval eval;
                  eval.flattenPatternAssignments(s, tps, (expr*)rhs);
                } else if (rhs->UhdmType() == uhdmoperation) {
                  operation* op = (operation*)rhs;
                  if (const typespec* tps = op->Typespec()) {
                    UHDM::ExprEval eval;
                    eval.flattenPatternAssignments(s, tps, (expr*)rhs);
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

    param_assign* inst_assign = s.MakeParam_assign();
    inst_assign->VpiOverriden(instance->isOverridenParam(paramName));
    inst_assign->VpiFile(mod_assign->VpiFile());
    inst_assign->VpiLineNo(mod_assign->VpiLineNo());
    inst_assign->VpiColumnNo(mod_assign->VpiColumnNo());
    inst_assign->VpiEndLineNo(mod_assign->VpiEndLineNo());
    inst_assign->VpiEndColumnNo(mod_assign->VpiEndColumnNo());
    inst_assign->Lhs((any*)mod_assign->Lhs());

    bool overriden = false;
    for (Parameter* tpm :
         instance->getTypeParams()) {  // for parameters that do not resolve to
                                       // scalars (complex structs)
      if (tpm->getName() == paramName) {
        overriden = true;
        if (ModuleInstance* pinst = instance->getParent()) {
          ModuleDefinition* pmod =
              valuedcomponenti_cast<ModuleDefinition*>(pinst->getDefinition());
          expr* rhs = (expr*)m_helper.compileExpression(
              pmod, tpm->getFileContent(), tpm->getNodeId(), m_compileDesign,
              nullptr, pinst, !isMultidimensional);
          if (en_replay && m_helper.errorOnNegativeConstant(
                               pmod, rhs, m_compileDesign, pinst)) {
            bool replay = false;
            // GDB: p replay=true
            if (replay) {
              m_helper.compileExpression(pmod, tpm->getFileContent(),
                                         tpm->getNodeId(), m_compileDesign,
                                         nullptr, pinst, !isMultidimensional);
            }
          }

          // If it is a complex expression (! constant)...
          if ((!rhs) || (rhs && (rhs->UhdmType() != uhdmconstant))) {
            // But if this value can be reduced to a constant then take the
            // constant
            expr* crhs = (expr*)m_helper.compileExpression(
                mod, assign->getFileContent(), assign->getAssignId(),
                m_compileDesign, nullptr, instance, true);
            if (crhs && crhs->UhdmType() == uhdmconstant) {
              if (en_replay && m_helper.errorOnNegativeConstant(
                                   mod, crhs, m_compileDesign, instance)) {
                bool replay = false;
                // GDB: p replay=true
                if (replay) {
                  m_helper.compileExpression(
                      mod, assign->getFileContent(), assign->getAssignId(),
                      m_compileDesign, nullptr, instance, true);
                }
              }

              constant* ccrhs = (constant*)crhs;
              const std::string& s = ccrhs->VpiValue();
              Value* v1 = m_exprBuilder.fromVpiValue(s, ccrhs->VpiSize());
              Value* v2 = m_exprBuilder.fromVpiValue("INT:0", 64);
              if (*v1 > *v2) {
                rhs = crhs;
              }
            }
          }
          inst_assign->Rhs(rhs);
          break;
        }
      }
    }
    if ((overriden == false) && (!isMultidimensional)) {
      Value* value = instance->getValue(paramName, m_exprBuilder);
      if (value && value->isValid()) {
        constant* c = s.MakeConstant();
        const any* orig_p = mod_assign->Lhs();
        if (orig_p->UhdmType() == uhdmparameter) {
          c->Typespec((typespec*)((parameter*)orig_p)->Typespec());
        } else {
          c->Typespec((typespec*)((type_parameter*)orig_p)->Typespec());
        }
        c->VpiValue(value->uhdmValue());
        c->VpiDecompile(value->decompiledValue());
        c->VpiFile(assign->getFileContent()->getFileName());
        c->VpiSize(value->getSize());
        c->VpiConstType(value->vpiValType());
        c->VpiLineNo(assign->getFileContent()->Line(assign->getAssignId()));
        c->VpiColumnNo(assign->getFileContent()->Column(assign->getAssignId()));
        c->VpiEndLineNo(
            assign->getFileContent()->EndLine(assign->getAssignId()));
        c->VpiEndColumnNo(
            assign->getFileContent()->EndColumn(assign->getAssignId()));
        inst_assign->Rhs(c);
        m_helper.adjustSize(c->Typespec(), instance->getDefinition(),
                            m_compileDesign, instance, c);
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
      expr* exp = instance->getComplexValue(paramName);
      if (exp) {
        if (!isMultidimensional) {
          bool invalidValue = false;
          expr* tmp = m_helper.reduceExpr(
              exp, invalidValue, mod, m_compileDesign, instance, exp->VpiFile(),
              exp->VpiLineNo(), nullptr, true);
          if (tmp && (invalidValue == false)) exp = tmp;
        }
        inst_assign->Rhs(exp);

        if (en_replay && m_helper.errorOnNegativeConstant(
                             mod, exp, m_compileDesign, instance)) {
          bool replay = false;
          // GDB: p replay=true
          if (replay) {
            expr* exp = instance->getComplexValue(paramName);
            if (exp) {
              if (!isMultidimensional) {
                bool invalidValue = false;
                expr* tmp = m_helper.reduceExpr(
                    exp, invalidValue, mod, m_compileDesign, instance,
                    exp->VpiFile(), exp->VpiLineNo(), nullptr, true);
                if (tmp && (invalidValue == false)) exp = tmp;
              }
            }
          }
        }
        overriden = true;
      } else if (instance->isOverridenParam(paramName)) {
        // simple value
        Value* value = instance->getValue(paramName, m_exprBuilder);
        if (value && value->isValid()) {
          constant* c = s.MakeConstant();
          const any* orig_p = mod_assign->Lhs();
          if (orig_p->UhdmType() == uhdmparameter) {
            c->Typespec((typespec*)((parameter*)orig_p)->Typespec());
          } else {
            c->Typespec((typespec*)((type_parameter*)orig_p)->Typespec());
          }
          c->VpiValue(value->uhdmValue());
          c->VpiDecompile(value->decompiledValue());
          c->VpiFile(assign->getFileContent()->getFileName());
          c->VpiSize(value->getSize());
          c->VpiConstType(value->vpiValType());
          c->VpiLineNo(assign->getFileContent()->Line(assign->getAssignId()));
          c->VpiColumnNo(
              assign->getFileContent()->Column(assign->getAssignId()));
          c->VpiEndLineNo(
              assign->getFileContent()->EndLine(assign->getAssignId()));
          c->VpiEndColumnNo(
              assign->getFileContent()->EndColumn(assign->getAssignId()));
          inst_assign->Rhs(c);
          overriden = true;
        }
      }
    }
    if (overriden == false) {
      // Default
      if (assign->getAssignId()) {
        expr* rhs = (expr*)m_helper.compileExpression(
            mod, assign->getFileContent(), assign->getAssignId(),
            m_compileDesign, nullptr, instance, !isMultidimensional);
        inst_assign->Rhs(rhs);
      }
    }
    if (inst_assign->Rhs() &&
        m_helper.isOverloaded(inst_assign->Rhs(), m_compileDesign, instance)) {
      inst_assign->VpiOverriden(true);
    }
    if (const any* lhs = inst_assign->Lhs()) {
      const typespec* tps = nullptr;
      if (lhs->UhdmType() == uhdmparameter) {
        tps = ((parameter*)lhs)->Typespec();
      } else {
        tps = ((type_parameter*)lhs)->Typespec();
      }
      if (tps) {
        if (m_helper.isOverloaded(tps, m_compileDesign, instance)) {
          inst_assign->VpiOverriden(true);
        }
      }
    }
    if (inst_assign) assigns->push_back(inst_assign);
  }
  return true;
}

bool NetlistElaboration::elaborate_(ModuleInstance* instance, bool recurse) {
  if (instance->isElaborated()) return true;
  instance->setElaborated();
  Netlist* netlist = instance->getNetlist();
  bool elabPortsNets = false;
  VObjectType insttype = instance->getType();
  if ((insttype != VObjectType::slInterface_instantiation) &&
      (insttype != VObjectType::slConditional_generate_construct) &&
      (insttype != VObjectType::slLoop_generate_construct) &&
      (insttype != VObjectType::slGenerate_item) &&
      (insttype != VObjectType::slGenerate_module_conditional_statement) &&
      (insttype != VObjectType::slGenerate_interface_conditional_statement) &&
      (insttype != VObjectType::slGenerate_module_loop_statement) &&
      (insttype != VObjectType::slGenerate_interface_loop_statement) &&
      (insttype != VObjectType::slGenerate_module_named_block) &&
      (insttype != VObjectType::slGenerate_interface_named_block) &&
      (insttype != VObjectType::slGenerate_module_block) &&
      (insttype != VObjectType::slGenerate_interface_block) &&
      (insttype != VObjectType::slGenerate_module_item) &&
      (insttype != VObjectType::slGenerate_interface_item) &&
      (insttype != VObjectType::slGenerate_block)) {
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
    if (insttype == VObjectType::slInterface_instantiation) {
      elab_interface_(instance->getParent(), instance,
                      instance->getInstanceName(), instance->getModuleName(),
                      mm, instance->getFileName(), instance->getLineNb(),
                      nullptr, "");
    }
  }

  elab_generates_(instance);

  if (elabPortsNets) {
    elab_ports_nets_(instance, false);
  }

  high_conn_(instance);
  if (recurse) {
    for (unsigned int i = 0; i < instance->getNbChildren(); i++) {
      elaborate_(instance->getChildren(i), recurse);
    }
  }
  return true;
}

ModuleInstance* NetlistElaboration::getInterfaceInstance_(
    ModuleInstance* instance, const std::string& portName) {
  ModuleInstance* parent = instance->getParent();
  const FileContent* fC = instance->getFileContent();
  NodeId Udp_instantiation = instance->getNodeId();
  VObjectType inst_type = fC->Type(Udp_instantiation);

  if ((inst_type == VObjectType::slUdp_instantiation) ||
      (inst_type == VObjectType::slModule_instantiation) ||
      (inst_type == VObjectType::slProgram_instantiation) ||
      (inst_type == VObjectType::slInterface_instantiation) ||
      (inst_type == VObjectType::slGate_instantiation)) {
    NodeId modId = fC->Child(Udp_instantiation);
    NodeId Udp_instance = fC->Sibling(modId);
    if (fC->Type(Udp_instance) == VObjectType::slParameter_value_assignment) {
      Udp_instance = fC->Sibling(Udp_instance);
    } else if (fC->Type(Udp_instance) == VObjectType::slDelay2 ||
               fC->Type(Udp_instance) == VObjectType::slDelay3) {
      Udp_instance = fC->Sibling(Udp_instance);
    }
    NodeId Net_lvalue = 0;
    if (const NodeId Name_of_instance = fC->Child(Udp_instance);
        fC->Type(Name_of_instance) == slName_of_instance) {
      Net_lvalue = fC->Sibling(Name_of_instance);
    } else {
      Net_lvalue = Name_of_instance;
    }
    if (fC->Type(Net_lvalue) == VObjectType::slNet_lvalue) {
      unsigned int index = 0;
      while (Net_lvalue) {
        std::string sigName;
        NodeId sigId = 0;
        if (fC->Type(Net_lvalue) == VObjectType::slNet_lvalue) {
          NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
          if (fC->Type(fC->Child(Hierarchical_identifier)) ==
              slHierarchical_identifier) {
            Hierarchical_identifier =
                fC->Child(fC->Child(Hierarchical_identifier));
          } else if (fC->Type(Hierarchical_identifier) !=
                     slPs_or_hierarchical_identifier) {
            Hierarchical_identifier = Net_lvalue;
          }
          sigId = Hierarchical_identifier;
          if (fC->Type(fC->Child(sigId)) == slStringConst) {
            sigId = fC->Child(sigId);
          }
          sigName = fC->SymName(sigId);
        } else if (fC->Type(Net_lvalue) == VObjectType::slExpression) {
          NodeId Primary = fC->Child(Net_lvalue);
          NodeId Primary_literal = fC->Child(Primary);
          sigId = fC->Child(Primary_literal);
          sigName = fC->SymName(sigId);
        }
        Net_lvalue = fC->Sibling(Net_lvalue);
        index++;
      }
    } else if (fC->Type(Net_lvalue) ==
               VObjectType::slList_of_port_connections) {
      NodeId Named_port_connection = fC->Child(Net_lvalue);
      unsigned int index = 0;
      bool orderedConnection = false;
      if (fC->Type(Named_port_connection) ==
          VObjectType::slOrdered_port_connection) {
        orderedConnection = true;
      }

      NodeId MemNamed_port_connection = Named_port_connection;
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (fC->Type(formalId) == VObjectType::slDotStar) {
          // .* connection
          break;
        }
        Named_port_connection = fC->Sibling(Named_port_connection);
      }

      Named_port_connection = MemNamed_port_connection;
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (formalId == 0) break;
        if (fC->Type(formalId) == VObjectType::slDotStar) {
          // .* connection
          Named_port_connection = fC->Sibling(Named_port_connection);
          continue;
        }

        std::string formalName = fC->SymName(formalId);
        NodeId Expression = fC->Sibling(formalId);
        if (orderedConnection) {
          Expression = formalId;
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          NodeId formalNameId = fC->Child(Primary_literal);
          formalName = fC->SymName(formalNameId);
        } else {
          NodeId tmp = Expression;
          if (fC->Type(tmp) == slOpenParens) {
            tmp = fC->Sibling(tmp);
            if (fC->Type(tmp) == slCloseParens) {  // .p()  explicit disconnect
              Named_port_connection = fC->Sibling(Named_port_connection);
              index++;
              continue;
            } else if (fC->Type(tmp) ==
                       slExpression) {  // .p(s) connection by name
              formalId = tmp;
              Expression = tmp;
            }
          }  // else .p implicit connection
        }
        NodeId sigId = formalId;
        if (fC->Type(Expression) == slAttribute_instance) {
          while (fC->Type(Expression) == slAttribute_instance)
            Expression = fC->Sibling(Expression);
        }
        if (Expression) {
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          sigId = fC->Child(Primary_literal);
        }
        std::string sigName;
        if (fC->Name(sigId)) sigName = fC->SymName(sigId);
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
        index++;
      }
    }
  }
  return nullptr;
}

bool NetlistElaboration::high_conn_(ModuleInstance* instance) {
  ModuleInstance* parent = instance->getParent();
  DesignComponent* parent_comp = nullptr;
  if (parent) parent_comp = parent->getDefinition();
  const FileContent* fC = instance->getFileContent();
  NodeId Udp_instantiation = instance->getNodeId();
  Serializer& s = m_compileDesign->getSerializer();
  Netlist* netlist = instance->getNetlist();
  VObjectType inst_type = fC->Type(Udp_instantiation);
  std::vector<UHDM::port*>* ports = netlist->ports();
  DesignComponent* comp = instance->getDefinition();
  std::vector<Signal*>* signals = nullptr;
  if (comp) {
    signals = &comp->getPorts();
  }

  if ((inst_type == VObjectType::slUdp_instantiation) ||
      (inst_type == VObjectType::slModule_instantiation) ||
      (inst_type == VObjectType::slProgram_instantiation) ||
      (inst_type == VObjectType::slInterface_instantiation) ||
      (inst_type == VObjectType::slGate_instantiation)) {
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
    if (fC->Type(Udp_instance) == VObjectType::slParameter_value_assignment) {
      Udp_instance = fC->Sibling(Udp_instance);
    } else if (fC->Type(Udp_instance) == VObjectType::slDelay2 ||
               fC->Type(Udp_instance) == VObjectType::slDelay3) {
      expr* delay_expr = (expr*)m_helper.compileExpression(
          parent_comp, fC, Udp_instance, m_compileDesign, nullptr, parent,
          true);
      VectorOfexpr* delays = s.MakeExprVec();
      netlist->delays(delays);
      delays->push_back(delay_expr);
      Udp_instance = fC->Sibling(Udp_instance);
    }
    NodeId Net_lvalue = 0;
    if (const NodeId Name_of_instance = fC->Child(Udp_instance);
        fC->Type(Name_of_instance) == slName_of_instance) {
      Net_lvalue = fC->Sibling(Name_of_instance);
      NodeId Name = fC->Child(Name_of_instance);
      NodeId Unpacked_dimension = fC->Sibling(Name);
      if (Unpacked_dimension) {
        int size;
        VectorOfrange* ranges = m_helper.compileRanges(
            comp, fC, Unpacked_dimension, m_compileDesign, nullptr, parent,
            true, size, false);
        netlist->ranges(ranges);
      }
    } else {
      Net_lvalue = Name_of_instance;
    }
    if (fC->Type(Net_lvalue) == VObjectType::slNet_lvalue) {
      unsigned int index = 0;
      while (Net_lvalue) {
        std::string sigName;
        NodeId sigId = 0;
        bool bit_or_part_select = false;
        if (fC->Type(Net_lvalue) == VObjectType::slNet_lvalue) {
          NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
          if (fC->Type(fC->Child(Hierarchical_identifier)) ==
              slHierarchical_identifier) {
            Hierarchical_identifier =
                fC->Child(fC->Child(Hierarchical_identifier));
          } else if (fC->Type(Hierarchical_identifier) !=
                     slPs_or_hierarchical_identifier) {
            Hierarchical_identifier = Net_lvalue;
          }
          if (m_helper.isSelected(fC, Hierarchical_identifier))
            bit_or_part_select = true;
          sigId = Hierarchical_identifier;
          if (fC->Type(fC->Child(sigId)) == slStringConst) {
            sigId = fC->Child(sigId);
          }
          sigName = fC->SymName(sigId);
        } else if (fC->Type(Net_lvalue) == VObjectType::slExpression) {
          NodeId Primary = fC->Child(Net_lvalue);
          NodeId Primary_literal = fC->Child(Primary);
          if (fC->Type(Primary_literal) == slComplex_func_call)
            bit_or_part_select = true;
          sigId = fC->Child(Primary_literal);
          sigName = fC->SymName(sigId);
        }
        if (ports) {
          if (index < ports->size()) {
            port* p = (*ports)[index];

            if ((!bit_or_part_select) && (fC->Type(sigId) == slStringConst)) {
              ref_obj* ref = s.MakeRef_obj();
              ref->VpiFile(fC->getFileName());
              ref->VpiLineNo(fC->Line(sigId));
              ref->VpiColumnNo(fC->Column(sigId));
              ref->VpiEndLineNo(fC->EndLine(sigId));
              ref->VpiEndColumnNo(fC->EndColumn(sigId));
              p->High_conn(ref);
              ref->VpiName(sigName);
              if (parent) {
                ref->VpiFullName(parent->getFullPathName() + "." + sigName);
                any* net = bind_net_(fC, sigId, parent,
                                     instance->getInstanceBinding(), sigName);
                ref->Actual_group(net);
              }
            } else {
              any* exp = nullptr;
              if (fC->Type(Net_lvalue) == VObjectType::slNet_lvalue) {
                NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
                if (fC->Type(fC->Child(Hierarchical_identifier)) ==
                    slHierarchical_identifier) {
                  Hierarchical_identifier =
                      fC->Child(fC->Child(Hierarchical_identifier));
                } else if (fC->Type(Hierarchical_identifier) !=
                           slPs_or_hierarchical_identifier) {
                  Hierarchical_identifier = Net_lvalue;
                }
                exp = m_helper.compileExpression(
                    parent_comp, fC, Hierarchical_identifier, m_compileDesign,
                    nullptr, parent, true);
              } else {
                exp = m_helper.compileExpression(parent_comp, fC, Net_lvalue,
                                                 m_compileDesign, nullptr,
                                                 parent, true);
              }
              p->High_conn(exp);
            }
          }
        }
        if (inst_type == VObjectType::slGate_instantiation) {
          port* p = s.MakePort();
          if (ports == nullptr) {
            ports = s.MakePortVec();
            netlist->ports(ports);
          }
          p->VpiFile(fC->getFileName());
          p->VpiLineNo(fC->Line(Net_lvalue));
          p->VpiColumnNo(fC->Column(Net_lvalue));
          p->VpiEndLineNo(fC->EndLine(Net_lvalue));
          p->VpiEndColumnNo(fC->EndColumn(Net_lvalue));
          if (fC->Type(sigId) == slStringConst) {
            ref_obj* ref = s.MakeRef_obj();
            ref->VpiFile(fC->getFileName());
            ref->VpiLineNo(fC->Line(sigId));
            ref->VpiColumnNo(fC->Column(sigId));
            ref->VpiEndLineNo(fC->EndLine(sigId));
            ref->VpiEndColumnNo(fC->EndColumn(sigId));
            p->High_conn(ref);
            ref->VpiName(sigName);
            if (parent) {
              ref->VpiFullName(parent->getFullPathName() + "." + sigName);
              any* net = bind_net_(fC, sigId, parent,
                                   instance->getInstanceBinding(), sigName);
              ref->Actual_group(net);
            }
          } else {
            NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
            if (fC->Type(fC->Child(Hierarchical_identifier)) ==
                slHierarchical_identifier) {
              Hierarchical_identifier =
                  fC->Child(fC->Child(Hierarchical_identifier));
            } else if (fC->Type(Hierarchical_identifier) !=
                       slPs_or_hierarchical_identifier) {
              Hierarchical_identifier = Net_lvalue;
            }

            any* exp = m_helper.compileExpression(
                parent_comp, fC, Hierarchical_identifier, m_compileDesign,
                nullptr, parent, true);
            p->High_conn(exp);
            if (exp->UhdmType() == uhdmref_obj) {
              ref_obj* ref = (ref_obj*)exp;
              const std::string& n = ref->VpiName();
              any* net = bind_net_(fC, Hierarchical_identifier, parent,
                                   instance->getInstanceBinding(), n);
              ref->Actual_group(net);
            }
          }
          ports->push_back(p);
        }
        Net_lvalue = fC->Sibling(Net_lvalue);
        index++;
      }
    } else if (fC->Type(Net_lvalue) ==
               VObjectType::slList_of_port_connections) {
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
      unsigned int index = 0;
      bool orderedConnection = false;
      if (fC->Type(Named_port_connection) ==
          VObjectType::slOrdered_port_connection) {
        orderedConnection = true;
      }

      bool wildcard = false;
      NodeId MemNamed_port_connection = Named_port_connection;
      unsigned int wildcardLineNumber = 0;
      unsigned short wildcardColumnNumber = 0;
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (fC->Type(formalId) == VObjectType::slDotStar) {
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
        if (formalId == 0) {
          Named_port_connection = fC->Sibling(Named_port_connection);
          index++;
          continue;
        }
        UHDM::VectorOfattribute* attributes = nullptr;
        if (fC->Type(formalId) == VObjectType::slAttribute_instance) {
          attributes = m_helper.compileAttributes(parent_comp, fC, formalId,
                                                  m_compileDesign);
          while (fC->Type(formalId) == slAttribute_instance) {
            formalId = fC->Sibling(formalId);
          }
        }
        if (fC->Type(formalId) == VObjectType::slDotStar) {
          // .* connection
          Named_port_connection = fC->Sibling(Named_port_connection);
          continue;
        }

        NodeId sigId = formalId;
        std::string formalName = fC->SymName(formalId);
        NodeId Expression = fC->Sibling(formalId);
        if (orderedConnection) {
          Expression = formalId;
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          NodeId formalNameId = fC->Child(Primary_literal);
          formalName = fC->SymName(formalNameId);
        } else {
          NodeId tmp = Expression;
          if (fC->Type(tmp) == slOpenParens) {
            tmp = fC->Sibling(tmp);
            if (fC->Type(tmp) == slCloseParens) {  // .p()  explicit disconnect
              Named_port_connection = fC->Sibling(Named_port_connection);
              port* p = nullptr;
              if (ports) {
                if (index < ports->size()) {
                  if (orderedConnection) {
                    formalName = ((*signals)[index])->getName();
                    p = (*ports)[index];
                  } else {
                    for (port* pItr : *ports) {
                      if (pItr->VpiName() == formalName) {
                        p = pItr;
                        break;
                      }
                    }
                    if (p == nullptr) p = (*ports)[index];
                  }
                } else {
                  p = s.MakePort();
                  ports->push_back(p);
                  p->VpiName(formalName);
                }
              } else {
                ports = s.MakePortVec();
                netlist->ports(ports);
                p = s.MakePort();
                ports->push_back(p);
                p->VpiName(formalName);
                p->VpiFile(fC->getFileName());
                p->VpiLineNo(fC->Line(formalId));
                p->VpiColumnNo(fC->Column(formalId));
                p->VpiEndLineNo(fC->EndLine(formalId));
                p->VpiEndColumnNo(fC->EndColumn(formalId));
              }
              operation* op = s.MakeOperation();
              op->VpiOpType(vpiNullOp);
              op->VpiFile(fC->getFileName());
              op->VpiLineNo(fC->Line(tmp));
              op->VpiColumnNo(fC->EndColumn(tmp));
              op->VpiEndLineNo(fC->EndLine(tmp));
              op->VpiEndColumnNo(fC->Column(tmp));
              p->High_conn(op);
              index++;
              continue;
            } else if (fC->Type(tmp) ==
                       slExpression) {  // .p(s) connection by name
              sigId = tmp;
              Expression = tmp;
            }
          }  // else .p implicit connection
        }
        expr* hexpr = nullptr;
        if (fC->Type(Expression) == slAttribute_instance) {
          attributes =
              m_helper.compileAttributes(comp, fC, Expression, m_compileDesign);
          while (fC->Type(Expression) == slAttribute_instance)
            Expression = fC->Sibling(Expression);
        }
        if (Expression) {
          hexpr = (expr*)m_helper.compileExpression(parent_comp, fC, Expression,
                                                    m_compileDesign, nullptr,
                                                    parent, true);
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          sigId = fC->Child(Primary_literal);
        }
        std::string sigName;
        if (fC->Type(sigId) == slStringConst) sigName = fC->SymName(sigId);
        std::string baseName = sigName;
        std::string selectName;
        if (NodeId subId = fC->Sibling(sigId)) {
          if (fC->Name(subId)) {
            selectName = fC->SymName(subId);
            sigName += std::string(".") + selectName;
          }
        }
        port* p = nullptr;
        if (ports) {
          if (index < ports->size()) {
            if (orderedConnection) {
              formalName = ((*signals)[index])->getName();
              p = (*ports)[index];
            } else {
              for (port* pItr : *ports) {
                if (pItr->VpiName() == formalName) {
                  p = pItr;
                  break;
                }
              }
              if (p == nullptr) p = (*ports)[index];
            }
          } else {
            p = s.MakePort();
            ports->push_back(p);
          }
        } else {
          ports = s.MakePortVec();
          netlist->ports(ports);
          p = s.MakePort();
          ports->push_back(p);
        }
        any* net = nullptr;
        if (!sigName.empty()) {
          net = bind_net_(fC, sigId, parent, instance->getInstanceBinding(),
                          sigName);
        }

        if ((!sigName.empty()) && (hexpr == nullptr)) {
          ref_obj* ref = s.MakeRef_obj();
          ref->VpiFile(fC->getFileName());
          ref->VpiLineNo(fC->Line(sigId));
          ref->VpiColumnNo(fC->Column(sigId));
          ref->VpiEndLineNo(fC->EndLine(sigId));
          ref->VpiEndColumnNo(fC->EndColumn(sigId));
          ref->VpiName(sigName);
          if (parent) {
            ref->VpiFullName(parent->getFullPathName() + "." + sigName);
            p->High_conn(ref);
            ref->Actual_group(net);
          }
        } else if (hexpr != nullptr) {
          p->High_conn(hexpr);
          if (hexpr->UhdmType() == uhdmref_obj) {
            ((ref_obj*)hexpr)->Actual_group(net);
            if (parent) {
              ((ref_obj*)hexpr)
                  ->VpiFullName(parent->getFullPathName() + "." +
                                ((ref_obj*)hexpr)->VpiName());
            }
          }
        }
        p->VpiName(formalName);
        p->Attributes(attributes);
        if (p->VpiLineNo() == 0) {
          p->VpiFile(fC->getFileName());
          p->VpiLineNo(fC->Line(formalId));
          p->VpiColumnNo(fC->Column(formalId));
          p->VpiEndLineNo(fC->EndLine(formalId));
          p->VpiEndColumnNo(fC->EndColumn(formalId));
        }
        bool lowconn_is_nettype = false;
        if (const any* lc = p->Low_conn()) {
          if (lc->UhdmType() == uhdmref_obj) {
            ref_obj* rf = (ref_obj*)lc;
            rf->VpiFile(fC->getFileName());
            rf->VpiLineNo(fC->Line(formalId));
            rf->VpiColumnNo(fC->Column(formalId));
            rf->VpiEndLineNo(fC->EndLine(formalId));
            rf->VpiEndColumnNo(fC->EndColumn(formalId));
            const any* act = rf->Actual_group();
            if (act && (act->UhdmType() == uhdmlogic_net))
              lowconn_is_nettype = true;
          }
        }
        if (net && (net->UhdmType() == uhdmmodport) && (lowconn_is_nettype)) {
          Netlist* parentNetlist = parent->getNetlist();
          Netlist::ModPortMap::iterator itr;
          modport* mp = nullptr;
          if (orderedConnection) {
            itr = netlist->getModPortMap().find(formalName);
            if (itr != netlist->getModPortMap().end()) {
              mp = (*itr).second.second;
            }
          } else {
            itr = parentNetlist->getModPortMap().find(sigName);
            if (itr != parentNetlist->getModPortMap().end()) {
              ModPort* orig_modport = (*itr).second.first;
              ModuleDefinition* orig_interf = orig_modport->getParent();

              ModuleInstance* interfaceInstance =
                  new ModuleInstance(orig_interf, fC, sigId, instance, sigName,
                                     orig_interf->getName());
              Netlist* netlistInterf = new Netlist(interfaceInstance);
              interfaceInstance->setNetlist(netlistInterf);

              mp = elab_modport_(instance, interfaceInstance, formalName,
                                 orig_interf->getName(), orig_interf,
                                 p->VpiFile(), p->VpiLineNo(), selectName,
                                 nullptr);
            }
          }
          if (mp) {
            ref_obj* ref = s.MakeRef_obj();
            ref->VpiFile(p->VpiFile());
            ref->VpiLineNo(p->VpiLineNo());
            ref->VpiColumnNo(p->VpiColumnNo());
            ref->VpiEndLineNo(p->VpiEndLineNo());
            ref->VpiEndColumnNo(p->VpiEndColumnNo());
            ref->Actual_group(mp);
            p->Low_conn(ref);
          }
        } else if (net && (net->UhdmType() == uhdminterface) &&
                   (lowconn_is_nettype)) {
          BaseClass* sm = nullptr;
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
              sm = elab_interface_(instance, orig_instance, formalName,
                                   orig_interf->getName(), orig_interf,
                                   instance->getFileName(),
                                   instance->getLineNb(), nullptr, "");
            }
          }
          if (sm) {
            ref_obj* ref = s.MakeRef_obj();
            ref->Actual_group(sm);
            ref->VpiFile(fC->getFileName());
            ref->VpiLineNo(fC->Line(Named_port_connection));
            ref->VpiColumnNo(fC->Column(Named_port_connection));
            ref->VpiEndLineNo(fC->EndLine(Named_port_connection));
            ref->VpiEndColumnNo(fC->EndColumn(Named_port_connection));
            p->Low_conn(ref);
          }
        }

        Named_port_connection = fC->Sibling(Named_port_connection);
        index++;
      }
      if (wildcard) {
        if (signals) {
          // Add missing ports
          VectorOfport* newPorts = s.MakePortVec();
          for (Signal* s1 : *signals) {
            const std::string& sigName = s1->getName();
            bool found = false;
            port* pp = nullptr;
            for (port* p : *ports) {
              if (p->VpiName() == s1->getName()) {
                newPorts->push_back(p);
                found = true;
                pp = p;
                break;
              }
            }
            if (!found) {
              port* p = s.MakePort();
              p->VpiName(sigName);
              p->VpiFile(fC->getFileName());
              p->VpiLineNo(wildcardLineNumber);
              p->VpiColumnNo(wildcardColumnNumber);
              p->VpiEndLineNo(wildcardLineNumber);
              p->VpiEndColumnNo(wildcardColumnNumber + 1);
              newPorts->push_back(p);
              pp = p;
            }
            if (pp->High_conn() == nullptr) {
              ref_obj* ref = s.MakeRef_obj();
              ref->VpiFile(fC->getFileName());
              ref->VpiLineNo(wildcardLineNumber);
              ref->VpiColumnNo(wildcardColumnNumber);
              ref->VpiEndLineNo(wildcardLineNumber);
              ref->VpiEndColumnNo(wildcardColumnNumber + 1);
              ref->VpiName(sigName);
              if (parent) {
                ref->VpiFullName(parent->getFullPathName() + "." + sigName);
                pp->High_conn(ref);
                UHDM::any* net = bind_net_(
                    fC, 0, parent, instance->getInstanceBinding(), sigName);
                ref->Actual_group(net);
              }
            }
          }
          netlist->ports(newPorts);
        }
      }
    }
  }
  return true;
}

interface* NetlistElaboration::elab_interface_(
    ModuleInstance* instance, ModuleInstance* interf_instance,
    const std::string& instName, const std::string& defName,
    ModuleDefinition* mod, const fs::path& fileName, int lineNb,
    interface_array* interf_array, const std::string& modPortName) {
  Netlist* netlist = instance->getNetlist();
  Serializer& s = m_compileDesign->getSerializer();
  VectorOfinterface* subInterfaces = netlist->interfaces();
  if (subInterfaces == nullptr) {
    subInterfaces = s.MakeInterfaceVec();
    netlist->interfaces(subInterfaces);
  }
  interface* sm = s.MakeInterface();
  sm->VpiName(instName);
  sm->VpiDefName(defName);
  // sm->VpiFullName(??);
  sm->VpiFile(fileName);
  sm->VpiLineNo(lineNb);
  subInterfaces->push_back(sm);
  if (interf_array) {
    interf_array->Instances()->push_back(sm);
    netlist->getInstanceMap().insert(std::make_pair(
        instName, std::make_pair(interf_instance, interf_array)));
    netlist->getSymbolTable().insert(std::make_pair(instName, interf_array));
  } else {
    netlist->getInstanceMap().insert(
        std::make_pair(instName, std::make_pair(interf_instance, sm)));
    netlist->getSymbolTable().insert(std::make_pair(instName, sm));
  }
  const std::string prefix = instName + ".";
  elab_ports_nets_(instance, interf_instance, instance->getNetlist(),
                   interf_instance->getNetlist(), mod, prefix, true);
  elab_ports_nets_(instance, interf_instance, instance->getNetlist(),
                   interf_instance->getNetlist(), mod, prefix, false);
  // Modports
  ModuleDefinition::ModPortSignalMap& orig_modports =
      mod->getModPortSignalMap();
  VectorOfmodport* dest_modports = s.MakeModportVec();
  for (auto& orig_modport : orig_modports) {
    const std::string modportfullname = instName + "." + orig_modport.first;
    if (!modPortName.empty() && (modportfullname != modPortName)) continue;
    modport* dest_modport = s.MakeModport();
    dest_modport->Interface(sm);
    dest_modport->VpiParent(sm);
    const FileContent* orig_fC = orig_modport.second.getFileContent();
    const NodeId orig_nodeId = orig_modport.second.getNodeId();
    dest_modport->VpiFile(orig_fC->getFileName());
    dest_modport->VpiLineNo(orig_fC->Line(orig_nodeId));
    dest_modport->VpiColumnNo(orig_fC->Column(orig_nodeId));
    dest_modport->VpiEndLineNo(orig_fC->EndLine(orig_nodeId));
    dest_modport->VpiEndColumnNo(orig_fC->EndColumn(orig_nodeId));
    netlist->getModPortMap().insert(std::make_pair(
        modportfullname, std::make_pair(&orig_modport.second, dest_modport)));
    netlist->getSymbolTable().insert(
        std::make_pair(modportfullname, dest_modport));
    dest_modport->VpiName(orig_modport.first);
    VectorOfio_decl* ios = s.MakeIo_declVec();
    for (auto& sig : orig_modport.second.getPorts()) {
      const FileContent* const fC = sig.getFileContent();
      const NodeId nodeId = sig.getNodeId();
      const std::string& sigName = sig.getName();
      io_decl* io = s.MakeIo_decl();
      io->VpiName(sigName);
      unsigned int direction = UhdmWriter::getVpiDirection(sig.getDirection());
      io->VpiDirection(direction);
      io->VpiFile(fC->getFileName());
      io->VpiLineNo(fC->Line(nodeId));
      io->VpiColumnNo(fC->Column(nodeId));
      io->VpiEndLineNo(fC->EndLine(nodeId));
      io->VpiEndColumnNo(fC->EndColumn(nodeId));
      any* net = bind_net_(instance, sigName);
      if (net == nullptr) {
        net = bind_net_(interf_instance, sigName);
      }
      if (net && (net->UhdmType() == uhdminterface)) {
        ref_obj* n = s.MakeRef_obj();
        n->VpiName(sigName);
        n->VpiFullName(instance->getFullPathName() + "." + sigName);
        n->VpiFile(fC->getFileName());
        n->VpiLineNo(fC->Line(nodeId));
        n->VpiColumnNo(fC->Column(nodeId));
        n->VpiEndLineNo(fC->EndLine(nodeId));
        n->VpiEndColumnNo(fC->EndColumn(nodeId));
        if (sigName != instName)  // prevent loop in listener
          n->Actual_group(net);
        net = n;
        io->Expr(net);
      } else {
        io->Expr(net);
      }
      ios->push_back(io);
    }
    dest_modport->Io_decls(ios);
    dest_modports->push_back(dest_modport);
  }
  sm->Modports(dest_modports);

  return sm;
}

modport* NetlistElaboration::elab_modport_(
    ModuleInstance* instance, ModuleInstance* interfaceInstance,
    const std::string& instName, const std::string& defName,
    ModuleDefinition* mod, const fs::path& fileName, int lineNb,
    const std::string& modPortName, UHDM::interface_array* interf_array) {
  Netlist* netlist = instance->getNetlist();
  std::string fullname = instName + "." + modPortName;
  Netlist::ModPortMap::iterator itr = netlist->getModPortMap().find(fullname);
  if (itr == netlist->getModPortMap().end()) {
    elab_interface_(instance, interfaceInstance, instName, defName, mod,
                    fileName, lineNb, interf_array, fullname);
  }
  itr = netlist->getModPortMap().find(fullname);
  if (itr != netlist->getModPortMap().end()) {
    return (*itr).second.second;
  }
  return nullptr;
}

bool NetlistElaboration::elab_generates_(ModuleInstance* instance) {
  Serializer& s = m_compileDesign->getSerializer();
  Netlist* netlist = instance->getNetlist();
  DesignComponent* comp_def = instance->getDefinition();
  if (ModuleDefinition* mm =
          valuedcomponenti_cast<ModuleDefinition*>(comp_def)) {
    VObjectType insttype = instance->getType();
    if (insttype == VObjectType::slConditional_generate_construct ||
        insttype == VObjectType::slLoop_generate_construct ||
        insttype == VObjectType::slGenerate_block ||
        insttype == VObjectType::slGenerate_item ||
        insttype == VObjectType::slGenerate_module_conditional_statement ||
        insttype == VObjectType::slGenerate_interface_conditional_statement ||
        insttype == VObjectType::slGenerate_module_loop_statement ||
        insttype == VObjectType::slGenerate_interface_loop_statement ||
        insttype == VObjectType::slGenerate_module_named_block ||
        insttype == VObjectType::slGenerate_interface_named_block ||
        insttype == VObjectType::slGenerate_module_block ||
        insttype == VObjectType::slGenerate_interface_block ||
        insttype == VObjectType::slGenerate_module_item ||
        insttype == VObjectType::slGenerate_interface_item) {
      std::vector<gen_scope_array*>* gen_scopes = netlist->gen_scopes();
      if (gen_scopes == nullptr) {
        gen_scopes = s.MakeGen_scope_arrayVec();
        netlist->gen_scopes(gen_scopes);
      }

      const FileContent* fC = mm->getFileContents()[0];
      gen_scope_array* gen_scope_array = s.MakeGen_scope_array();
      std::vector<gen_scope*>* vec = s.MakeGen_scopeVec();
      gen_scope* gen_scope = s.MakeGen_scope();
      vec->push_back(gen_scope);
      gen_scope_array->Gen_scopes(vec);
      gen_scope->VpiFile(fC->getFileName());
      gen_scope->VpiLineNo(fC->Line(mm->getGenBlockId()));
      gen_scope->VpiColumnNo(fC->Column(mm->getGenBlockId()));
      gen_scope->VpiEndLineNo(fC->EndLine(mm->getGenBlockId()));
      gen_scope->VpiEndColumnNo(fC->EndColumn(mm->getGenBlockId()));
      gen_scope->VpiName(instance->getInstanceName());
      gen_scope_array->VpiFile(fC->getFileName());
      gen_scope_array->VpiLineNo(fC->Line(mm->getGenBlockId()));
      gen_scope_array->VpiColumnNo(fC->Column(mm->getGenBlockId()));
      gen_scope_array->VpiEndLineNo(fC->EndLine(mm->getGenBlockId()));
      gen_scope_array->VpiEndColumnNo(fC->EndColumn(mm->getGenBlockId()));
      gen_scopes->push_back(gen_scope_array);

      if (mm->getContAssigns()) gen_scope->Cont_assigns(mm->getContAssigns());
      if (mm->getProcesses()) gen_scope->Process(mm->getProcesses());
      if (mm->getParameters()) gen_scope->Parameters(mm->getParameters());
      if (mm->getParam_assigns())
        gen_scope->Param_assigns(mm->getParam_assigns());

      elab_ports_nets_(instance, true);
      elab_ports_nets_(instance, false);

      gen_scope->Nets(netlist->nets());
      gen_scope->Array_vars(netlist->array_vars());
    }
  }
  return true;
}

bool NetlistElaboration::elab_interfaces_(ModuleInstance* instance) {
  for (unsigned int i = 0; i < instance->getNbChildren(); i++) {
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
      if (insttype == VObjectType::slInterface_instantiation) {
        elab_interface_(instance, child, child->getInstanceName(),
                        child->getModuleName(), mm, child->getFileName(),
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
                                    const std::string& prefix,
                                    bool signalIsPort, TypespecCache& tscache) {
  Serializer& s = m_compileDesign->getSerializer();
  std::vector<net*>* nets = netlist->nets();
  std::vector<variables*>* vars = netlist->variables();
  std::vector<array_net*>* array_nets = netlist->array_nets();
  const FileContent* fC = sig->getFileContent();
  NodeId id = sig->getNodeId();
  NodeId packedDimension = sig->getPackedDimension();
  NodeId unpackedDimension = sig->getUnpackedDimension();
  // Nets pass
  const DataType* dtype = sig->getDataType();
  VObjectType subnettype = sig->getType();
  UHDM::typespec* tps = nullptr;
  // Determine if the "signal" is a net or a var
  bool isNet = true;
  if ((dtype && (subnettype == slNoType)) || sig->isConst() || sig->isVar() ||
      (!sig->isStatic()) || (subnettype == slClass_scope) ||
      (subnettype == slStringConst) || (subnettype == slIntegerAtomType_Int) ||
      (subnettype == slIntegerAtomType_Integer) ||
      (subnettype == slIntegerAtomType_Byte) ||
      (subnettype == slIntegerAtomType_LongInt) ||
      (subnettype == slIntegerAtomType_Shortint) ||
      (subnettype == slString_type) || (subnettype == slNonIntType_Real) ||
      (subnettype == slNonIntType_RealTime) ||
      (subnettype == slNonIntType_ShortReal) || (subnettype == slEvent_type) ||
      (subnettype == slChandle_type) || (subnettype == slIntVec_TypeBit) ||
      (subnettype == slEnum_base_type) ||
      ((!sig->isVar()) && (subnettype == slIntVec_TypeLogic))) {
    isNet = false;
  }
  if (sig->getDirection() == slPortDir_Out ||
      sig->getDirection() == slPortDir_Inp ||
      sig->getDirection() == slPortDir_Inout) {
    if ((!sig->isVar()) && (subnettype == slIntVec_TypeLogic)) {
      isNet = true;
    }
  }

  NodeId typeSpecId = sig->getTypeSpecId();
  if (typeSpecId) {
    auto itr = tscache.find(typeSpecId);
    if (itr == tscache.end()) {
      tps = m_helper.compileTypespec(comp, fC, typeSpecId, m_compileDesign,
                                     nullptr, child, true, true);
      tscache.insert(std::make_pair(typeSpecId, tps));
    } else {
      tps = (*itr).second;
    }
  }
  if (tps == nullptr) {
    if (sig->getInterfaceTypeNameId()) {
      auto itr = tscache.find(sig->getInterfaceTypeNameId());
      if (itr == tscache.end()) {
        tps = m_helper.compileTypespec(comp, fC, sig->getInterfaceTypeNameId(),
                                       m_compileDesign, nullptr, child, true,
                                       true);
        tscache.insert(std::make_pair(sig->getInterfaceTypeNameId(), tps));
      } else {
        tps = (*itr).second;
      }
    }
  }
  if (tps) {
    typespec* tmp = tps;
    UHDM_OBJECT_TYPE ttmp = tmp->UhdmType();
    if (ttmp == uhdmpacked_array_typespec) {
      tmp = (typespec*)((packed_array_typespec*)tmp)->Elem_typespec();
    } else if (ttmp == uhdmstruct_typespec) {
      struct_typespec* the_tps = (struct_typespec*)tmp;
      if (the_tps->Members()) {
        isNet = true;
        for (typespec_member* member : *the_tps->Members()) {
          const typespec* mtps = member->Typespec();
          if (mtps) {
            UHDM_OBJECT_TYPE mtype = mtps->UhdmType();
            if (mtype != uhdmlogic_typespec && mtype != uhdmstruct_typespec) {
              isNet = false;
              break;
            }
          }
        }
      }
    } else if (ttmp == uhdmenum_typespec) {
      isNet = false;
    } else if (ttmp == uhdmbit_typespec) {
      isNet = false;
    } else if (ttmp == uhdmbyte_typespec) {
      isNet = false;
    } else if (ttmp == uhdmreal_typespec) {
      isNet = false;
    } else if (ttmp == uhdmclass_typespec) {
      isNet = false;
    } else if (ttmp == uhdminterface_typespec) {
      if (!signalIsPort) {
        SymbolTable* symbols = m_compileDesign->getCompiler()->getSymbolTable();
        ErrorContainer* errors =
            m_compileDesign->getCompiler()->getErrorContainer();
        Location loc1(symbols->registerSymbol(fC->getFileName().string()),
                      fC->Line(id), fC->Column(id),
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
      vars = s.MakeVariablesVec();
      netlist->variables(vars);
    }
  }

  const std::string& signame = sig->getName();
  const std::string parentSymbol = prefix + signame;

  // Packed and unpacked ranges
  int packedSize;
  int unpackedSize;
  std::vector<UHDM::range*>* packedDimensions =
      m_helper.compileRanges(comp, fC, packedDimension, m_compileDesign,
                             nullptr, child, true, packedSize, false);
  std::vector<UHDM::range*>* unpackedDimensions =
      m_helper.compileRanges(comp, fC, unpackedDimension, m_compileDesign,
                             nullptr, child, true, unpackedSize, false);

  any* obj = nullptr;

  // Assignment to a default value
  expr* exp = exprFromAssign_(comp, fC, id, unpackedDimension, child);
  if ((exp == nullptr) && sig->getDefaultValue()) {
    exp = (expr*)m_helper.compileExpression(comp, fC, sig->getDefaultValue(),
                                            m_compileDesign, nullptr, child,
                                            true);
  }
  if (isNet) {
    // Nets
    if (dtype) {
      dtype = dtype->getActual();
      if (const DummyType* en = datatype_cast<const DummyType*>(dtype)) {
        UHDM::typespec* spec = en->getTypespec();
        if (spec->UhdmType() == uhdmlogic_typespec) {
          logic_net* logicn = s.MakeLogic_net();
          logicn->Attributes(sig->attributes());
          logicn->VpiSigned(sig->isSigned());
          logicn->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
          // Move range to typespec for simple types
          // logicn->Ranges(packedDimensions);
          logicn->Typespec(tps);
          logicn->VpiName(signame);
          obj = logicn;
          logicn->Typespec(spec);
        } else if (spec->UhdmType() == uhdmstruct_typespec) {
          struct_net* stv = s.MakeStruct_net();
          stv->Attributes(sig->attributes());
          stv->Typespec(spec);
          obj = stv;
          if (packedDimensions) {
            packed_array_net* pnets = s.MakePacked_array_net();
            pnets->Ranges(packedDimensions);
            pnets->Elements(s.MakeAnyVec());
            pnets->Elements()->push_back(stv);
            obj = pnets;
          }
        } else if (spec->UhdmType() == uhdmenum_typespec) {
          enum_net* stv = s.MakeEnum_net();
          stv->Attributes(sig->attributes());
          stv->Typespec(spec);
          obj = stv;
          if (packedDimensions) {
            packed_array_net* pnets = s.MakePacked_array_net();
            pnets->Ranges(packedDimensions);
            pnets->Elements(s.MakeAnyVec());
            pnets->Elements()->push_back(stv);
            obj = pnets;
          }
        } else if (spec->UhdmType() == uhdmbit_typespec) {
          bit_var* logicn = s.MakeBit_var();
          logicn->Attributes(sig->attributes());
          logicn->VpiSigned(sig->isSigned());
          // Move range to typespec for simple types
          // logicn->Ranges(packedDimensions);
          logicn->Typespec(tps);
          logicn->VpiName(signame);
          obj = logicn;
          logicn->Typespec(spec);
        } else if (spec->UhdmType() == uhdmbyte_typespec) {
          byte_var* logicn = s.MakeByte_var();
          logicn->Attributes(sig->attributes());
          logicn->VpiSigned(sig->isSigned());
          logicn->VpiName(signame);
          obj = logicn;
          logicn->Typespec(spec);
        } else {
          variables* var = m_helper.getSimpleVarFromTypespec(
              spec, packedDimensions, m_compileDesign);
          var->Attributes(sig->attributes());
          var->Expr(exp);
          var->VpiConstantVariable(sig->isConst());
          var->VpiSigned(sig->isSigned());
          var->VpiName(signame);
          obj = var;
        }

      } else if (const Enum* en = datatype_cast<const Enum*>(dtype)) {
        enum_net* stv = s.MakeEnum_net();
        stv->VpiName(signame);
        stv->Typespec(en->getTypespec());
        stv->Attributes(sig->attributes());
        obj = stv;
        if (packedDimensions) {
          packed_array_net* pnets = s.MakePacked_array_net();
          pnets->Ranges(packedDimensions);
          pnets->Elements(s.MakeAnyVec());
          pnets->Elements()->push_back(stv);
          obj = pnets;
          pnets->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
        } else {
          stv->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
        }
      } else if (const Struct* st = datatype_cast<const Struct*>(dtype)) {
        struct_net* stv = s.MakeStruct_net();
        stv->VpiName(signame);
        stv->Attributes(sig->attributes());
        stv->Typespec(st->getTypespec());
        obj = stv;
        if (packedDimensions) {
          packed_array_net* pnets = s.MakePacked_array_net();
          pnets->Ranges(packedDimensions);
          pnets->Elements(s.MakeAnyVec());
          pnets->Elements()->push_back(stv);
          obj = pnets;
          pnets->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
        } else {
          stv->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
        }
      } else if (const SimpleType* sit =
                     datatype_cast<const SimpleType*>(dtype)) {
        UHDM::typespec* spec = sit->getTypespec();
        if (spec->UhdmType() == uhdmlogic_typespec) {
          logic_net* logicn = s.MakeLogic_net();
          logicn->Attributes(sig->attributes());
          logicn->VpiSigned(sig->isSigned());
          logicn->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
          // Move range to typespec for simple types
          // logicn->Ranges(packedDimensions);
          logicn->Typespec(tps);
          logicn->VpiName(signame);
          obj = logicn;
          logicn->Typespec(spec);
        } else if (spec->UhdmType() == uhdmstruct_typespec) {
          struct_net* stv = s.MakeStruct_net();
          stv->VpiName(signame);
          stv->Attributes(sig->attributes());
          stv->Typespec(spec);
          obj = stv;
          if (packedDimensions) {
            packed_array_net* pnets = s.MakePacked_array_net();
            pnets->Ranges(packedDimensions);
            pnets->Elements(s.MakeAnyVec());
            pnets->Elements()->push_back(stv);
            obj = pnets;
            pnets->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
          } else {
            stv->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
          }
        } else if (spec->UhdmType() == uhdmenum_typespec) {
          enum_net* stv = s.MakeEnum_net();
          stv->VpiName(signame);
          stv->Attributes(sig->attributes());
          stv->Typespec(spec);
          obj = stv;
          if (packedDimensions) {
            packed_array_net* pnets = s.MakePacked_array_net();
            pnets->Ranges(packedDimensions);
            pnets->Elements(s.MakeAnyVec());
            pnets->Elements()->push_back(stv);
            obj = pnets;
            pnets->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
          } else {
            stv->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
          }
        } else if (spec->UhdmType() == uhdmbit_typespec) {
          bit_var* logicn = s.MakeBit_var();
          logicn->Attributes(sig->attributes());
          logicn->VpiSigned(sig->isSigned());
          logicn->Typespec(tps);
          // Move range to typespec for simple types
          // logicn->Ranges(packedDimensions);
          logicn->VpiName(signame);
          obj = logicn;
          logicn->Typespec(spec);
        } else if (spec->UhdmType() == uhdmbyte_typespec) {
          byte_var* logicn = s.MakeByte_var();
          logicn->Attributes(sig->attributes());
          logicn->VpiSigned(sig->isSigned());
          logicn->VpiName(signame);
          obj = logicn;
          logicn->Typespec(spec);
        } else {
          variables* var = m_helper.getSimpleVarFromTypespec(
              spec, packedDimensions, m_compileDesign);
          var->Attributes(sig->attributes());
          var->Expr(exp);
          var->VpiConstantVariable(sig->isConst());
          var->VpiSigned(sig->isSigned());
          var->VpiName(signame);
          obj = var;
        }
      } else {
        logic_net* logicn = s.MakeLogic_net();
        logicn->Attributes(sig->attributes());
        logicn->VpiSigned(sig->isSigned());
        logicn->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
        logicn->Typespec(tps);
        // Move range to typespec for simple types
        // logicn->Ranges(packedDimensions);
        logicn->VpiName(signame);
        obj = logicn;
      }

      if (unpackedDimensions) {
        array_net* array_net = s.MakeArray_net();
        array_net->Nets(s.MakeNetVec());
        array_net->Ranges(unpackedDimensions);
        array_net->VpiName(signame);
        array_net->VpiSize(unpackedSize);
        array_net->VpiFile(fC->getFileName());
        array_net->VpiLineNo(fC->Line(sig->getNodeId()));
        array_net->VpiColumnNo(fC->Column(sig->getNodeId()));
        array_net->VpiEndLineNo(fC->EndLine(sig->getNodeId()));
        array_net->VpiEndColumnNo(fC->EndColumn(sig->getNodeId()));
        if (array_nets == nullptr) {
          array_nets = s.MakeArray_netVec();
          netlist->array_nets(array_nets);
        }

        array_nets->push_back(array_net);
        obj->VpiParent(array_net);
        UHDM::VectorOfnet* array_n = array_net->Nets();
        array_n->push_back((net*)obj);

      } else {
        if (nets == nullptr) {
          nets = s.MakeNetVec();
          netlist->nets(nets);
        }
        UHDM_OBJECT_TYPE nettype = obj->UhdmType();
        if (nettype == uhdmenum_net) {
          ((enum_net*)obj)->VpiName(signame);
        } else if (nettype == uhdmstruct_net) {
          ((struct_net*)obj)->VpiName(signame);
        } else if (nettype == uhdmpacked_array_net) {
          ((packed_array_net*)obj)->VpiName(signame);
        }
        nets->push_back((net*)obj);
      }
    } else if (subnettype == slStruct_union) {
      // Implicit type
      struct_net* stv = s.MakeStruct_net();
      stv->VpiName(signame);
      stv->Attributes(sig->attributes());
      stv->Typespec(tps);
      obj = stv;
      stv->VpiName(signame);
      if (nets == nullptr) {
        nets = s.MakeNetVec();
        netlist->nets(nets);
      }
      nets->push_back(stv);
    } else if (tps && tps->UhdmType() == uhdmstruct_typespec) {
      struct_net* stv = s.MakeStruct_net();
      stv->VpiName(signame);
      stv->Typespec(tps);
      obj = stv;
      if (unpackedDimensions) {
        array_net* array_net = s.MakeArray_net();
        array_net->Nets(s.MakeNetVec());
        array_net->Ranges(unpackedDimensions);
        array_net->VpiName(signame);
        array_net->VpiSize(unpackedSize);
        array_net->VpiFile(fC->getFileName());
        array_net->VpiLineNo(fC->Line(sig->getNodeId()));
        array_net->VpiColumnNo(fC->Column(sig->getNodeId()));
        array_net->VpiEndLineNo(fC->EndLine(sig->getNodeId()));
        array_net->VpiEndColumnNo(fC->EndColumn(sig->getNodeId()));
        if (array_nets == nullptr) {
          array_nets = s.MakeArray_netVec();
          netlist->array_nets(array_nets);
        }

        array_nets->push_back(array_net);
        obj->VpiParent(array_net);
        UHDM::VectorOfnet* array_n = array_net->Nets();
        array_n->push_back((net*)obj);

      } else {
        if (nets == nullptr) {
          nets = s.MakeNetVec();
          netlist->nets(nets);
        }
        if (obj->UhdmType() == uhdmenum_net) {
          ((enum_net*)obj)->VpiName(signame);
        } else if (obj->UhdmType() == uhdmstruct_net) {
          ((struct_net*)obj)->VpiName(signame);
        }
        nets->push_back((net*)obj);
      }
    } else {
      logic_net* logicn = s.MakeLogic_net();
      logicn->VpiSigned(sig->isSigned());
      logicn->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
      // Move range to typespec for simple types
      // logicn->Ranges(packedDimensions);
      logicn->Typespec(tps);
      logicn->Attributes(sig->attributes());
      logicn->Typespec(tps);
      if (unpackedDimensions) {
        logicn->VpiLineNo(fC->Line(id));
        logicn->VpiColumnNo(fC->Column(id));
        logicn->VpiEndLineNo(fC->EndLine(id));
        logicn->VpiEndColumnNo(fC->EndColumn(id));
        logicn->VpiFile(fC->getFileName());
        array_net* array_net = s.MakeArray_net();
        array_net->Nets(s.MakeNetVec());
        array_net->Ranges(unpackedDimensions);
        array_net->VpiName(signame);
        array_net->VpiSize(unpackedSize);
        array_net->VpiFile(fC->getFileName());
        array_net->VpiLineNo(fC->Line(sig->getNodeId()));
        array_net->VpiColumnNo(fC->Column(sig->getNodeId()));
        array_net->VpiEndLineNo(fC->EndLine(sig->getNodeId()));
        array_net->VpiEndColumnNo(fC->EndColumn(sig->getNodeId()));
        if (array_nets == nullptr) {
          array_nets = s.MakeArray_netVec();
          netlist->array_nets(array_nets);
        }
        array_nets->push_back(array_net);
        logicn->VpiParent(array_net);
        UHDM::VectorOfnet* array_n = array_net->Nets();
        array_n->push_back(logicn);
        obj = array_net;
      } else {
        logicn->VpiName(signame);
        logicn->VpiSigned(sig->isSigned());
        obj = logicn;
        if (nets == nullptr) {
          nets = s.MakeNetVec();
          netlist->nets(nets);
        }
        nets->push_back(logicn);
      }
    }
    if (parentNetlist)
      parentNetlist->getSymbolTable().insert(std::make_pair(parentSymbol, obj));
    if (netlist) netlist->getSymbolTable().insert(std::make_pair(signame, obj));

    if (exp) {
      cont_assign* assign = s.MakeCont_assign();
      assign->VpiNetDeclAssign(true);
      assign->VpiFile(fC->getFileName());
      assign->VpiLineNo(fC->Line(id));
      assign->VpiColumnNo(fC->Column(id));
      assign->VpiEndLineNo(fC->EndLine(id));
      assign->VpiEndColumnNo(fC->EndColumn(id));
      assign->Lhs((expr*)obj);
      assign->Rhs(exp);
      m_helper.setParentNoOverride((expr*)obj, assign);
      m_helper.setParentNoOverride(exp, assign);
      if (sig->getDelay()) {
        expr* delay_expr = (expr*)m_helper.compileExpression(
            comp, fC, sig->getDelay(), m_compileDesign, nullptr, child, true);
        assign->Delay(delay_expr);
      }
      std::vector<cont_assign*>* assigns = netlist->cont_assigns();
      if (assigns == nullptr) {
        netlist->cont_assigns(s.MakeCont_assignVec());
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
    if (obj->VpiLineNo() == 0) {
      obj->VpiFile(fC->getFileName());
      obj->VpiLineNo(fC->Line(id));
      obj->VpiColumnNo(fC->Column(id));
      if (unpackedDimension) {
        obj->VpiEndLineNo(fC->EndLine(unpackedDimension));
        obj->VpiEndColumnNo(fC->EndColumn(unpackedDimension));
      } else {
        obj->VpiEndLineNo(fC->EndLine(id));
        obj->VpiEndColumnNo(fC->EndColumn(id));
      }
    }
    if (parentNetlist)
      parentNetlist->getSymbolTable().insert(std::make_pair(parentSymbol, obj));
    netlist->getSymbolTable().insert(std::make_pair(signame, obj));
  } else {
    // Unsupported type
    ErrorContainer* errors =
        m_compileDesign->getCompiler()->getErrorContainer();
    SymbolTable* symbols = m_compileDesign->getCompiler()->getSymbolTable();
    Location loc(symbols->registerSymbol(fC->getFileName().string()),
                 fC->Line(id), 0, symbols->registerSymbol(signame));
    Error err(ErrorDefinition::UHDM_UNSUPPORTED_SIGNAL, loc);
    errors->addError(err);
  }
  return isNet;
}

bool NetlistElaboration::elab_ports_nets_(
    ModuleInstance* instance, ModuleInstance* child, Netlist* parentNetlist,
    Netlist* netlist, DesignComponent* comp, const std::string& prefix,
    bool do_ports) {
  Serializer& s = m_compileDesign->getSerializer();
  VObjectType compType = comp->getType();
  std::vector<port*>* ports = netlist->ports();
  TypespecCache tscache;
  std::set<std::string> portInterf;
  for (int pass = 0; pass < 3; pass++) {
    std::vector<Signal*>* signals = nullptr;
    if (compType == VObjectType::slModule_declaration ||
        compType == VObjectType::slConditional_generate_construct ||
        compType == VObjectType::slLoop_generate_construct ||
        compType == VObjectType::slGenerate_item ||
        compType == VObjectType::slGenerate_module_conditional_statement ||
        compType == VObjectType::slGenerate_interface_conditional_statement ||
        compType == VObjectType::slGenerate_module_loop_statement ||
        compType == VObjectType::slGenerate_interface_loop_statement ||
        compType == VObjectType::slGenerate_module_named_block ||
        compType == VObjectType::slGenerate_interface_named_block ||
        compType == VObjectType::slGenerate_module_block ||
        compType == VObjectType::slGenerate_interface_block ||
        compType == VObjectType::slGenerate_module_item ||
        compType == VObjectType::slGenerate_interface_item ||
        compType == VObjectType::slGenerate_block ||
        compType == VObjectType::slInterface_declaration ||
        compType == VObjectType::slProgram_declaration) {
      if (pass == 1)
        signals = &comp->getSignals();
      else
        signals = &comp->getPorts();
    } else {
      continue;
    }
    int portIndex = 0;
    int lastPortDirection = vpiInout;
    for (Signal* sig : *signals) {
      const FileContent* fC = sig->getFileContent();
      NodeId id = sig->getNodeId();
      if (pass == 0) {
        if (!do_ports) continue;
        // Ports pass
        port* dest_port = s.MakePort();
        if (sig->getDirection() != slNoType) {
          lastPortDirection = UhdmWriter::getVpiDirection(sig->getDirection());
        }
        dest_port->VpiDirection(lastPortDirection);
        std::string signame;
        if (fC->Type(sig->getNodeId()) == slStringConst) {
          signame = sig->getName();
          dest_port->VpiName(signame);
        }
        dest_port->VpiLineNo(fC->Line(id));
        dest_port->VpiColumnNo(fC->Column(id));
        dest_port->VpiEndLineNo(fC->EndLine(id));
        dest_port->VpiEndColumnNo(fC->EndColumn(id));
        dest_port->VpiFile(fC->getFileName());
        if (ports == nullptr) {
          ports = s.MakePortVec();
          netlist->ports(ports);
        }
        ports->push_back(dest_port);

        NodeId unpackedDimension = sig->getUnpackedDimension();
        int unpackedSize;
        std::vector<UHDM::range*>* unpackedDimensions =
            m_helper.compileRanges(comp, fC, unpackedDimension, m_compileDesign,
                                   nullptr, child, true, unpackedSize, false);

        NodeId typeSpecId = sig->getTypeSpecId();
        if (typeSpecId) {
          UHDM::typespec* tps = nullptr;
          auto itr = tscache.find(typeSpecId);
          if (itr == tscache.end()) {
            tps =
                m_helper.compileTypespec(comp, fC, typeSpecId, m_compileDesign,
                                         dest_port, instance, true, true);
            tscache.insert(std::make_pair(typeSpecId, tps));
          } else {
            tps = (*itr).second;
          }
          if (tps) dest_port->Typespec(tps);
        }

        if (ModPort* orig_modport = sig->getModPort()) {
          portInterf.insert(sig->getName());
          ref_obj* ref = s.MakeRef_obj();
          ref->VpiFullName(instance->getFullPathName() + "." + sig->getName());
          ref->VpiFile(fC->getFileName());
          ref->VpiLineNo(fC->Line(sig->getNodeId()));
          ref->VpiColumnNo(fC->Column(sig->getNodeId()));
          ref->VpiEndLineNo(fC->EndLine(sig->getNodeId()));
          ref->VpiEndColumnNo(fC->EndColumn(sig->getNodeId()));
          dest_port->Low_conn(ref);
          Netlist::ModPortMap::iterator itr =
              netlist->getModPortMap().find(signame);
          if (itr == netlist->getModPortMap().end()) {
            ModuleDefinition* orig_interf = orig_modport->getParent();

            interface_array* array_int = nullptr;
            if (unpackedDimensions) {
              array_int = s.MakeInterface_array();
              VectorOfinstance* vec = s.MakeInstanceVec();
              array_int->Instances(vec);
              array_int->Ranges(unpackedDimensions);
              array_int->VpiName(signame);
              array_int->VpiSize(unpackedSize);

              auto array = netlist->interface_arrays();
              if (array == nullptr) {
                netlist->interface_arrays(s.MakeInterface_arrayVec());
                array = netlist->interface_arrays();
              }
              array->push_back(array_int);
              ref->Actual_group(array_int);
            }

            const std::string& sigName = sig->getName();
            ModuleInstance* interfaceRefInstance =
                getInterfaceInstance_(instance, sigName);

            ModuleInstance* interfaceInstance = new ModuleInstance(
                orig_interf, sig->getFileContent(), sig->getNodeId(), instance,
                signame, orig_interf->getName());
            Netlist* netlistInterf = new Netlist(interfaceInstance);
            interfaceInstance->setNetlist(netlistInterf);
            if (interfaceRefInstance) {
              for (auto& itr : interfaceRefInstance->getMappedValues()) {
                interfaceInstance->setValue(itr.first, itr.second.first,
                                            m_exprBuilder, itr.second.second);
              }
            }

            modport* mp = elab_modport_(
                instance, interfaceInstance, signame, orig_interf->getName(),
                orig_interf, instance->getFileName(), instance->getLineNb(),
                orig_modport->getName(), array_int);

            if (unpackedDimensions) {
            } else {
              ref->Actual_group(mp);

              auto interfs = netlist->interfaces();
              if (interfs == nullptr) {
                netlist->interfaces(s.MakeInterfaceVec());
                interfs = netlist->interfaces();
              }
              interfs->push_back((interface*)mp->Interface());
            }

          } else {
            ref->Actual_group((*itr).second.second);
          }
        } else if (ModuleDefinition* orig_interf = sig->getInterfaceDef()) {
          portInterf.insert(sig->getName());
          ref_obj* ref = s.MakeRef_obj();
          ref->VpiFullName(instance->getFullPathName() + "." + sig->getName());
          ref->VpiFile(fC->getFileName());
          ref->VpiLineNo(fC->Line(sig->getNodeId()));
          ref->VpiColumnNo(fC->Column(sig->getNodeId()));
          ref->VpiEndLineNo(fC->EndLine(sig->getNodeId()));
          ref->VpiEndColumnNo(fC->EndColumn(sig->getNodeId()));
          dest_port->Low_conn(ref);
          Netlist::InstanceMap::iterator itr =
              netlist->getInstanceMap().find(signame);
          if (itr == netlist->getInstanceMap().end()) {
            ModuleInstance* interfaceInstance = new ModuleInstance(
                orig_interf, sig->getFileContent(), sig->getNodeId(), instance,
                signame, orig_interf->getName());
            Netlist* netlistInterf = new Netlist(interfaceInstance);
            interfaceInstance->setNetlist(netlistInterf);

            interface_array* array_int = nullptr;
            if (unpackedDimensions) {
              array_int = s.MakeInterface_array();
              VectorOfinstance* vec = s.MakeInstanceVec();
              array_int->Instances(vec);
              array_int->Ranges(unpackedDimensions);
              array_int->VpiName(signame);
              array_int->VpiSize(unpackedSize);

              auto array = netlist->interface_arrays();
              if (array == nullptr) {
                netlist->interface_arrays(s.MakeInterface_arrayVec());
                array = netlist->interface_arrays();
              }
              array->push_back(array_int);
              ref->Actual_group(array_int);
            }

            interface* sm = elab_interface_(
                instance, interfaceInstance, signame, orig_interf->getName(),
                orig_interf, instance->getFileName(), instance->getLineNb(),
                array_int, "");

            if (unpackedDimensions) {
            } else {
              ref->Actual_group(sm);

              auto interfs = netlist->interfaces();
              if (interfs == nullptr) {
                netlist->interfaces(s.MakeInterfaceVec());
                interfs = netlist->interfaces();
              }
              interfs->push_back(sm);
            }

          } else {
            ref->Actual_group((*itr).second.second);
          }
        }

      } else if (pass == 1) {
        // Nets pass
        if (do_ports) continue;
        if (fC->Type(sig->getNodeId()) == slStringConst) {
          const std::string& signame = sig->getName();
          if (portInterf.find(signame) == portInterf.end()) {
            bool sigIsPort = false;
            if (ports) {
              for (auto s : *ports) {
                if (s->VpiName() == signame) {
                  sigIsPort = true;
                }
              }
            }
            elabSignal(sig, instance, child, parentNetlist, netlist, comp,
                       prefix, sigIsPort, tscache);
          }
        }

      } else if (pass == 2) {
        // Port low conn pass
        if (do_ports) continue;
        std::string signame;
        if (fC->Type(sig->getNodeId()) == slStringConst) {
          signame = sig->getName();
        } else {
          portIndex++;
          continue;
        }

        port* dest_port = (*netlist->ports())[portIndex];

        if (sig->getModPort() || sig->getInterfaceDef()) {
          // No rebind
        } else {
          if (any* n = bind_net_(netlist->getParent(), signame)) {
            ref_obj* ref = s.MakeRef_obj();
            ref->VpiName(signame);
            ref->VpiFullName(netlist->getParent()->getFullPathName() + "." +
                             signame);
            ref->VpiFile(fC->getFileName());
            ref->VpiLineNo(fC->Line(sig->getNodeId()));
            ref->VpiColumnNo(fC->Column(sig->getNodeId()));
            ref->VpiEndLineNo(fC->EndLine(sig->getNodeId()));
            ref->VpiEndColumnNo(fC->EndColumn(sig->getNodeId()));
            ref->Actual_group(n);
            dest_port->Low_conn(ref);
          }
        }
      }
      portIndex++;
    }
  }

  return true;
}

UHDM::any* NetlistElaboration::bind_net_(const FileContent* origfC, NodeId id,
                                         ModuleInstance* instance,
                                         ModuleInstance* boundInstance,
                                         const std::string& name) {
  UHDM::any* result = nullptr;
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

    if ((insttype != VObjectType::slConditional_generate_construct) &&
        (insttype != VObjectType::slLoop_generate_construct) &&
        (insttype != VObjectType::slGenerate_item) &&
        (insttype != VObjectType::slGenerate_module_conditional_statement) &&
        (insttype != VObjectType::slGenerate_interface_conditional_statement) &&
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
    }
    itrInst = itrInst->getParent();
  }
  if (instance && (result == nullptr)) {
    DesignComponent* component = instance->getDefinition();
    if (component) {
      for (const auto& tp : component->getTypeDefMap()) {
        TypeDef* tpd = tp.second;
        typespec* tps = tpd->getTypespec();
        if (tps && tps->UhdmType() == uhdmenum_typespec) {
          enum_typespec* etps = (enum_typespec*)tps;
          for (auto n : *etps->Enum_consts()) {
            if (n->VpiName() == name) {
              return n;
            }
          }
        }
      }
      for (const auto& tp : component->getDataTypeMap()) {
        const DataType* dt = tp.second;
        dt = dt->getActual();
        typespec* tps = dt->getTypespec();
        if (tps && tps->UhdmType() == uhdmenum_typespec) {
          enum_typespec* etps = (enum_typespec*)tps;
          for (auto n : *etps->Enum_consts()) {
            if (n->VpiName() == name) {
              return n;
            }
          }
        }
      }
    }

    result = m_helper.getValue(name, instance->getDefinition(), m_compileDesign,
                               instance, "", 0, nullptr, true, true);
  }
  if ((instance != nullptr) && (result == nullptr)) {
    if (Netlist* netlist = instance->getNetlist()) {
      if (name.find('.') == std::string::npos) {  // Not for hierarchical names
        DesignComponent* component = instance->getDefinition();
        VObjectType implicitNetType =
            component->getDesignElement()
                ? component->getDesignElement()->m_defaultNetType
                : slNetType_Wire;
        if (implicitNetType == slNoType) {
          SymbolTable* symbols =
              m_compileDesign->getCompiler()->getSymbolTable();
          ErrorContainer* errors =
              m_compileDesign->getCompiler()->getErrorContainer();

          Location loc(symbols->registerSymbol(origfC->getFileName().string()),
                       id ? origfC->Line(id) : instance->getLineNb(),
                       id ? origfC->Column(id) : instance->getColumnNb(),
                       symbols->registerSymbol(name));
          Error err(ErrorDefinition::ELAB_ILLEGAL_IMPLICIT_NET, loc);
          errors->addError(err);
        }
        // Implicit net
        Serializer& s = m_compileDesign->getSerializer();
        logic_net* net = s.MakeLogic_net();
        net->VpiName(name);
        net->VpiNetType(UhdmWriter::getVpiNetType(implicitNetType));
        net->VpiFile(origfC->getFileName());
        net->VpiLineNo(origfC->Line(id));
        net->VpiColumnNo(origfC->Column(id));
        net->VpiEndLineNo(origfC->EndLine(id));
        net->VpiEndColumnNo(origfC->EndColumn(id));
        result = net;
        Netlist::SymbolTable& symbols = netlist->getSymbolTable();
        std::vector<UHDM::net*>* nets = netlist->nets();
        if (nets == nullptr) {
          nets = s.MakeNetVec();
          netlist->nets(nets);
        }
        nets->push_back(net);
        symbols.insert(std::make_pair(name, result));
      }
    }
  }
  return result;
}

any* NetlistElaboration::bind_net_(ModuleInstance* instance,
                                   const std::string& name) {
  any* result = nullptr;
  Netlist* netlist = instance->getNetlist();
  if (netlist) {
    Netlist::SymbolTable& symbols = netlist->getSymbolTable();
    Netlist::SymbolTable::iterator itr = symbols.find(name);
    if (itr != symbols.end()) {
      return (*itr).second;
    } else {
      std::string basename = name;
      std::string subname;
      if (basename.find('.') != std::string::npos) {
        subname = basename;
        StringUtils::ltrim(subname, '.');
        StringUtils::rtrim(basename, '.');
      }
      itr = symbols.find(basename);
      if (itr != symbols.end()) {
        BaseClass* baseclass = (*itr).second;
        port* conn = any_cast<port*>(baseclass);
        ref_obj* ref1 = nullptr;
        const interface* interf = nullptr;
        if (conn) {
          ref1 = any_cast<ref_obj*>((BaseClass*)conn->Low_conn());
        }
        if (ref1) {
          interf = any_cast<interface*>((BaseClass*)ref1->Actual_group());
        }
        if (interf == nullptr) {
          interf = any_cast<interface*>(baseclass);
        }
        if ((interf == nullptr) && ref1) {
          modport* mport = any_cast<modport*>((BaseClass*)ref1->Actual_group());
          if (mport) {
            interf = mport->Interface();
          }
        }
        if (interf) {
          VectorOfnet* nets = interf->Nets();
          if (nets) {
            for (net* p : *nets) {
              if (p->VpiName() == subname) {
                return p;
              }
            }
          }
        } else {
          modport* mport = any_cast<modport*>(baseclass);
          if (mport) {
            VectorOfio_decl* ios = mport->Io_decls();
            if (ios) {
              for (io_decl* decl : *ios) {
                if (decl->VpiName() == subname) {
                  return (any*)decl->Expr();
                }
              }
            }
          }
        }
      } else {
        if (netlist->variables()) {
          for (variables* var : *netlist->variables()) {
            if (var->VpiName() == name) {
              return var;
            }
          }
        }
        if (netlist->array_vars()) {
          for (variables* var : *netlist->array_vars()) {
            if (var->VpiName() == name) {
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
