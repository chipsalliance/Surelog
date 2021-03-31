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
#include "Utils/StringUtils.h"
#include "SourceCompile/VObjectTypes.h"
#include "Design/VObject.h"
#include "Library/Library.h"
#include "Design/FileContent.h"
#include "SourceCompile/SymbolTable.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/Location.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Config/ConfigSet.h"
#include "CommandLine/CommandLineParser.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/Compiler.h"
#include "DesignCompile/CompileDesign.h"
#include "Testbench/Property.h"
#include "Design/Function.h"
#include "Testbench/ClassDefinition.h"
#include "DesignCompile/NetlistElaboration.h"
#include "Common/PortNetHolder.h"
#include "Design/Enum.h"
#include "Design/Netlist.h"
#include "Design/Struct.h"
#include "Design/Union.h"
#include "Design/SimpleType.h"
#include "Design/ParamAssign.h"
#include "ElaboratorListener.h"
#include "clone_tree.h"
#include <queue>
#include <algorithm>
#include "uhdm.h"
#include "Serializer.h"
#include "UhdmWriter.h"

using namespace SURELOG;
using namespace UHDM;

NetlistElaboration::NetlistElaboration(CompileDesign* compileDesign)
    : TestbenchElaboration(compileDesign) {
  m_exprBuilder.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
  m_exprBuilder.setDesign(m_compileDesign->getCompiler()->getDesign());
  m_helper.seterrorReporting(m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
  m_symbols = m_compileDesign->getCompiler()->getSymbolTable();
  m_errors = m_compileDesign->getCompiler()->getErrorContainer();
}

NetlistElaboration::~NetlistElaboration() {
}

bool NetlistElaboration::elaboratePackages() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  // Packages
  auto& packageDefs = design->getPackageDefinitions();
  for (auto& packageDef : packageDefs) {
    Package* pack = packageDef.second;
    Netlist* netlist = new Netlist(nullptr);
    pack->setNetlist(netlist);
    // Variables in Packages
    for (Signal* sig : pack->getSignals()) {
      elabSignal(sig, nullptr, nullptr, nullptr, netlist, pack, "");
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
  const std::vector<ModuleInstance*>& topModules = design->getTopLevelModuleInstances();
  for (ModuleInstance* inst : topModules) {
    if (!elaborate_(inst, true))
      return false;
  }
  return true;
}

bool NetlistElaboration::elab_parameters_(ModuleInstance* instance, bool param_port) {
  Serializer& s =  m_compileDesign->getSerializer();
  if (!instance) return true;
  bool en_replay = m_compileDesign->getCompiler()->getCommandLineParser()->replay();
  ModuleDefinition* mod =
      dynamic_cast<ModuleDefinition*>(instance->getDefinition());
  if (!mod) return true;
  if (mod->getParameters() != nullptr) {
    // Type params
    for (auto nameParam : mod->getParameterMap()) {
      Parameter* sit = nameParam.second;
      elabTypeParameter_(mod, sit, instance);
    }
  }
  // Regular 
  Netlist* netlist = instance->getNetlist();
  if (netlist == nullptr) return true;
  VectorOfparam_assign* assigns = netlist->param_assigns();
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
    if (mod_assign) {
      const any* rhs = mod_assign->Rhs();
      if (rhs && rhs->UhdmType() == uhdmoperation) {
        operation* op = (operation*)rhs;
        int opType = op->VpiOpType();
        if (opType == vpiCastOp ||
           (opType == vpiMultiConcatOp) ||
           (opType == vpiConditionOp)) {
          isMultidimensional = false;
        }

        // Don't reduce these operations
        if (opType == vpiAssignmentPatternOp || opType == vpiMultiAssignmentPatternOp) {
          ElaboratorListener listener(&s);
          param_assign* pclone = (param_assign*) UHDM::clone_tree(mod_assign, s, &listener);
          pclone->VpiParent((any*) mod_assign->VpiParent());
          
          if (opType == vpiAssignmentPatternOp) {
            const any* lhs = pclone->Lhs();
            any* rhs = (any*) pclone->Rhs();
            m_helper.reorderAssignmentPattern(mod, lhs, rhs, m_compileDesign, instance, 0);
          }
          
          assigns->push_back(pclone);
          continue;
        }
      }
    }

    param_assign* inst_assign = s.MakeParam_assign();
    inst_assign->VpiFile(mod_assign->VpiFile());
    inst_assign->VpiLineNo(mod_assign->VpiLineNo());
    inst_assign->VpiColumnNo(mod_assign->VpiColumnNo());
    inst_assign->Lhs((any*) mod_assign->Lhs());
    const std::string& paramName = assign->getFileContent()->SymName(assign->getParamId());

    bool override = false;
    for (Parameter* tpm :
         instance->getTypeParams()) {  // for parameters that do not resolve to
                                       // scalars (complex structs)
      if (tpm->getName() == paramName) {
        override = true;
        if (ModuleInstance* pinst = instance->getParent()) {
          ModuleDefinition* pmod =
              dynamic_cast<ModuleDefinition*>(pinst->getDefinition());
          expr* rhs = (expr*)m_helper.compileExpression(
              pmod, tpm->getFileContent(), tpm->getNodeId(), m_compileDesign,
              nullptr, pinst, !isMultidimensional);
          
          if (en_replay && m_helper.errorOnNegativeConstant(pmod, rhs, m_compileDesign, pinst)) {
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
              
              if (en_replay && m_helper.errorOnNegativeConstant(mod, crhs, m_compileDesign, instance)) {
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
              Value* v1 = m_exprBuilder.fromVpiValue(s);
              Value* v2 = m_exprBuilder.fromVpiValue("INT:0");
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
    if ((override == false) && (!isMultidimensional)) {
      Value* value = instance->getValue(paramName, m_exprBuilder);
      if (value && value->isValid()) {
        constant* c = s.MakeConstant();
        c->VpiValue(value->uhdmValue());
        c->VpiDecompile(value->decompiledValue());
        c->VpiFile(assign->getFileContent()->getFileName());
        c->VpiSize(value->getSize());
        c->VpiConstType(value->vpiValType());
        c->VpiLineNo(assign->getFileContent()->Line(assign->getAssignId()));
        c->VpiColumnNo(assign->getFileContent()->Column(assign->getAssignId()));
        inst_assign->Rhs(c);
        
        if (en_replay && m_helper.errorOnNegativeConstant(mod, c, m_compileDesign, instance)) {
          bool replay = false;
          //GDB: p replay=true
          if (replay) {
            instance->getValue(paramName, m_exprBuilder);
          }
        }
        
        override = true;
      }
    }
    if (override == false) {
      expr* exp = instance->getComplexValue(paramName);
      if (exp) {
        if (!isMultidimensional) {
          bool invalidValue = false;
          expr* tmp = m_helper.reduceExpr(exp, invalidValue, mod, m_compileDesign, instance, exp->VpiFile(), exp->VpiLineNo(), nullptr, true);
          if (tmp && (invalidValue == false))
            exp = tmp;
        }
        inst_assign->Rhs(exp);
        
        if (en_replay && m_helper.errorOnNegativeConstant(mod, exp, m_compileDesign, instance)) {
          bool replay = false;
          //GDB: p replay=true
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
        
        override = true;
      }
    }
    if (override == false) {
      // Default
      expr* rhs = (expr*)m_helper.compileExpression(
          mod, assign->getFileContent(), assign->getAssignId(), m_compileDesign,
          nullptr, instance, !isMultidimensional);
      inst_assign->Rhs(rhs);
    }

    if (inst_assign) assigns->push_back(inst_assign);
  }
  return true;
}

bool NetlistElaboration::elaborate_(ModuleInstance* instance, bool recurse) {
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
      (insttype != VObjectType::slGenerate_block)
      ) {
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
  if (ModuleDefinition* mm = dynamic_cast<ModuleDefinition*>(childDef)) {
    VObjectType insttype = instance->getType();
    if (insttype == VObjectType::slInterface_instantiation) {
      elab_interface_(instance->getParent(), instance, instance->getInstanceName(),
                      instance->getModuleName(), mm, instance->getFileName(),
                      instance->getLineNb(), nullptr, "");
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

bool NetlistElaboration::high_conn_(ModuleInstance* instance) {
  ModuleInstance* parent = instance->getParent();
  const FileContent* fC = instance->getFileContent();
  NodeId Udp_instantiation = instance->getNodeId();
  Serializer& s = m_compileDesign->getSerializer();
  Netlist* netlist = instance->getNetlist();
  const std::string& instName = instance->getFullPathName();
  VObjectType inst_type = fC->Type(Udp_instantiation);
  std::vector<UHDM::port*>* ports = netlist->ports();
  DesignComponent* comp = instance->getDefinition();
  std::vector<Signal*>* signals = nullptr;
  if (comp) {
    signals = &comp->getPorts();
  }

  if ((inst_type == VObjectType::slUdp_instantiation) ||
     (inst_type == VObjectType::slModule_instantiation) ||
     (inst_type == VObjectType::slProgram_instantiation)||
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
      expr* delay_expr = (expr*) m_helper.compileExpression(comp, fC, Udp_instance, m_compileDesign);
      VectorOfexpr* delays = s.MakeExprVec();
      netlist->delays(delays);
      delays->push_back(delay_expr);     
      Udp_instance = fC->Sibling(Udp_instance);
    }
    NodeId Name_of_instance = fC->Child(Udp_instance);
    NodeId Net_lvalue = 0;
    if (fC->Type(Name_of_instance) == slName_of_instance) {
      Net_lvalue = fC->Sibling(Name_of_instance);
      NodeId Name = fC->Child(Name_of_instance);
      NodeId Unpacked_dimension = fC->Sibling(Name);
      if (Unpacked_dimension) {
        int size;
        VectorOfrange* ranges = m_helper.compileRanges(comp, fC, Unpacked_dimension, m_compileDesign, nullptr, instance, true, size, false);
        netlist->ranges(ranges);
      }
    } else {
      Net_lvalue = Name_of_instance;
      Name_of_instance = 0;
    }
    if (fC->Type(Net_lvalue) == VObjectType::slNet_lvalue) {
      unsigned int index = 0;
      while (Net_lvalue) {
        std::string sigName;
        NodeId sigId = 0; 
        bool bit_or_part_select = false;
        if (fC->Type(Net_lvalue) == VObjectType::slNet_lvalue) {
          NodeId Ps_or_hierarchical_identifier = fC->Child(Net_lvalue);
          if (m_helper.isSelected(fC, Ps_or_hierarchical_identifier))
            bit_or_part_select = true;
          sigId = fC->Child(Ps_or_hierarchical_identifier);
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
              p->High_conn(ref);
              ref->VpiName(sigName);
              any* net = bind_net_(parent, sigName);
              ref->Actual_group(net);
            } else {
              any* exp = nullptr; 
              if (fC->Type(Net_lvalue) == VObjectType::slNet_lvalue) {
                NodeId Ps_or_hierarchical_identifier = fC->Child(Net_lvalue);
                exp = m_helper.compileExpression(comp, fC, Ps_or_hierarchical_identifier, m_compileDesign, nullptr, instance);
              } else {
                exp = m_helper.compileExpression(comp, fC, Net_lvalue, m_compileDesign, nullptr, instance);
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
          if (fC->Type(sigId) == slStringConst) {
            ref_obj* ref = s.MakeRef_obj();
            ref->VpiFile(fC->getFileName());
            ref->VpiLineNo(fC->Line(sigId));
            ref->VpiColumnNo(fC->Column(sigId));
            p->High_conn(ref);
            ref->VpiName(sigName);
            any* net = bind_net_(parent, sigName);
            ref->Actual_group(net);
          } else { 
            any* exp = m_helper.compileExpression(comp, fC, Net_lvalue, m_compileDesign, nullptr, instance);
            p->High_conn(exp);
          }
          ports->push_back(p);
        }
        Net_lvalue = fC->Sibling(Net_lvalue);
        index++;
      }
    } else if (fC->Type(Net_lvalue) == VObjectType::slList_of_port_connections) {
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
      if (fC->Type(Named_port_connection) == VObjectType::slOrdered_port_connection) {
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
        if (formalId == 0)
          break;
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
            tmp =  fC->Sibling(tmp);
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
              }
              operation* op = s.MakeOperation();
              op->VpiOpType(vpiNullOp);
              op->VpiFile(fC->getFileName());
              op->VpiLineNo(fC->Line(tmp));
              op->VpiColumnNo(fC->Column(tmp));
              p->High_conn(op);
              index++;
              continue;
            } else if (fC->Type(tmp) ==
                       slExpression) {  // .p(s) connection by name
              formalId = tmp;
              Expression = tmp;
            }
          } // else .p implicit connection

        }
        NodeId sigId = formalId;
        expr* hexpr = nullptr;
        UHDM::VectorOfattribute* attributes = nullptr;
        if (fC->Type(Expression) == slAttribute_instance) {
           attributes =  m_helper.compileAttributes(comp, fC, Expression, m_compileDesign);
           while (fC->Type(Expression) == slAttribute_instance)
             Expression =  fC->Sibling(Expression);
        }
        if (Expression) {
          hexpr = (expr*) m_helper.compileExpression(comp, fC, Expression, m_compileDesign, nullptr, instance);
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          sigId = fC->Child(Primary_literal);
        }
        std::string sigName;
        if (fC->Name(sigId))
          sigName = fC->SymName(sigId);
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
              if (p == nullptr)
                p = (*ports)[index];
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
          net = bind_net_(parent, sigName);
        }

        if ((!sigName.empty()) && (hexpr == nullptr)) {
          ref_obj* ref = s.MakeRef_obj();
          ref->VpiFile(fC->getFileName());
          ref->VpiLineNo(fC->Line(sigId));
          ref->VpiColumnNo(fC->Column(sigId));
          ref->VpiName(sigName);
          p->High_conn(ref);
          ref->Actual_group(net);
        } else if (hexpr != nullptr) {
          p->High_conn(hexpr);
          if (hexpr->UhdmType() == uhdmref_obj) {
            ((ref_obj*)hexpr)->Actual_group(net);
          }
        }
        p->VpiName(formalName);
        p->Attributes(attributes);
        bool lowconn_is_nettype = false;
        if (const any* lc = p->Low_conn()) {
          if (lc->UhdmType() == uhdmref_obj) {
            ref_obj* rf = (ref_obj*)lc;
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

              ModuleInstance* interfaceInstance = new ModuleInstance(
                  orig_interf, fC, sigId,
                  instance, sigName, orig_interf->getName());
              Netlist* netlistInterf = new Netlist(interfaceInstance);
              interfaceInstance->setNetlist(netlistInterf);

              mp = elab_modport_(instance, interfaceInstance, formalName, orig_interf->getName(),
                                 orig_interf, p->VpiFile(), p->VpiLineNo(),
                                 selectName, nullptr);
            }
          }
          if (mp) {
            ref_obj* ref = s.MakeRef_obj();
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
              sm = elab_interface_(
                  instance, orig_instance, formalName, orig_interf->getName(),
                  orig_interf, instance->getFileName(), instance->getLineNb(), nullptr, "");
            }
          }
          if (sm) {
            ref_obj* ref = s.MakeRef_obj();
            ref->Actual_group(sm);
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
              newPorts->push_back(p);
              pp = p;
            }
            if (pp->High_conn() == nullptr) {
              ref_obj* ref = s.MakeRef_obj();
              ref->VpiFile(fC->getFileName());
              ref->VpiLineNo(wildcardLineNumber);
              ref->VpiColumnNo(wildcardColumnNumber);
              ref->VpiName(sigName);
              pp->High_conn(ref);
              UHDM::any* net = bind_net_(parent, sigName);
              ref->Actual_group(net);
            }  
          }
          netlist->ports(newPorts);
        }
      }
    }
  }
  return true;
}

interface* NetlistElaboration::elab_interface_(ModuleInstance* instance, ModuleInstance* interf_instance, const std::string& instName,
                       const std::string& defName, ModuleDefinition* mod,
                       const std::string& fileName, int lineNb, interface_array* interf_array, const std::string& modPortName) {
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
  //sm->VpiFullName(??);
  sm->VpiFile(fileName);
  sm->VpiLineNo(lineNb);
  subInterfaces->push_back(sm);
  if (interf_array) {
    interf_array->Instances()->push_back(sm);
    netlist->getInstanceMap().insert(std::make_pair(instName, std::make_pair(interf_instance, interf_array)));
    netlist->getSymbolTable().insert(std::make_pair(instName, interf_array));
  } else {
    netlist->getInstanceMap().insert(std::make_pair(instName, std::make_pair(interf_instance, sm)));
    netlist->getSymbolTable().insert(std::make_pair(instName, sm));
  }
  const std::string prefix = instName + ".";
  elab_ports_nets_(instance, interf_instance, instance->getNetlist(), interf_instance->getNetlist(), mod, prefix, true);
  elab_ports_nets_(instance, interf_instance, instance->getNetlist(), interf_instance->getNetlist(), mod, prefix, false);
  // Modports
  ModuleDefinition::ModPortSignalMap& orig_modports = mod->getModPortSignalMap();
  VectorOfmodport* dest_modports = s.MakeModportVec();
  for (auto& orig_modport : orig_modports ) {
    const std::string modportfullname = instName + "." + orig_modport.first  ;
    if ((modPortName != "") && (modportfullname != modPortName))
      continue;
    modport* dest_modport = s.MakeModport();
    dest_modport->Interface(sm);
    dest_modport->VpiParent(sm);
    netlist->getModPortMap().insert(std::make_pair(modportfullname, std::make_pair(&orig_modport.second,dest_modport)));
    netlist->getSymbolTable().insert(std::make_pair(modportfullname, dest_modport));
    dest_modport->VpiName(orig_modport.first);
    VectorOfio_decl* ios = s.MakeIo_declVec();
    for (auto& sig : orig_modport.second.getPorts()) {
      io_decl* io = s.MakeIo_decl();
      io->VpiName(sig.getName());
      unsigned int direction = UhdmWriter::getVpiDirection(sig.getDirection());
      io->VpiDirection(direction);
      any* net = bind_net_(instance, sig.getName());
      io->Expr(net);
      ios->push_back(io);
    }
    dest_modport->Io_decls(ios);
    dest_modports->push_back(dest_modport);
  }
  sm->Modports(dest_modports);

  return sm;
}


modport* NetlistElaboration::elab_modport_(ModuleInstance* instance, ModuleInstance* interfaceInstance, const std::string& instName,
                       const std::string& defName, ModuleDefinition* mod,
                       const std::string& fileName, int lineNb, const std::string& modPortName, UHDM::interface_array* interf_array) {
  Netlist* netlist = instance->getNetlist();
  std::string fullname = instName + "." + modPortName;
  Netlist::ModPortMap::iterator itr = netlist->getModPortMap().find(fullname);
  if (itr == netlist->getModPortMap().end()) {
    elab_interface_(instance, interfaceInstance, instName, defName, mod, fileName, lineNb, interf_array, fullname);
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
  if (ModuleDefinition* mm = dynamic_cast<ModuleDefinition*>(comp_def)) {
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
      gen_scope->VpiName(instance->getInstanceName());
      gen_scope_array->VpiFile(fC->getFileName());
      gen_scope_array->VpiLineNo(fC->Line(mm->getGenBlockId()));
      gen_scope_array->VpiColumnNo(fC->Column(mm->getGenBlockId()));
      gen_scopes->push_back(gen_scope_array);

      if (mm->getContAssigns())
        gen_scope->Cont_assigns(mm->getContAssigns());
      if (mm->getProcesses())
        gen_scope->Process(mm->getProcesses());
      if (mm->getParameters())
        gen_scope->Parameters(mm->getParameters());
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
    if (ModuleDefinition* mm = dynamic_cast<ModuleDefinition*> (childDef)) {
      VObjectType insttype = child->getType();
      if (insttype == VObjectType::slInterface_instantiation) {
        elab_interface_(instance, child, child->getInstanceName(), child->getModuleName(), mm,
                        child->getFileName(),child->getLineNb(), nullptr, "");
      }
    }
  }

  return true;
}

bool NetlistElaboration::elab_ports_nets_(ModuleInstance* instance, bool ports) {
  Netlist* netlist = instance->getNetlist();
  DesignComponent* comp = instance->getDefinition();
  if (comp == nullptr) {
    return true;
  }
  return elab_ports_nets_(instance, instance, netlist, netlist, comp, "", ports);
}

void NetlistElaboration::elabSignal(Signal* sig, ModuleInstance* instance, ModuleInstance* child, 
                                    Netlist* parentNetlist, Netlist* netlist, DesignComponent* comp, 
                                    const std::string& prefix) {
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
  if ((dtype && (subnettype == slNoType)) || sig->isConst() || sig->isVar() || sig->isStatic() ||
      (subnettype == slClass_scope) || (subnettype == slStringConst) ||
      (subnettype == slIntegerAtomType_Int) ||
      (subnettype == slIntegerAtomType_Byte) ||
      (subnettype == slIntegerAtomType_LongInt) ||
      (subnettype == slIntegerAtomType_Shortint) ||
      (subnettype == slString_type) || (subnettype == slNonIntType_Real) ||
      (subnettype == slNonIntType_RealTime) ||
      (subnettype == slNonIntType_ShortReal) ||
      (subnettype == slIntVec_TypeBit)) {
    isNet = false;
  }

  NodeId typeSpecId = sig->getTypeSpecId();
  if (typeSpecId) {
    tps = m_helper.compileTypespec(comp, fC, typeSpecId, m_compileDesign,
                                   nullptr, instance, true);
  }
  if (tps == nullptr) {
    if (sig->getInterfaceTypeNameId()) {
      tps = m_helper.compileTypespec(comp, fC, sig->getInterfaceTypeNameId(),
                                     m_compileDesign, nullptr, instance, true);
    }
  }
  if (tps) {
    typespec* tmp = tps;
    UHDM_OBJECT_TYPE ttmp = tmp->UhdmType();
    if (ttmp == uhdmpacked_array_typespec) {
      tmp = (typespec*) ((packed_array_typespec*) tmp)->Elem_typespec();
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

  if (isNet) {
    // Nets
    if (dtype) {
      dtype = dtype->getActual();
      if (const Enum* en = dynamic_cast<const Enum*>(dtype)) {
        enum_net* stv = s.MakeEnum_net();
        stv->Typespec(en->getTypespec());
        obj = stv;
        if (packedDimensions) {
          packed_array_net* pnets = s.MakePacked_array_net();
          pnets->Ranges(packedDimensions);
          pnets->Elements(s.MakeAnyVec());
          pnets->Elements()->push_back(stv);
          obj = pnets;
        }
      } else if (const Struct* st = dynamic_cast<const Struct*>(dtype)) {
        struct_net* stv = s.MakeStruct_net();
        stv->Typespec(st->getTypespec());
        obj = stv;
        if (packedDimensions) {
          packed_array_net* pnets = s.MakePacked_array_net();
          pnets->Ranges(packedDimensions);
          pnets->Elements(s.MakeAnyVec());
          pnets->Elements()->push_back(stv);
          obj = pnets;
        }
      } else if (const SimpleType* sit =
                     dynamic_cast<const SimpleType*>(dtype)) {
        UHDM::typespec* spec = sit->getTypespec();
        if (spec->UhdmType() == uhdmlogic_typespec) {
          logic_net* logicn = s.MakeLogic_net();
          logicn->VpiSigned(sig->isSigned());
          logicn->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
          logicn->Ranges(packedDimensions);
          logicn->VpiName(signame);
          obj = logicn;
          logicn->Typespec(spec);
        } else if (spec->UhdmType() == uhdmstruct_typespec) {
          struct_net* stv = s.MakeStruct_net();
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
          logicn->VpiSigned(sig->isSigned());
          logicn->Ranges(packedDimensions);
          logicn->VpiName(signame);
          obj = logicn;
          logicn->Typespec(spec);  
        } else if (spec->UhdmType() == uhdmbyte_typespec) {
          byte_var* logicn = s.MakeByte_var();
          logicn->VpiSigned(sig->isSigned());
          logicn->VpiName(signame);
          obj = logicn;
          logicn->Typespec(spec);  
        } else {
          variables* var = m_helper.getSimpleVarFromTypespec(spec, packedDimensions, m_compileDesign);
          var->Expr(exp);
          var->VpiConstantVariable(sig->isConst());
          var->VpiSigned(sig->isSigned());
          var->VpiName(signame);
          obj = var;
        }
      } else {
        logic_net* logicn = s.MakeLogic_net();
        logicn->VpiSigned(sig->isSigned());
        logicn->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
        logicn->Ranges(packedDimensions);
        logicn->VpiName(signame);
        obj = logicn;
      }

      if (unpackedDimensions) {
        array_net* array_net = s.MakeArray_net();
        array_net->Nets(s.MakeNetVec());
        array_net->Ranges(unpackedDimensions);
        array_net->VpiName(signame);
        array_net->VpiSize(unpackedSize);
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
    } else if (subnettype == slStruct_union) {
      // Implicit type
      struct_net* stv = s.MakeStruct_net();
      stv->Typespec(tps);
      obj = stv;
      stv->VpiName(signame);
      if (nets == nullptr) {
        nets = s.MakeNetVec();
        netlist->nets(nets);
      }
      nets->push_back(stv);
    } else if (tps && tps->UhdmType() == uhdminterface_typespec) {
      // No signal needs to be created in that case
      return;
    } else if (tps && tps->UhdmType() == uhdmstruct_typespec) {
      struct_net* stv = s.MakeStruct_net();
      stv->Typespec(tps);
      obj = stv;
      if (unpackedDimensions) {
        array_net* array_net = s.MakeArray_net();
        array_net->Nets(s.MakeNetVec());
        array_net->Ranges(unpackedDimensions);
        array_net->VpiName(signame);
        array_net->VpiSize(unpackedSize);
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
      logicn->Ranges(packedDimensions);
      if (unpackedDimensions) {
        array_net* array_net = s.MakeArray_net();
        array_net->Nets(s.MakeNetVec());
        array_net->Ranges(unpackedDimensions);
        array_net->VpiName(signame);
        array_net->VpiSize(unpackedSize);
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
    if (netlist)  
      netlist->getSymbolTable().insert(std::make_pair(signame, obj));

    if (exp) {
      cont_assign* assign = s.MakeCont_assign();
      assign->VpiFile(fC->getFileName());
      assign->VpiLineNo(fC->Line(id));
      assign->VpiColumnNo(fC->Column(id));
      assign->Lhs((expr*)obj);
      assign->Rhs(exp);
      m_helper.setParentNoOverride((expr*)obj, assign);
      m_helper.setParentNoOverride(exp, assign);
      if (sig->getDelay()) {
        expr* delay_expr = (expr*) m_helper.compileExpression(comp, fC, sig->getDelay(), m_compileDesign);
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
                   unpackedSize, instance, vars, exp, tps);
  }

  if (obj) {
    obj->VpiLineNo(fC->Line(id));
    obj->VpiColumnNo(fC->Column(id));
    obj->VpiFile(fC->getFileName());
    if (parentNetlist)
      parentNetlist->getSymbolTable().insert(std::make_pair(parentSymbol, obj));
    netlist->getSymbolTable().insert(std::make_pair(signame, obj));
  } else {
    // Unsupported type
    ErrorContainer* errors =
        m_compileDesign->getCompiler()->getErrorContainer();
    SymbolTable* symbols = m_compileDesign->getCompiler()->getSymbolTable();
    Location loc(symbols->registerSymbol(fC->getFileName()), fC->Line(id), 0,
                 symbols->registerSymbol(signame));
    Error err(ErrorDefinition::UHDM_UNSUPPORTED_SIGNAL, loc);
    errors->addError(err);
  }
}

bool NetlistElaboration::elab_ports_nets_(ModuleInstance* instance, ModuleInstance* child, Netlist* parentNetlist, 
     Netlist* netlist, DesignComponent* comp, const std::string& prefix, bool do_ports) {
  Serializer& s = m_compileDesign->getSerializer();
  VObjectType compType = comp->getType();
  std::vector<port*>* ports = netlist->ports();
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
    for (Signal* sig : *signals) {
      const FileContent* fC = sig->getFileContent();
      NodeId id = sig->getNodeId();
      if (pass == 0) {
        if (!do_ports)
          continue;
        // Ports pass
        port* dest_port = s.MakePort();
        dest_port->VpiDirection(UhdmWriter::getVpiDirection(sig->getDirection()));
        const std::string& signame = sig->getName();
        dest_port->VpiName(signame);
        dest_port->VpiLineNo(fC->Line(id));
        dest_port->VpiColumnNo(fC->Column(id));
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
           UHDM::typespec* tps = m_helper.compileTypespec(comp, fC, typeSpecId, m_compileDesign, dest_port, instance, true);
           if (tps)
             dest_port->Typespec(tps);
        }

        if (ModPort* orig_modport = sig->getModPort()) {
          portInterf.insert(sig->getName());
          ref_obj* ref = s.MakeRef_obj();
          dest_port->Low_conn(ref);
          Netlist::ModPortMap::iterator itr = netlist->getModPortMap().find(signame);
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
            ModuleInstance* interfaceInstance = new ModuleInstance(
                orig_interf, sig->getFileContent(), sig->getNodeId(), instance,
                signame, orig_interf->getName());
            Netlist* netlistInterf = new Netlist(interfaceInstance);
            interfaceInstance->setNetlist(netlistInterf);

            modport* mp =  elab_modport_(instance, interfaceInstance, signame, orig_interf->getName(), orig_interf,
                        instance->getFileName(),instance->getLineNb(), orig_modport->getName(), array_int);

            if (unpackedDimensions) {
            } else {
              ref->Actual_group(mp);

              auto interfs = netlist->interfaces();
              if (interfs == nullptr) {
                netlist->interfaces(s.MakeInterfaceVec());
                interfs = netlist->interfaces();
              }
              interfs->push_back((interface*) mp->Interface());
            }

          } else {
           ref->Actual_group((*itr).second.second);
          }
        } else if (ModuleDefinition* orig_interf = sig->getInterfaceDef()) {
          portInterf.insert(sig->getName());
          ref_obj* ref = s.MakeRef_obj();
          dest_port->Low_conn(ref);
          Netlist::InstanceMap::iterator itr = netlist->getInstanceMap().find(signame);
          if (itr == netlist->getInstanceMap().end()) {
            ModuleInstance* interfaceInstance = new ModuleInstance(orig_interf, sig->getFileContent(),
                 sig->getNodeId(), instance, signame, orig_interf->getName());
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

            interface* sm =  elab_interface_(instance, interfaceInstance, signame, orig_interf->getName(), orig_interf,
                        instance->getFileName(),instance->getLineNb(), array_int, "");

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
        if (do_ports)
          continue;
        if (portInterf.find(sig->getName()) == portInterf.end())
          elabSignal(sig, instance, child, parentNetlist, netlist, comp, prefix);   

      } else if (pass == 2) {
        // Port low conn pass
        if (do_ports)
          continue;
        const std::string& signame = sig->getName();
        port* dest_port = (*netlist->ports())[portIndex];
     
        if (sig->getModPort() || sig->getInterfaceDef()) {
          // No rebind
        } else {
          if (any* n = bind_net_(netlist->getParent(), signame)) {
            ref_obj* ref = s.MakeRef_obj();
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

any* NetlistElaboration::bind_net_(ModuleInstance* instance, const std::string& name) {
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
      if (strstr(basename.c_str(),".")) {
        subname = basename;
        StringUtils::ltrim(subname,'.');
        StringUtils::rtrim(basename,'.');
      }
      itr = symbols.find(basename);
      if (itr != symbols.end()) {
        BaseClass* baseclass = (*itr).second;
        port* conn = dynamic_cast<port*> (baseclass);
        ref_obj* ref1 = nullptr;
        const interface* interf = nullptr;
        if (conn) {
          ref1 = dynamic_cast<ref_obj*> ((BaseClass*) conn->Low_conn());
        }
        if (ref1) {
          interf = dynamic_cast<interface*> ((BaseClass*) ref1->Actual_group());
        }
        if (interf == nullptr) {
          interf = dynamic_cast<interface*> (baseclass);
        }
        if ((interf == nullptr) && ref1) {
          modport* mport = dynamic_cast<modport*> ((BaseClass*) ref1->Actual_group());
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
          modport* mport = dynamic_cast<modport*> (baseclass);
          if (mport) {
            VectorOfio_decl* ios = mport->Io_decls();
            if (ios) {
              for (io_decl* decl : *ios) {
                if (decl->VpiName() == subname) {
                  return (any*) decl->Expr();
                }
              }
            }
          }
        }
      }
    }
  }
  return result;
}
