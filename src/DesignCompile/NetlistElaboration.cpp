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
#include "Design/Netlist.h"
#include <queue>

#include "uhdm.h"
#include "Serializer.h"
#include "UhdmWriter.h"

using namespace SURELOG;

NetlistElaboration::NetlistElaboration(CompileDesign* compileDesign)
    : TestbenchElaboration(compileDesign) {
  m_exprBuilder.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
}

NetlistElaboration::~NetlistElaboration() {
}


bool NetlistElaboration::elaborate() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  std::vector<ModuleInstance*>& topModules = design->getTopLevelModuleInstances();
  for (ModuleInstance* inst : topModules) {
    if (!elaborate_(inst)) 
      return false;
  }
  return true;
}

bool NetlistElaboration::elaborate_(ModuleInstance* instance) {
  Netlist* netlist = instance->getNetlist();
  if (netlist == nullptr) {
    netlist = new Netlist(instance);
    instance->setNetlist(netlist);
  }
  elab_interfaces_(instance);
  VObjectType insttype = instance->getType();
  if (insttype != VObjectType::slInterface_instantiation) {
    elab_ports_nets_(instance);
  }
  high_conn_(instance);
  elab_cont_assigns_(instance);
  elab_processes_(instance);
  for (unsigned int i = 0; i < instance->getNbChildren(); i++) {
     elaborate_(instance->getChildren(i));
  }
  return true;
}

bool NetlistElaboration::high_conn_(ModuleInstance* instance) {
  ModuleInstance* parent = instance->getParent();
  FileContent* fC = instance->getFileContent();
  NodeId Udp_instantiation = instance->getNodeId();
  Serializer& s = m_compileDesign->getSerializer();
  Netlist* netlist = instance->getNetlist();
  std::string instName = instance->getFullPathName();
  VObjectType inst_type = fC->Type(Udp_instantiation);
  std::vector<UHDM::port*>* ports = netlist->ports();
  DesignComponent* comp = instance->getDefinition();
  VObjectType compType = VObjectType::slNoType;
  if (comp)
    compType = comp->getType();
  std::vector<Signal*>* signals = nullptr;
  if (compType == VObjectType::slModule_declaration) {
    signals = &((ModuleDefinition*) comp)->getPorts();
  } else if (compType == VObjectType::slInterface_declaration) {
    signals = &((ModuleDefinition*) comp)->getPorts();
  } else if (compType == VObjectType::slProgram_declaration) {
    signals = &((Program*) comp)->getPorts();
  } 

  if ((inst_type == VObjectType::slUdp_instantiation) ||
     (inst_type == VObjectType::slModule_instantiation) ||
     (inst_type == VObjectType::slProgram_instantiation)||
     (inst_type == VObjectType::slInterface_instantiation)) {
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
    const std::string& modName = fC->SymName(modId);
    NodeId Udp_instance = fC->Sibling(modId);
    if (fC->Type(Udp_instance) == VObjectType::slParameter_value_assignment) {
      Udp_instance = fC->Sibling(Udp_instance);
    }
    NodeId Name_of_instance = fC->Child(Udp_instance);
    NodeId instId = fC->Child(Name_of_instance);
    const std::string& instName = fC->SymName(instId);
    NodeId Net_lvalue = fC->Sibling(Name_of_instance);
    if (fC->Type(Net_lvalue) == VObjectType::slNet_lvalue) {
      unsigned int index = 0; 
      while (Net_lvalue) {
        std::string sigName;
        if (fC->Type(Net_lvalue) == VObjectType::slNet_lvalue) {
          NodeId Ps_or_hierarchical_identifier = fC->Child(Net_lvalue);
          NodeId sigId = fC->Child(Ps_or_hierarchical_identifier);
          sigName = fC->SymName(sigId);
        } else if (fC->Type(Net_lvalue) == VObjectType::slExpression) {
          NodeId Primary = fC->Child(Net_lvalue);
          NodeId Primary_literal = fC->Child(Primary);
          NodeId sigId = fC->Child(Primary_literal);
          sigName = fC->SymName(sigId);
        }
        if (ports) {
          if (index < ports->size()) {
            port* p = (*ports)[index];
            p->VpiName(sigName);
            ref_obj* ref = s.MakeRef_obj();
            ref->VpiName(sigName);
            p->High_conn(ref);
            any* net = bind_net_(parent, sigName);
            ref->Actual_group(net);
          }
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
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (formalId == 0) 
          break;
        if (fC->Type(formalId) == VObjectType::slExpression) {
          NodeId Expression = formalId;
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          formalId = fC->Child(Primary_literal);
        }
        std::string formalName = fC->SymName(formalId);
        NodeId sigId = formalId;
        NodeId Expression =  fC->Sibling(formalId);
        if (Expression) {
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          sigId = fC->Child(Primary_literal);
        }
        std::string sigName = fC->SymName(sigId);
        std::string baseName = sigName;
        std::string selectName;
        if (NodeId subId = fC->Sibling(sigId)) {
          selectName = fC->SymName(subId);
          sigName += std::string(".") + selectName;
        }
        
        if (ports) {
          if (index < ports->size()) {
            if (orderedConnection) {
              formalName = ((*signals)[index])->getName();
            }
            port* p = (*ports)[index];
            ref_obj* ref = s.MakeRef_obj();
            ref->VpiName(sigName);
            p->VpiName(formalName);
            p->High_conn(ref);
            any* net = bind_net_(parent, sigName);
            ref->Actual_group(net);
            bool lowconn_is_nettype = false;
            if (const any* lc = p->Low_conn()) {
              if (lc->UhdmType() == uhdmref_obj) {
                ref_obj* rf = (ref_obj*) lc;
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
                  mp = elab_modport_(instance, formalName, orig_interf->getName(), orig_interf, 
                          p->VpiFile(),p->VpiLineNo(), selectName);
                }
              }
              if (mp) {
                ref_obj* ref = s.MakeRef_obj();         
                ref->Actual_group(mp);
                p->Low_conn(ref);
              } 
            } else if (net && (net->UhdmType() == uhdminterface) && (lowconn_is_nettype)) {
              BaseClass* sm = nullptr;
              if (orderedConnection) {
                Netlist::InstanceMap::iterator itr = netlist->getInstanceMap().find(formalName);
                if (itr != netlist->getInstanceMap().end()) {
                  sm = (*itr).second.second;
                }
              } else {
                Netlist* parentNetlist = parent->getNetlist();
                Netlist::InstanceMap::iterator itr = parentNetlist->getInstanceMap().find(sigName);
                if (itr != parentNetlist->getInstanceMap().end()) {
                  ModuleInstance* orig_instance = (*itr).second.first;
                  ModuleDefinition* orig_interf = (ModuleDefinition*) orig_instance->getDefinition();
                  sm = elab_interface_(instance, orig_instance, formalName, orig_interf->getName(), orig_interf, 
                        instance->getFileName(),instance->getLineNb());   
                }
              }
              if (sm) {
                ref_obj* ref = s.MakeRef_obj();         
                ref->Actual_group(sm);
                p->Low_conn(ref);
              } 
            } 
          }
        }
        Named_port_connection = fC->Sibling(Named_port_connection);
        index++;
      }
    }
  } 
  return true;
}

interface* NetlistElaboration::elab_interface_(ModuleInstance* instance, ModuleInstance* interf_instance, const std::string& instName,  
                       const std::string& defName, ModuleDefinition* mod,
                       const std::string& fileName, int lineNb) {
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
  netlist->getInstanceMap().insert(std::make_pair(instName, std::make_pair(interf_instance, sm)));
  netlist->getSymbolTable().insert(std::make_pair(instName, sm));
  std::string prefix = instName + ".";
  elab_ports_nets_(instance, instance->getNetlist(), interf_instance->getNetlist(), mod, prefix);

  // Modports
  ModuleDefinition::ModPortSignalMap& orig_modports = mod->getModPortSignalMap();
  VectorOfmodport* dest_modports = s.MakeModportVec();
  for (auto& orig_modport : orig_modports ) {
    modport* dest_modport = s.MakeModport();
    dest_modport->Interface(sm);
    std::string modportfullname = instName + "." + orig_modport.first  ;
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


modport* NetlistElaboration::elab_modport_(ModuleInstance* instance, const std::string& instName,  
                       const std::string& defName, ModuleDefinition* mod,
                       const std::string& fileName, int lineNb, const std::string& modPortName) {
  Netlist* netlist = instance->getNetlist();
  std::string fullname = instName + "." + modPortName;
  Netlist::ModPortMap::iterator itr = netlist->getModPortMap().find(fullname);
  if (itr == netlist->getModPortMap().end()) {
    elab_interface_(instance, instance, instName, defName, mod, fileName, lineNb);
  }
  itr = netlist->getModPortMap().find(fullname);
  if (itr != netlist->getModPortMap().end()) {
    return (*itr).second.second;
  }
  return nullptr;
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
                        child->getFileName(),child->getLineNb());
      }
    }
  }
 
  return true;
}

bool NetlistElaboration::elab_ports_nets_(ModuleInstance* instance) {
  Netlist* netlist = instance->getNetlist();
  DesignComponent* comp = instance->getDefinition();
  if (comp == nullptr) {
    return true;
  }
  return elab_ports_nets_(instance, netlist, netlist, comp, "");
}


bool NetlistElaboration::elab_ports_nets_(ModuleInstance* instance, Netlist* parentNetlist, Netlist* netlist, DesignComponent* comp, const std::string& prefix) {
  Serializer& s = m_compileDesign->getSerializer();
  VObjectType compType = comp->getType();
  std::vector<net*>* nets = netlist->nets();
  std::vector<port*>* ports = netlist->ports();
  for (int pass = 0; pass < 2; pass++) {
    std::vector<Signal*>* signals = nullptr;
    if (compType == VObjectType::slModule_declaration) {
      if (pass == 0)
        signals = &((ModuleDefinition*) comp)->getSignals();
      else
        signals = &((ModuleDefinition*) comp)->getPorts();
    } else if (compType == VObjectType::slInterface_declaration) {
      if (pass == 0)
        signals = &((ModuleDefinition*) comp)->getSignals();
      else
        signals = &((ModuleDefinition*) comp)->getPorts();
    } else if (compType == VObjectType::slProgram_declaration) {
      if (pass == 0)
        signals = &((Program*) comp)->getSignals();
      else 
        signals = &((Program*) comp)->getPorts();
    } else {
      continue;
    }
    for (Signal* sig : *signals) {
      FileContent* fC = sig->getFileContent();
      NodeId id = sig->getNodeId();
      NodeId range = sig->getRange();
      if (pass == 0) {
        logic_net* logicn = s.MakeLogic_net();
        std::string signame = sig->getName();
        std::string parentSymbol = prefix + signame;
        parentNetlist->getSymbolTable().insert(std::make_pair(parentSymbol, logicn));
        netlist->getSymbolTable().insert(std::make_pair(signame, logicn));
        logicn->VpiName(signame);
        logicn->VpiLineNo(fC->Line(id));
        logicn->VpiFile(fC->getFileName());
        logicn->VpiNetType(UhdmWriter::getVpiNetType(sig->getType()));
        if (range) {
          VObjectType rangeType = fC->Type(range);
          if (rangeType == VObjectType::slPacked_dimension) {
            NodeId Constant_range = fC->Child(range);
            NodeId Constant_expression_left =  fC->Child(Constant_range);
            NodeId Constant_expression_right =  fC->Sibling(Constant_expression_left);
            Value* leftV = m_exprBuilder.evalExpr(fC, Constant_expression_left, instance);
            Value* rightV = m_exprBuilder.evalExpr(fC, Constant_expression_right, instance);
            UHDM::constant* leftc = s.MakeConstant();
            leftc->VpiValue(leftV->uhdmValue());
            UHDM::constant* rightc = s.MakeConstant();
            rightc->VpiValue(rightV->uhdmValue());
            logicn->Left_expr(leftc);
            logicn->Right_expr(rightc);
          }
        }
        if (nets == nullptr) {
          nets = s.MakeNetVec();
          netlist->nets(nets);
        } 
        nets->push_back(logicn);
      } else { 
        port* dest_port = s.MakePort();
        dest_port->VpiDirection(UhdmWriter::getVpiDirection(sig->getDirection())); 
        std::string signame = sig->getName();
        dest_port->VpiName(signame);
        dest_port->VpiLineNo(fC->Line(id));
        dest_port->VpiFile(fC->getFileName());
        if (ports == nullptr) {
          ports = s.MakePortVec();
          netlist->ports(ports);
        } 
        ports->push_back(dest_port);

        if (any* n = bind_net_(netlist->getParent(), signame)) {
          ref_obj* ref = s.MakeRef_obj();          
          ref->Actual_group(n);
          dest_port->Low_conn(ref);
        }

        if (ModPort* orig_modport = sig->getModPort()) {
          ref_obj* ref = s.MakeRef_obj();
          dest_port->Low_conn(ref);
          Netlist::ModPortMap::iterator itr = netlist->getModPortMap().find(signame);
          if (itr == netlist->getModPortMap().end()) {
            ModuleDefinition* orig_interf = orig_modport->getParent();
            modport* mp =  elab_modport_(instance, signame, orig_interf->getName(), orig_interf, 
                        instance->getFileName(),instance->getLineNb(), orig_modport->getName());
            ref->Actual_group(mp);            
          } else {
           ref->Actual_group((*itr).second.second); 
          }
        } else if (ModuleDefinition* orig_interf = sig->getInterfaceDef()) {
          ref_obj* ref = s.MakeRef_obj();
          dest_port->Low_conn(ref);
          Netlist::InstanceMap::iterator itr = netlist->getInstanceMap().find(signame);
          if (itr == netlist->getInstanceMap().end()) {
            ModuleInstance* interfaceInstance = new ModuleInstance(orig_interf, sig->getFileContent(),
                 sig->getNodeId(), instance, signame, orig_interf->getName());
            Netlist* netlist = new Netlist(interfaceInstance);
            interfaceInstance->setNetlist(netlist);
            interface* sm =  elab_interface_(instance, interfaceInstance, signame, orig_interf->getName(), orig_interf, 
                        instance->getFileName(),instance->getLineNb());
            ref->Actual_group(sm);
          } else {
            ref->Actual_group((*itr).second.second);
          }
        }
      }
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

expr* NetlistElaboration::bind_expr_(ModuleInstance* instance, expr* ex) {
  Serializer& s = m_compileDesign->getSerializer();
  switch (ex->UhdmType()) {
  case UHDM_OBJECT_TYPE::uhdmref_obj:
  {
    ref_obj* ref = (ref_obj*) ex;
    const std::string& name = ref->VpiName();
    any* object = bind_net_(instance, name);
    ref_obj* newRef = s.MakeRef_obj();
    newRef->VpiName(name);
    newRef->Actual_group(object);
    return newRef;
  }
  default:
    break;
  }
  return nullptr; 
}

 assignment* NetlistElaboration::elab_assignment_(ModuleInstance* instance, assignment* assign) {
   Serializer& s = m_compileDesign->getSerializer();
   const expr* lhs = assign->Lhs();
   const any*  rhs = assign->Rhs();
   assignment* newAssign = s.MakeAssignment();
   if (lhs->UhdmType() == uhdmref_obj) {
     const std::string& name = ((ref_obj*) lhs)->VpiName();
     any* actual = bind_net_(instance, name);
     newAssign->Lhs((expr*) actual);
   }
   if (rhs && (rhs->UhdmType() == uhdmconstant)) {
     newAssign->Rhs((any*) rhs);
   }
   return newAssign;
 }

 initial* NetlistElaboration::elab_initial_(ModuleInstance* instance, initial* init) {
  const any* stmt = init->Stmt();
  Serializer& s = m_compileDesign->getSerializer();
  initial* newInitial = s.MakeInitial();
  if (stmt->UhdmType() == uhdmbegin) {
    begin* newBegin = s.MakeBegin();
    newInitial->Stmt(newBegin);
    VectorOfany* newStmts = s.MakeAnyVec();
    newBegin->Stmts(newStmts);
    begin* begin_block = (begin*) stmt;
    VectorOfany* stmts = begin_block->Stmts();
    if (stmts == nullptr) 
      return nullptr;
    for (any* stmt : *stmts) {
      UHDM_OBJECT_TYPE stmtType = stmt->UhdmType();
      switch (stmtType) {
      case uhdmassignment: {
        assignment* newAssign = elab_assignment_(instance, (assignment*) stmt);
        newStmts->push_back(newAssign);
        break;
      }
      case uhdmdelay_control: {
        delay_control* dc = (delay_control*) stmt;
        delay_control* newDelayControl = s.MakeDelay_control();
        newDelayControl->VpiDelay(dc->VpiDelay());
        const any* the_stmt = dc->Stmt();
        if (the_stmt && (the_stmt->UhdmType() == uhdmassignment)) {
          assignment* newAssign = elab_assignment_(instance, (assignment*) the_stmt);
          newDelayControl->Stmt(newAssign);
        }
        newStmts->push_back(newDelayControl);
        break;
      }
      default:
        break;
      }
    }
  }
  return newInitial;
 }


bool NetlistElaboration::elab_cont_assigns_(ModuleInstance* instance) {
  DesignComponent* comp = instance->getDefinition();
  Netlist* netlist = instance->getNetlist();
  Serializer& s = m_compileDesign->getSerializer();
  if (comp == nullptr) {
    return true;
  }
  VObjectType compType = comp->getType();
  VectorOfcont_assign* cont_assigns = nullptr;
  if (compType == VObjectType::slModule_declaration) {
    cont_assigns = ((ModuleDefinition*) comp)->getContAssigns();
  } else if (compType == VObjectType::slInterface_declaration) {
    cont_assigns = ((ModuleDefinition*) comp)->getContAssigns();
  } else if (compType == VObjectType::slProgram_declaration) {
    cont_assigns = ((Program*) comp)->getContAssigns();
  } 
  if (cont_assigns == nullptr) {
    return true;
  }
  std::vector<UHDM::cont_assign*>* newAssigns = netlist->cont_assigns(); 
  if (newAssigns == nullptr) {
    newAssigns = s.MakeCont_assignVec();
    netlist->cont_assigns(newAssigns);
  }
  for (cont_assign* cassign : *cont_assigns) {
    cont_assign* newAssign = s.MakeCont_assign();
    newAssigns->push_back(newAssign); 
    expr* lexpr = (expr*) cassign->Lhs();
    newAssign->Lhs(bind_expr_(instance, lexpr));
    expr* rexpr = (expr*) cassign->Rhs();
    newAssign->Rhs(bind_expr_(instance, rexpr));
  }
  return true;
}

 bool NetlistElaboration::elab_processes_(ModuleInstance* instance) {
  DesignComponent* comp = instance->getDefinition();
  Netlist* netlist = instance->getNetlist();
  Serializer& s = m_compileDesign->getSerializer();
  if (comp == nullptr) {
    return true;
  }
  VObjectType compType = comp->getType();
  VectorOfprocess* processes = nullptr;
  if (compType == VObjectType::slModule_declaration) {
    processes = ((ModuleDefinition*) comp)->getProcesses();
  } else if (compType == VObjectType::slInterface_declaration) {
    processes = ((ModuleDefinition*) comp)->getProcesses();  
  } else if (compType == VObjectType::slProgram_declaration) {
    processes = ((Program*) comp)->getProcesses();  
  } 
  if (processes == nullptr) {
    return true;
  }
  for (process* p : *processes) {
    UHDM_OBJECT_TYPE processType = p->UhdmType();
    if (processType == uhdminitial) {
      initial* newInitial = elab_initial_(instance, (initial*) p);
      if (netlist->processes() == nullptr) {
        netlist->processes(s.MakeProcessVec());
      }
      netlist->processes()->push_back(newInitial);
    }
  }
  return true;
 }
