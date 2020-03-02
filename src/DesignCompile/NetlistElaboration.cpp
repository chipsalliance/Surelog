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
#include "Design/Netlist.h"
#include <queue>

#include "uhdm.h"
#include "Serializer.h"

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
  Netlist* netlist = new Netlist();
  instance->setNetlist(netlist);
  high_conn_(instance);
  for (unsigned int i = 0; i < instance->getNbChildren(); i++) {
     elaborate_(instance->getChildren(i));
  }
  return true;
}

bool NetlistElaboration::high_conn_(ModuleInstance* instance) {
  //ModuleInstance* parent = instance->getParent();
  FileContent* fC = instance->getFileContent();
  NodeId Udp_instantiation = instance->getNodeId();
  Serializer& s = m_compileDesign->getSerializer();
  Netlist* netlist = instance->getNetlist();
  VObjectType inst_type = fC->Type(Udp_instantiation);
  if ((inst_type == VObjectType::slUdp_instantiation) ||
     (inst_type == VObjectType::slModule_instantiation) ||
     (inst_type == VObjectType::slProgram_instantiation)) {
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
    NodeId Name_of_instance = fC->Child(Udp_instance);
    NodeId instId = fC->Child(Name_of_instance);
    const std::string& instName = fC->SymName(instId);
    NodeId Net_lvalue = fC->Sibling(Name_of_instance);
    if (fC->Type(Net_lvalue) == VObjectType::slNet_lvalue) {
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
        port* p = s.MakePort();
        p->VpiName(sigName);
        ref_obj* ref = s.MakeRef_obj();
        ref->VpiName(sigName);
        p->High_conn(ref);
        netlist->actualPorts().push_back(p);
        
        Net_lvalue = fC->Sibling(Net_lvalue);
      }
    } else if (fC->Type(Net_lvalue) == VObjectType::slList_of_port_connections) {
      NodeId Named_port_connection = fC->Child(Net_lvalue);
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        const std::string& formalName = fC->SymName(formalId);
        NodeId Expression =  fC->Sibling(formalId);
        NodeId Primary = fC->Child(Expression);
        NodeId Primary_literal = fC->Child(Primary);
        NodeId sigId = fC->Child(Primary_literal);
        const std::string& sigName = fC->SymName(sigId);
        port* p = s.MakePort();
        ref_obj* ref = s.MakeRef_obj();
        ref->VpiName(sigName);
        p->VpiName(formalName);
        p->High_conn(ref);
        netlist->actualPorts().push_back(p);

        Named_port_connection = fC->Sibling(Named_port_connection);
      }
    }
  } 
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
   
  return true;
}