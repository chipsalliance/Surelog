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
 * File:   NetlistElaboration.h
 * Author: alain
 *
 * Created on Mar 1, 2020, 6:36 PM
 */

#ifndef NETLIST_ELABORATION_H
#define NETLIST_ELABORATION_H

#include "DesignCompile/ElaborationStep.h"
#include "TestbenchElaboration.h"
#include "Expression/ExprBuilder.h"
#include "Design/Netlist.h"

namespace SURELOG {

class CompileDesign;

class NetlistElaboration : public TestbenchElaboration {
 public:
  NetlistElaboration(CompileDesign* compileDesign);
  NetlistElaboration(const NetlistElaboration& orig) = delete;
  bool elaborate() override;
  
  virtual ~NetlistElaboration() override;

 private:
   bool elaborate_(ModuleInstance* instance);
   bool high_conn_(ModuleInstance* instance);
   bool elab_interfaces_(ModuleInstance* instance);
   interface* elab_interface_(ModuleInstance* instance, ModuleInstance* interf_instance, const std::string& instName,  
                       const std::string& defName, ModuleDefinition* mod, 
                       const std::string& fileName, int lineNb);
   modport* elab_modport_(ModuleInstance* instance, const std::string& instName,  
                       const std::string& defName, ModuleDefinition* mod,
                       const std::string& fileName, int lineNb, const std::string& modPortName);                    
   bool elab_ports_nets_(ModuleInstance* instance);
   bool elab_ports_nets_(ModuleInstance* instance, Netlist* parentNetlist, Netlist* netlist,
                         DesignComponent* comp, const std::string& prefix);
   bool elab_processes_(ModuleInstance* instance);
   bool elab_cont_assigns_(ModuleInstance* instance);
   initial* elab_initial_(ModuleInstance* instance, initial* init);
   assignment* elab_assignment_(ModuleInstance* instance, assignment* assign);
   any* bind_net_(ModuleInstance* instance, const std::string& name);
   expr* bind_expr_(ModuleInstance* instance, expr* ep);

   ExprBuilder m_exprBuilder;
};

};  // namespace SURELOG

#endif /* NETLIST_ELABORATION_H */
