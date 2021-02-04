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
  bool elaboratePackages();
  bool elaborateInstance(ModuleInstance* instance);

  virtual ~NetlistElaboration() override;
  void elabSignal(Signal* sig, ModuleInstance* instance, ModuleInstance* child, Netlist* parentNetlist, 
                  Netlist* netlist, DesignComponent* comp, const std::string& prefix);
 private:
   bool elaborate_(ModuleInstance* instance, bool recurse);
   bool high_conn_(ModuleInstance* instance);
   bool elab_parameters_(ModuleInstance* instance, bool port_params);
   bool elab_interfaces_(ModuleInstance* instance);
   bool elab_generates_(ModuleInstance* instance);
  UHDM::interface* elab_interface_(ModuleInstance* instance, ModuleInstance* interf_instance, const std::string& instName,
                       const std::string& defName, ModuleDefinition* mod,
                       const std::string& fileName, int lineNb, UHDM::interface_array* interf_array, const std::string& modPortName);
  UHDM::modport* elab_modport_(ModuleInstance* instance, ModuleInstance* interfInstance, const std::string& instName,
                       const std::string& defName, ModuleDefinition* mod,
                       const std::string& fileName, int lineNb, const std::string& modPortName, UHDM::interface_array* interf_array);
   bool elab_ports_nets_(ModuleInstance* instance, bool ports);
   bool elab_ports_nets_(ModuleInstance* instance, ModuleInstance* child, Netlist* parentNetlist, Netlist* netlist,
                         DesignComponent* comp, const std::string& prefix, bool ports);

  UHDM::any* bind_net_(ModuleInstance* instance, const std::string& name);

};

};  // namespace SURELOG

#endif /* NETLIST_ELABORATION_H */
