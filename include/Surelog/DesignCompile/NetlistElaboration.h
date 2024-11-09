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

#ifndef SURELOG_NETLISTELABORATION_H
#define SURELOG_NETLISTELABORATION_H
#pragma once

#include <Surelog/DesignCompile/TestbenchElaboration.h>

namespace SURELOG {

class CompileDesign;
class DesignComponent;
class ModuleDefinition;
class ModuleInstance;
class Netlist;
class Signal;

class NetlistElaboration final : public TestbenchElaboration {
 public:
  explicit NetlistElaboration(CompileDesign* compileDesign);
  NetlistElaboration(const NetlistElaboration& orig) = delete;

  bool elaborate() final;
  bool elaboratePackages();
  bool elaborateInstance(ModuleInstance* instance);

  ~NetlistElaboration() final;

  typedef std::map<NodeId, UHDM::typespec*> TypespecCache;
  bool elabSignal(Signal* sig, ModuleInstance* instance, ModuleInstance* child,
                  Netlist* parentNetlist, Netlist* netlist,
                  DesignComponent* comp, std::string_view prefix,
                  bool signalIsPort, TypespecCache& cache, Reduce reduce);

 private:
  bool elaborate_(ModuleInstance* instance, bool recurse);
  bool high_conn_(ModuleInstance* instance);
  bool elab_parameters_(ModuleInstance* instance, bool port_params);
  bool elab_interfaces_(ModuleInstance* instance);
  bool elab_generates_(ModuleInstance* instance);
  UHDM::interface_inst* elab_interface_(
      ModuleInstance* instance, ModuleInstance* interf_instance,
      std::string_view instName, std::string_view defName,
      ModuleDefinition* mod, PathId fileId, uint32_t lineNb,
      UHDM::interface_array* interf_array, std::string_view modPortName);
  UHDM::modport* elab_modport_(ModuleInstance* instance,
                               ModuleInstance* interfInstance,
                               std::string_view instName,
                               std::string_view defName, ModuleDefinition* mod,
                               PathId fileId, uint32_t lineNb,
                               std::string_view modPortName,
                               UHDM::interface_array* interf_array);
  bool elab_ports_nets_(ModuleInstance* instance, bool ports);
  bool elab_ports_nets_(ModuleInstance* instance, ModuleInstance* child,
                        Netlist* parentNetlist, Netlist* netlist,
                        DesignComponent* comp, std::string_view prefix,
                        bool ports);

  UHDM::any* bind_net_(const FileContent* idfC, NodeId id,
                       ModuleInstance* instance, ModuleInstance* boundInstance,
                       std::string_view name);
  UHDM::any* bind_net_(ModuleInstance* instance, std::string_view name);
  ModuleInstance* getInterfaceInstance_(ModuleInstance* instance,
                                        std::string_view sigName);
};

};  // namespace SURELOG

#endif /* SURELOG_NETLIST_ELABORATION_H */
