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
 * File:   Netlist.h
 * Author: alain
 *
 * Created on April 15, 2019, 8:03 PM
 */

#ifndef SURELOG_NETLIST_H
#define SURELOG_NETLIST_H
#pragma once

// UHDM
#include <uhdm/uhdm_forward_decl.h>

#include <functional>
#include <map>
#include <string>
#include <utility>
#include <vector>

namespace SURELOG {

class ModuleInstance;
class Modport;
class Session;

class Netlist {
 public:
  explicit Netlist(ModuleInstance* parent) : m_parent(parent) {}
  ~Netlist();

  using ModportMap =
      std::map<std::string, std::pair<Modport*, uhdm::Modport*>, std::less<>>;
  using InstanceMap =
      std::map<std::string, std::pair<ModuleInstance*, uhdm::BaseClass*>,
               std::less<>>;
  using SymbolTable = std::map<std::string, uhdm::BaseClass*, std::less<>>;

  std::vector<uhdm::Interface*>* interfaces() { return m_interfaces; }
  std::vector<uhdm::InterfaceArray*>* interface_arrays() {
    return m_interface_arrays;
  }
  std::vector<uhdm::Port*>* ports() { return m_ports; }
  std::vector<uhdm::Net*>* nets() { return m_nets; }
  std::vector<uhdm::GenScopeArray*>* gen_scopes() { return m_gen_scope_arrays; }
  std::vector<uhdm::Variables*>* variables() { return m_variables; }
  std::vector<uhdm::ArrayVar*>* array_vars() { return m_array_vars; }
  std::vector<uhdm::ArrayNet*>* array_nets() { return m_array_nets; }
  std::vector<uhdm::NamedEvent*>* named_events() { return m_named_events; }
  std::vector<uhdm::Expr*>* delays() { return m_delays; }
  std::vector<uhdm::Range*>* ranges() { return m_ranges; }
  std::vector<uhdm::ContAssign*>* cont_assigns() { return m_assign_stmts; }
  std::vector<uhdm::Process*>* process_stmts() { return m_process_stmts; }
  std::vector<uhdm::ParamAssign*>* param_assigns() { return m_param_assigns; }

  void interfaces(std::vector<uhdm::Interface*>* interfaces) {
    m_interfaces = interfaces;
  }
  void interface_arrays(std::vector<uhdm::InterfaceArray*>* interfaces) {
    m_interface_arrays = interfaces;
  }
  void ports(std::vector<uhdm::Port*>* ports) { m_ports = ports; }
  void nets(std::vector<uhdm::Net*>* nets) { m_nets = nets; }
  void gen_scopes(std::vector<uhdm::GenScopeArray*>* gen_scopes) {
    m_gen_scope_arrays = gen_scopes;
  }
  void variables(std::vector<uhdm::Variables*>* variables) {
    m_variables = variables;
  }
  void named_events(std::vector<uhdm::NamedEvent*>* events) {
    m_named_events = events;
  }
  void array_vars(std::vector<uhdm::ArrayVar*>* array_vars) {
    m_array_vars = array_vars;
  }
  void array_nets(std::vector<uhdm::ArrayNet*>* array_nets) {
    m_array_nets = array_nets;
  }
  void delays(std::vector<uhdm::Expr*>* delay) { m_delays = delay; }
  void ranges(std::vector<uhdm::Range*>* range) { m_ranges = range; }
  void cont_assigns(std::vector<uhdm::ContAssign*>* assigns) {
    m_assign_stmts = assigns;
  }
  void process_stmts(std::vector<uhdm::Process*>* stmts) {
    m_process_stmts = stmts;
  }
  void param_assigns(std::vector<uhdm::ParamAssign*>* assigns) {
    m_param_assigns = assigns;
  }

  std::vector<uhdm::Port*>& actualPorts() { return m_actualPorts; }
  SymbolTable& getSymbolTable() { return m_symbolTable; }
  ModportMap& getModportMap() { return m_modPortMap; }
  InstanceMap& getInstanceMap() { return m_instanceMap; }
  ModuleInstance* getParent() { return m_parent; }

 private:
  ModuleInstance* const m_parent = nullptr;

  // members of the netlist
  std::vector<uhdm::Interface*>* m_interfaces = nullptr;
  std::vector<uhdm::InterfaceArray*>* m_interface_arrays = nullptr;
  std::vector<uhdm::Net*>* m_nets = nullptr;
  std::vector<uhdm::Port*>* m_ports = nullptr;
  std::vector<uhdm::GenScopeArray*>* m_gen_scope_arrays = nullptr;
  std::vector<uhdm::Variables*>* m_variables = nullptr;
  std::vector<uhdm::ArrayVar*>* m_array_vars = nullptr;
  std::vector<uhdm::ArrayNet*>* m_array_nets = nullptr;
  std::vector<uhdm::NamedEvent*>* m_named_events = nullptr;
  // properties of the netlist itself (gate)
  std::vector<uhdm::Expr*>* m_delays = nullptr;
  std::vector<uhdm::Range*>* m_ranges = nullptr;
  std::vector<uhdm::ContAssign*>* m_assign_stmts = nullptr;
  std::vector<uhdm::ParamAssign*>* m_param_assigns = nullptr;
  std::vector<uhdm::Process*>* m_process_stmts = nullptr;
  // Helpers
  std::vector<uhdm::Port*> m_actualPorts;
  SymbolTable m_symbolTable;
  ModportMap m_modPortMap;
  InstanceMap m_instanceMap;
};

};  // namespace SURELOG

#endif /* SURELOG_NETLIST_H */
