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

#include <map>
#include <string>
#include <vector>

namespace SURELOG {

class ModuleInstance;
class ModPort;

class Netlist {
 public:
  Netlist(ModuleInstance* parent) : m_parent(parent) {}
  ~Netlist();

  typedef std::map<std::string, std::pair<ModPort*, UHDM::modport*>> ModPortMap;
  typedef std::map<std::string, std::pair<ModuleInstance*, UHDM::BaseClass*>>
      InstanceMap;
  typedef std::map<std::string, UHDM::BaseClass*, std::less<>> SymbolTable;

  std::vector<UHDM::interface_inst*>* interfaces() { return m_interfaces; }
  std::vector<UHDM::interface_array*>* interface_arrays() {
    return m_interface_arrays;
  }
  std::vector<UHDM::port*>* ports() { return m_ports; }
  std::vector<UHDM::net*>* nets() { return m_nets; }
  std::vector<UHDM::gen_scope_array*>* gen_scopes() {
    return m_gen_scope_arrays;
  }
  std::vector<UHDM::variables*>* variables() { return m_variables; }
  std::vector<UHDM::array_var*>* array_vars() { return m_array_vars; }
  std::vector<UHDM::array_net*>* array_nets() { return m_array_nets; }
  std::vector<UHDM::named_event*>* named_events() { return m_named_events; }
  std::vector<UHDM::expr*>* delays() { return m_delays; }
  std::vector<UHDM::range*>* ranges() { return m_ranges; }
  std::vector<UHDM::cont_assign*>* cont_assigns() { return m_assign_stmts; }
  std::vector<UHDM::process_stmt*>* process_stmts() { return m_process_stmts; }
  std::vector<UHDM::param_assign*>* param_assigns() { return m_param_assigns; }

  void interfaces(std::vector<UHDM::interface_inst*>* interfaces) {
    m_interfaces = interfaces;
  }
  void interface_arrays(std::vector<UHDM::interface_array*>* interfaces) {
    m_interface_arrays = interfaces;
  }
  void ports(std::vector<UHDM::port*>* ports) { m_ports = ports; }
  void nets(std::vector<UHDM::net*>* nets) { m_nets = nets; }
  void gen_scopes(std::vector<UHDM::gen_scope_array*>* gen_scopes) {
    m_gen_scope_arrays = gen_scopes;
  }
  void variables(std::vector<UHDM::variables*>* variables) {
    m_variables = variables;
  }
  void named_events(std::vector<UHDM::named_event*>* events) {
    m_named_events = events;
  }
  void array_vars(std::vector<UHDM::array_var*>* array_vars) {
    m_array_vars = array_vars;
  }
  void array_nets(std::vector<UHDM::array_net*>* array_nets) {
    m_array_nets = array_nets;
  }
  void delays(std::vector<UHDM::expr*>* delay) { m_delays = delay; }
  void ranges(std::vector<UHDM::range*>* range) { m_ranges = range; }
  void cont_assigns(std::vector<UHDM::cont_assign*>* assigns) {
    m_assign_stmts = assigns;
  }
  void process_stmts(std::vector<UHDM::process_stmt*>* stmts) {
    m_process_stmts = stmts;
  }
  void param_assigns(std::vector<UHDM::param_assign*>* assigns) {
    m_param_assigns = assigns;
  }

  std::vector<UHDM::port*>& actualPorts() { return m_actualPorts; }
  SymbolTable& getSymbolTable() { return m_symbolTable; }
  ModPortMap& getModPortMap() { return m_modPortMap; }
  InstanceMap& getInstanceMap() { return m_instanceMap; }
  ModuleInstance* getParent() { return m_parent; }

 private:
  ModuleInstance* const m_parent;

  // members of the netlist
  std::vector<UHDM::interface_inst*>* m_interfaces = nullptr;
  std::vector<UHDM::interface_array*>* m_interface_arrays = nullptr;
  std::vector<UHDM::net*>* m_nets = nullptr;
  std::vector<UHDM::port*>* m_ports = nullptr;
  std::vector<UHDM::gen_scope_array*>* m_gen_scope_arrays = nullptr;
  std::vector<UHDM::variables*>* m_variables = nullptr;
  std::vector<UHDM::array_var*>* m_array_vars = nullptr;
  std::vector<UHDM::array_net*>* m_array_nets = nullptr;
  std::vector<UHDM::named_event*>* m_named_events = nullptr;
  // properties of the netlist itself (gate)
  std::vector<UHDM::expr*>* m_delays = nullptr;
  std::vector<UHDM::range*>* m_ranges = nullptr;
  std::vector<UHDM::cont_assign*>* m_assign_stmts = nullptr;
  std::vector<UHDM::param_assign*>* m_param_assigns = nullptr;
  std::vector<UHDM::process_stmt*>* m_process_stmts = nullptr;
  // Helpers
  std::vector<UHDM::port*> m_actualPorts;
  SymbolTable m_symbolTable;
  ModPortMap m_modPortMap;
  InstanceMap m_instanceMap;
};

};  // namespace SURELOG

#endif /* SURELOG_NETLIST_H */
