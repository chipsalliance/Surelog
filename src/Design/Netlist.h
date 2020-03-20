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

#ifndef NETLIST_H
#define NETLIST_H
#include <string>
#include <vector>
#include <map>
#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"
#include "Design/ModPort.h"

namespace UHDM {
  class port;
  class net;
  class process;
  class cont_assign;
  class BaseClass;
  class modport;
  class interface;
};

namespace SURELOG {

class Netlist {
 public:
  Netlist() : m_interfaces(NULL), m_nets(NULL), m_ports(NULL), m_processes(NULL), m_cont_assigns(NULL) {}
  ~Netlist();

  typedef std::map<std::string, std::pair<ModPort*, UHDM::modport*>> ModPortMap;
  typedef std::map<std::string, UHDM::BaseClass*> InstanceMap;
  typedef std::map<std::string, UHDM::BaseClass*> SymbolTable;

  std::vector<UHDM::interface*>*   interfaces() { return m_interfaces; }
  std::vector<UHDM::port*>*        ports() { return m_ports;}
  std::vector<UHDM::net*>*         nets() { return m_nets;}
  std::vector<UHDM::process*>*     processes() { return m_processes; }
  std::vector<UHDM::cont_assign*>* cont_assigns() { return m_cont_assigns; }

  void interfaces(std::vector<UHDM::interface*>* interfaces) { m_interfaces = interfaces; }
  void ports(std::vector<UHDM::port*>* ports) { m_ports = ports;}
  void nets(std::vector<UHDM::net*>* nets) { m_nets = nets;}
  void processes(std::vector<UHDM::process*>* processes) { m_processes = processes; }
  void cont_assigns(std::vector<UHDM::cont_assign*>* cont_assigns) { m_cont_assigns = cont_assigns; }

  std::vector<UHDM::port*>& actualPorts() { return m_actualPorts;}
  SymbolTable&  getSymbolTable() { return m_symbolTable; }
  ModPortMap& getModPortMap() { return m_modPortMap; }
  InstanceMap& getInstanceMap() { return m_instanceMap; }
 private:
  std::vector<UHDM::interface*>*   m_interfaces;
  std::vector<UHDM::net*>*         m_nets;
  std::vector<UHDM::port*>*        m_ports;
  std::vector<UHDM::process*>*     m_processes;
  std::vector<UHDM::cont_assign*>* m_cont_assigns;

  // Helpers
  std::vector<UHDM::port*> m_actualPorts;
  SymbolTable m_symbolTable;
  ModPortMap m_modPortMap;
  InstanceMap m_instanceMap;
};

};  // namespace SURELOG

#endif /* NETLIST_H */