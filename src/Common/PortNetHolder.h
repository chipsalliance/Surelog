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
 * File:   PortNetHolder.h
 * Author: alain
 *
 * Created on January 30, 2020, 8:31 PM
 */

#include <vector>

// UHDM
#include <uhdm/uhdm_forward_decl.h>

#ifndef PORTNETHOLDER_H
#define PORTNETHOLDER_H

namespace SURELOG {
class Signal;

class PortNetHolder {
 public:
  virtual ~PortNetHolder() {}  // virtual as used as interface

  std::vector<Signal*>& getPorts() { return m_ports; }
  std::vector<Signal*>& getSignals() { return m_signals; }
  std::vector<UHDM::cont_assign*>* getContAssigns() { return m_contAssigns; }

  void setContAssigns(std::vector<UHDM::cont_assign*>* cont_assigns) {
    m_contAssigns = cont_assigns;
  }

  std::vector<UHDM::process_stmt*>* getProcesses() { return m_processes; }
  void setProcesses(std::vector<UHDM::process_stmt*>* processes) {
    m_processes = processes;
  }

  std::vector<UHDM::any*>* getParameters() { return m_parameters; }
  void setParameters(std::vector<UHDM::any*>* parameters) {
    m_parameters = parameters;
  }

  std::vector<UHDM::any*>* getAssertions() { return m_assertions; }
  void setAssertions(std::vector<UHDM::any*>* assertions) {
    m_assertions = assertions;
  }

  std::vector<UHDM::param_assign*>* getParam_assigns() {
    return m_param_assigns;
  }
  void setParam_assigns(std::vector<UHDM::param_assign*>* param_assigns) {
    m_param_assigns = param_assigns;
  }

  std::vector<UHDM::task_func*>* getTask_funcs() { return m_task_funcs; }

  void setTask_funcs(std::vector<UHDM::task_func*>* task_funcs) {
    m_task_funcs = task_funcs;
  }

 protected:
  std::vector<Signal*> m_ports;
  std::vector<Signal*> m_signals;
  std::vector<UHDM::cont_assign*>* m_contAssigns = nullptr;
  std::vector<UHDM::process_stmt*>* m_processes = nullptr;
  std::vector<UHDM::any*>* m_parameters = nullptr;
  std::vector<UHDM::param_assign*>* m_param_assigns = nullptr;
  std::vector<UHDM::task_func*>* m_task_funcs = nullptr;
  std::vector<UHDM::any*>* m_assertions = nullptr;
};

}  // namespace SURELOG

#endif /* PORTNETHOLDER_H */
