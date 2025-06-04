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

#ifndef SURELOG_PORTNETHOLDER_H
#define SURELOG_PORTNETHOLDER_H
#pragma once

// UHDM
#include <uhdm/uhdm_forward_decl.h>

#include <algorithm>
#include <vector>

namespace SURELOG {

class Signal;

class PortNetHolder {
 public:
  virtual ~PortNetHolder() = default;  // virtual as used as interface

  const std::vector<Signal*>& getPorts() const { return m_ports; }
  const std::vector<Signal*>& getSignals() const { return m_signals; }

  void addPort(Signal* signal) { m_ports.emplace_back(signal); }

  void addSignal(Signal* signal) { m_signals.emplace_back(signal); }

  bool removePort(Signal* signal) {
    auto it = std::find(m_ports.begin(), m_ports.end(), signal);
    if (it != m_ports.end()) {
      m_ports.erase(it);
      return true;
    }
    return false;
  }

  bool removeSignal(Signal* signal) {
    auto it = std::find(m_signals.begin(), m_signals.end(), signal);
    if (it != m_signals.end()) {
      m_signals.erase(it);
      return true;
    }
    return false;
  }

  std::vector<uhdm::ContAssign*>* getContAssigns() const {
    return m_contAssigns;
  }

  void setContAssigns(std::vector<uhdm::ContAssign*>* cont_assigns) {
    m_contAssigns = cont_assigns;
  }

  std::vector<uhdm::Process*>* getProcesses() const { return m_processes; }
  void setProcesses(std::vector<uhdm::Process*>* processes) {
    m_processes = processes;
  }

  std::vector<uhdm::Any*>* getParameters() const { return m_parameters; }
  void setParameters(std::vector<uhdm::Any*>* parameters) {
    m_parameters = parameters;
  }

  std::vector<uhdm::Any*>* getAssertions() const { return m_assertions; }
  void setAssertions(std::vector<uhdm::Any*>* assertions) {
    m_assertions = assertions;
  }

  std::vector<uhdm::ParamAssign*>* getParamAssigns() const {
    return m_paramAssigns;
  }
  void setParam_assigns(std::vector<uhdm::ParamAssign*>* param_assigns) {
    m_paramAssigns = param_assigns;
  }

  std::vector<uhdm::ParamAssign*>* getOrigParam_assigns() const {
    return m_origParamAssigns;
  }
  void setOrigParam_assigns(std::vector<uhdm::ParamAssign*>* param_assigns) {
    m_origParamAssigns = param_assigns;
  }

  std::vector<uhdm::TaskFunc*>* getTaskFuncs() const { return m_taskFuncs; }

  void setTaskFuncs(std::vector<uhdm::TaskFunc*>* taskFuncs) {
    m_taskFuncs = taskFuncs;
  }

  std::vector<uhdm::TaskFuncDecl*>* getTaskFuncDecls() const {
    return m_taskFuncDecls;
  }

  void setTaskFuncDecls(std::vector<uhdm::TaskFuncDecl*>* taskFuncDecls) {
    m_taskFuncDecls = taskFuncDecls;
  }

 protected:
  std::vector<Signal*> m_ports;
  std::vector<Signal*> m_signals;
  std::vector<uhdm::ContAssign*>* m_contAssigns = nullptr;
  std::vector<uhdm::Process*>* m_processes = nullptr;
  std::vector<uhdm::Any*>* m_parameters = nullptr;
  std::vector<uhdm::ParamAssign*>* m_paramAssigns = nullptr;
  std::vector<uhdm::ParamAssign*>* m_origParamAssigns = nullptr;
  std::vector<uhdm::TaskFunc*>* m_taskFuncs = nullptr;
  std::vector<uhdm::TaskFuncDecl*>* m_taskFuncDecls = nullptr;
  std::vector<uhdm::Any*>* m_assertions = nullptr;
};

}  // namespace SURELOG

#endif /* SURELOG_PORTNETHOLDER_H */
