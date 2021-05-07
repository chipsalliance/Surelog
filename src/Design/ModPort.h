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
 * File:   ModPort.h
 * Author: alain
 *
 * Created on January 31, 2020, 9:46 PM
 */
#ifndef MODPORT_H
#define MODPORT_H

#include <vector>

#include "Signal.h"
#include "SourceCompile/SymbolTable.h"

namespace SURELOG {

class ModuleDefinition;

class ModPort final {
 public:
  ModPort(ModuleDefinition* parent, const std::string_view name)
      : m_parent(parent), m_name(name) {}

  const std::string& getName() const { return m_name; }
  void addSignal(const Signal& sig) { m_ports.push_back(sig); }
  const std::vector<Signal>& getPorts() const { return m_ports; }
  const Signal* getPort(const std::string& name) const;
  ModuleDefinition* getParent() { return m_parent; }

 private:
  ModuleDefinition* const m_parent;
  const std::string m_name;

  std::vector<Signal> m_ports;
};
}  // namespace SURELOG

#endif /* MODPORT_H */
