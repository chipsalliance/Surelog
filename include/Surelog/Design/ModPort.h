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

#ifndef SURELOG_MODPORT_H
#define SURELOG_MODPORT_H
#pragma once

#include <Surelog/Design/Signal.h>

#include <string_view>
#include <vector>

#include <Surelog/Common/SymbolId.h>

namespace SURELOG {

class ModuleDefinition;
class FileContent;

class ModPort final {
 public:
  ModPort(ModuleDefinition* parent, std::string_view name, const FileContent *const fC, NodeId nodeId)
      : m_parent(parent), m_name(name), m_fileContent(fC), m_nodeId(nodeId) {}

  const std::string& getName() const { return m_name; }
  void addSignal(const Signal& sig) { m_ports.push_back(sig); }
  const std::vector<Signal>& getPorts() const { return m_ports; }
  const Signal* getPort(const std::string& name) const;
  ModuleDefinition* getParent() const { return m_parent; }
  const FileContent* getFileContent() const { return m_fileContent; }
  NodeId getNodeId() const { return m_nodeId; }

 private:
  ModuleDefinition* const m_parent;
  const std::string m_name;
  const FileContent* const m_fileContent;
  const NodeId m_nodeId;

  std::vector<Signal> m_ports;
};
}  // namespace SURELOG

#endif /* SURELOG_MODPORT_H */
