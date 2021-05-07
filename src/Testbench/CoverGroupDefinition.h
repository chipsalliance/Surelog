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
 * File:   CoverGroupDefinition.h
 * Author: alain
 *
 * Created on March 20, 2019, 9:06 PM
 */

#ifndef COVERGROUPDEFINITION_H
#define COVERGROUPDEFINITION_H

#include <string_view>

#include "Design/FileContent.h"
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/VObjectTypes.h"

namespace SURELOG {

class CoverGroupDefinition final {
 public:
  CoverGroupDefinition(const FileContent* fC, NodeId id, std::string_view name)
      : m_fileContent(fC), m_nodeId(id), m_name(name) {}

  const std::string& getName() const { return m_name; }

  const FileContent* getFileContent() const { return m_fileContent; }

  NodeId getNodeId() const { return m_nodeId; }

 private:
  CoverGroupDefinition(const CoverGroupDefinition&) = delete;

  // Set in constructor, never updated, no copy constructor. Can be const.
  const FileContent* const m_fileContent;
  const NodeId m_nodeId;
  const std::string m_name;
};

}  // namespace SURELOG

#endif /* COVERGROUPDEFINITION_H */
