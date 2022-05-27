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
 * File:   VObject.h
 * Author: alain
 *
 * Created on June 14, 2017, 10:58 PM
 */

#ifndef SURELOG_VOBJECT_H
#define SURELOG_VOBJECT_H
#pragma once

#include <Surelog/Common/NodeId.h>
#include <Surelog/Common/SymbolId.h>
#include <Surelog/SourceCompile/VObjectTypes.h>

#include <ostream>
#include <string>

namespace SURELOG {

class SymbolTable;

class VObject final {
 public:
  VObject(SymbolId name, SymbolId fileId, VObjectType type, unsigned int line,
          unsigned short column, unsigned int endLine, unsigned short endColumn,
          NodeId parent = InvalidNodeId)
      : VObject(name, fileId, type, line, column, endLine, endColumn, parent,
                InvalidNodeId /* definition */, InvalidNodeId /* child */,
                InvalidNodeId /* sibling */) {}

  VObject(SymbolId name, SymbolId fileId, VObjectType type, unsigned int line,
          unsigned short column, unsigned int endLine, unsigned short endColumn,
          NodeId parent, NodeId definition, NodeId child, NodeId sibling)
      : m_name(name),
        m_fileId(fileId),
        m_type(type),
        m_column(column),
        m_endColumn(endColumn),
        m_line(line),
        m_endLine(endLine),
        m_parent(parent),
        m_definition(definition),
        m_child(child),
        m_sibling(sibling) {}

  static std::string_view getTypeName(VObjectType type);

  std::string print(SymbolTable* symbols, NodeId uniqueId,
                    SymbolId definitionFile, SymbolId printedFile) const;

  SymbolId m_name;
  SymbolId m_fileId;
  VObjectType m_type;
  unsigned short m_column = 0;
  unsigned short m_endColumn = 0;
  unsigned int m_line = 0;
  unsigned int m_endLine = 0;
  NodeId m_parent;
  NodeId m_definition;
  NodeId m_child;
  NodeId m_sibling;
};

inline std::ostream& operator<<(std::ostream& os, VObjectType type) {
  return os << VObject::getTypeName(type);
}
}  // namespace SURELOG

#endif /* SURELOG_VOBJECT_H */
