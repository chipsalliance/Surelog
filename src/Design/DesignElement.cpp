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
 * File:   DesignElement.cpp
 * Author: alain
 *
 * Created on June 8, 2017, 8:05 PM
 */

#include <Surelog/Design/DesignElement.h>

namespace SURELOG {
DesignElement::DesignElement(SymbolId name, SymbolId fileId, ElemType type,
                             NodeId uniqueId, unsigned int line,
                             unsigned short column, unsigned int endLine,
                             unsigned short endColumn, NodeId parent)
    : m_name(name),
      m_fileId(fileId),
      m_type(type),
      m_uniqueId(uniqueId),
      m_line(line),
      m_column(column),
      m_endLine(endLine),
      m_endColumn(endColumn),
      m_parent(parent),
      m_node(0),
      m_context(nullptr) {}

std::ostream& operator<<(std::ostream& os, DesignElement::ElemType type) {
  switch (type) {
#define CASE_TYPE_PRINT(e)         \
  case DesignElement::ElemType::e: \
    return os << #e
    CASE_TYPE_PRINT(Module);
    CASE_TYPE_PRINT(Primitive);
    CASE_TYPE_PRINT(Interface);
    CASE_TYPE_PRINT(Program);
    CASE_TYPE_PRINT(Package);
    CASE_TYPE_PRINT(Config);
    CASE_TYPE_PRINT(Checker);
    CASE_TYPE_PRINT(Class);
    CASE_TYPE_PRINT(Function);
    CASE_TYPE_PRINT(Task);
    CASE_TYPE_PRINT(SLline);
#undef CASE_TYPE_PRINT
    // never add a default so that the compiler warns when new choices are added
  }
  return os;
}

}  // namespace SURELOG
