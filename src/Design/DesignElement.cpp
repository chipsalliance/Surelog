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
#include "SourceCompile/SymbolTable.h"
#include "Design/TimeInfo.h"
#include "Design/DesignElement.h"

using namespace SURELOG;

DesignElement::DesignElement(SymbolId name, SymbolId fileId, ElemType type,
                             SymbolId uniqueId, unsigned int line, unsigned short column,
                             unsigned int endLine, unsigned short endColumn,
                             SymbolId parent)
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
      m_context(NULL) {}
