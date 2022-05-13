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
 * File:   VObject.cpp
 * Author: alain
 *
 * Created on June 14, 2017, 10:58 PM
 */

#include <Surelog/Design/VObject.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/StringUtils.h>

namespace SURELOG {

std::string VObject::print(SymbolTable* symbols, NodeId uniqueId,
                           SymbolId definitionFile,
                           SymbolId printedFile) const {
  std::string text;
  const std::string& symbol = symbols->getSymbol(m_name);
  if (symbol == SymbolTable::getBadSymbol()) {
    StrAppend(&text, "n<>");
  } else {
    StrAppend(&text, "n<", symbol, ">");
  }
  StrAppend(&text, " u<", uniqueId, "> ");
  StrAppend(&text, "t<", getTypeName(m_type).substr(2), ">");
  if (m_parent) StrAppend(&text, " p<", m_parent, ">");
  if (m_definition) StrAppend(&text, " d<", m_definition, ">");
  if (definitionFile) StrAppend(&text, " df<", definitionFile, ">");
  if (m_child) StrAppend(&text, " c<", m_child, ">");
  if (m_sibling) StrAppend(&text, " s<", m_sibling, ">");

  StrAppend(&text, " ");
  if (printedFile != m_fileId) StrAppend(&text, "f<", m_fileId, "> ");

  StrAppend(&text, "l<", m_line, ":", m_column, ">");
  if (m_endLine) StrAppend(&text, " el<", m_endLine, ":", m_endColumn, ">");

  return text;
}
}  // namespace SURELOG
