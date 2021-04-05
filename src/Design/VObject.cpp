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
#include <string>
#include "SourceCompile/SymbolTable.h"
#include "Design/VObject.h"

using namespace SURELOG;

std::string VObject::print(SymbolTable* symbols, unsigned int uniqueId,
                           NodeId definitionFile) const {
  std::string text;
  std::string symbol = symbols->getSymbol(m_name);
  if (symbol == symbols->getBadSymbol()) {
    text += "n<>";
  } else {
    text = "n<" + symbols->getSymbol(m_name) + ">";
  }

  text += " ";
  text += "u<" + std::to_string(uniqueId) + ">";
  text += " ";
  std::string type = getTypeName(m_type);
  type.erase(0, 2);
  text += "t<" + type + ">";
  if (m_parent) {
    text += " ";
    text += "p<" + std::to_string(m_parent) + ">";
  }
  if (m_definition) {
    text += " ";
    text += "d<" + std::to_string(m_definition) + ">";
  }
  if (definitionFile) {
    text += " ";
    text += "df<" + std::to_string(definitionFile) + ">";
  }
  if (m_child) {
    text += " ";
    text += "c<" + std::to_string(m_child) + ">";
  }
  if (m_sibling) {
    text += " ";
    text += "s<" + std::to_string(m_sibling) + ">";
  }
  text += " ";
  text += "l<" + std::to_string(m_line) + ":" + std::to_string(m_column) + ">";
  if (m_endLine) {
    text += " ";
    text += "el<" + std::to_string(m_endLine) + ":" + std::to_string(m_endColumn) + ">";
  }
  return text;
}
