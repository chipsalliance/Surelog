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
 * File:   SymbolTable.cpp
 * Author: alain
 *
 * Created on March 6, 2017, 11:10 PM
 */
#include "SourceCompile/SymbolTable.h"

using namespace SURELOG;

SymbolTable::SymbolTable() : m_idCounter(0) { registerSymbol(getBadSymbol()); }

SymbolTable::~SymbolTable() {}

std::string_view SymbolTable::getBadSymbol() {
  static constexpr std::string_view k_badSymbol("@@BAD_SYMBOL@@");
  return k_badSymbol;
}

std::string_view SymbolTable::getEmptyMacroMarker() {
  static constexpr std::string_view k_emptyMacroMarker("@@EMPTY_MACRO@@");
  return k_emptyMacroMarker;
}

SymbolId SymbolTable::registerSymbol(std::string_view symbol) {
  Symbol2IdMap::const_iterator it = m_symbol2IdMap.find(symbol);
  if (it == m_symbol2IdMap.end()) {
    if (buffers.empty() || (buffers.back().size() + symbol.length() + 1) >
                               buffers.back().capacity()) {
      buffers.push_back(buffers_t::value_type());
      buffers.back().reserve(kBufferCapacity);
    }

    buffers_t::reference buffer = buffers.back();
    size_t length = buffer.length();
    buffer.append(symbol).append(1, '\0');
    symbol = std::string_view(&buffer[length], symbol.length());

    it = m_symbol2IdMap.insert({symbol, m_idCounter}).first;
    m_id2SymbolMap.emplace_back(symbol);
    m_idCounter++;
  }
  return it->second;
}

SymbolId SymbolTable::getId(std::string_view symbol) const {
  auto found = m_symbol2IdMap.find(symbol);
  return (found == m_symbol2IdMap.end()) ? getBadId() : found->second;
}

std::string_view SymbolTable::getSymbol(SymbolId id) const {
  return (id >= m_id2SymbolMap.size()) ? getBadSymbol() : m_id2SymbolMap[id];
}
