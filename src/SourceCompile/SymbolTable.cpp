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

#include <cstdlib>
#include <iostream>

using namespace SURELOG;

SymbolTable::SymbolTable() { registerSymbol(getBadSymbol()); }

SymbolTable::SymbolTable(const SymbolTable &other)
    : m_minWriteIndex(other.m_buffers.size()),
      m_buffers(other.m_buffers),
      m_id2SymbolMap(other.m_id2SymbolMap),
      m_symbol2IdMap(other.m_symbol2IdMap) {}

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
    if ((m_buffers.size() <= m_minWriteIndex) ||
        (m_buffers.back()->size() + symbol.length() + 1) >
            m_buffers.back()->capacity()) {
      m_buffers.emplace_back(std::make_shared<std::string>());
      m_buffers.back()->reserve(kBufferCapacity);
    }

    Buffers::reference buffer = m_buffers.back();
    size_t length = buffer->length();
    buffer->append(symbol).append(1, '\0');
    symbol = std::string_view(&(*buffer)[length], symbol.length());
    it = m_symbol2IdMap.insert({symbol, m_id2SymbolMap.size()}).first;
    m_id2SymbolMap.emplace_back(symbol);
  }
  return it->second;
}

std::vector<std::string> SymbolTable::getSymbols() const {
  std::vector<std::string> result;
  result.reserve(m_id2SymbolMap.size());
  for (auto s : m_id2SymbolMap) {
    result.emplace_back(s);
  }
  return result;
}
