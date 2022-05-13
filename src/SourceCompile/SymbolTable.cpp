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

#include <Surelog/SourceCompile/SymbolTable.h>

#include <cassert>

namespace SURELOG {

SymbolTable::SymbolTable() { registerSymbol(getBadSymbol()); }

SymbolTable::~SymbolTable() {}

const std::string& SymbolTable::getBadSymbol() {
  static const std::string k_badSymbol(BadRawSymbol);
  return k_badSymbol;
}

const std::string& SymbolTable::getEmptyMacroMarker() {
  static const std::string k_emptyMacroMarker("@@EMPTY_MACRO@@");
  return k_emptyMacroMarker;
}

SymbolId SymbolTable::registerSymbol(std::string_view symbol) {
  if (m_parent) {
    if (SymbolId id = m_parent->getId(symbol);
        (id != getBadId() || symbol == getBadSymbol()) && id < m_idOffset) {
      return id;
    }
  }
  assert(symbol.data());
  auto found = m_symbol2IdMap.find(symbol);
  if (found != m_symbol2IdMap.end()) {
    return SymbolId(found->second + m_idOffset, found->first);
  }
  m_id2SymbolMap.emplace_back(symbol);
  const std::string_view normalized_symbol = m_id2SymbolMap.back();
  const auto inserted = m_symbol2IdMap.insert({normalized_symbol, m_idCounter});
  assert(inserted.second);  // This new insert must succeed.
  m_idCounter++;
  return SymbolId(inserted.first->second + m_idOffset, inserted.first->first);
}

SymbolId SymbolTable::getId(std::string_view symbol) const {
  if (m_parent) {
    if (SymbolId id = m_parent->getId(symbol);
        id != getBadId() && id < m_idOffset) {
      return id;
    }
  }

  auto found = m_symbol2IdMap.find(symbol);
  return (found == m_symbol2IdMap.end())
             ? getBadId()
             : SymbolId(found->second + m_idOffset, found->first);
}

const std::string& SymbolTable::getSymbol(SymbolId id) const {
  RawSymbolId rid = (RawSymbolId)id;
  if (id < m_idOffset) {
    assert(m_parent);  // If we have a non-0 idOffset, we must have parent
    return m_parent->getSymbol(id);
  }
  rid -= m_idOffset;
  if (rid >= m_id2SymbolMap.size()) return getBadSymbol();
  return m_id2SymbolMap[rid];
}

void SymbolTable::AppendSymbols(int64_t up_to,
                                std::vector<std::string_view>* dest) const {
  if (m_parent) m_parent->AppendSymbols(m_idOffset, dest);
  up_to -= m_idOffset;
  assert(up_to >= 0);
  for (const auto& s : m_id2SymbolMap) {
    if (up_to-- <= 0) return;
    dest->push_back(s);
  }
}

std::vector<std::string_view> SymbolTable::getSymbols() const {
  std::vector<std::string_view> result;
  result.reserve(m_idOffset + m_id2SymbolMap.size());
  AppendSymbols(m_idOffset + m_id2SymbolMap.size(), &result);
  return result;
}

}  // namespace SURELOG
