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

#include <cassert>

using namespace SURELOG;

SymbolTable::SymbolTable() : m_idCounter(getBadId()) {
  registerSymbol(getBadSymbol());
}

SymbolTable::~SymbolTable() {}

const std::string& SymbolTable::getBadSymbol() {
  static const std::string k_badSymbol("@@BAD_SYMBOL@@");
  return k_badSymbol;
}

const std::string& SymbolTable::getEmptyMacroMarker() {
  static const std::string k_emptyMacroMarker("@@EMPTY_MACRO@@");
  return k_emptyMacroMarker;
}

SymbolId SymbolTable::registerSymbol(std::string_view symbol) {
  assert(symbol.data());
  auto found = m_symbol2IdMap.find(symbol);
  if (found != m_symbol2IdMap.end()) {
    return found->second;
  }
  m_id2SymbolMap.emplace_back(new std::string(symbol));
  const std::string_view normalized_symbol = *m_id2SymbolMap.back();
  const auto inserted = m_symbol2IdMap.insert({normalized_symbol, m_idCounter});
  assert(inserted.second);  // This new insert must succeed.
  m_idCounter++;
  return inserted.first->second;
}

SymbolId SymbolTable::getId(std::string_view symbol) const {
  auto found = m_symbol2IdMap.find(symbol);
  return (found == m_symbol2IdMap.end()) ? getBadId() : found->second;
}

const std::string& SymbolTable::getSymbol(SymbolId id) const {
  if (id >= m_id2SymbolMap.size()) return getBadSymbol();
  return *m_id2SymbolMap[id];
}

std::vector<std::string> SymbolTable::getSymbols() const {
  std::vector<std::string> result;
  result.reserve(m_id2SymbolMap.size());
  for (const auto& s : m_id2SymbolMap) {
    result.push_back(*s);
  }
  return result;
}
