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

const std::string SymbolTable::s_badSymbol("@@BAD_SYMBOL@@");
const std::string SymbolTable::s_emptyMacroMarker("@@EMPTY_MACRO@@");
const SymbolId SymbolTable::s_badId = 0;

SymbolTable::SymbolTable() : m_idCounter(1) {
  m_id2SymbolMap.push_back(s_badSymbol);
  m_symbol2IdMap.insert(std::make_pair(s_badSymbol, 0));
}

SymbolTable::~SymbolTable() {}

SymbolId SymbolTable::registerSymbol(const std::string& symbol) {
  // TODO: use std::string_view and heterogeneous lookup
  std::unordered_map<std::string, SymbolId>::const_iterator itr =
      m_symbol2IdMap.find(symbol);
  if (itr == m_symbol2IdMap.end()) {
    m_symbol2IdMap.insert(std::make_pair(symbol, m_idCounter));
    m_id2SymbolMap.emplace_back(symbol);
    m_idCounter++;
    SymbolId tmp = m_idCounter - 1;
    return (tmp);
  } else {
    SymbolId tmp = (*itr).second;
    return tmp;
  }
}

SymbolId SymbolTable::getId(const std::string& symbol) const {
  // TODO: use std::string_view and heterogeneous lookup
  std::unordered_map<std::string, SymbolId>::const_iterator itr =
      m_symbol2IdMap.find(symbol);
  if (itr == m_symbol2IdMap.end()) {
    return s_badId;
  } else {
    SymbolId tmp = (*itr).second;
    return tmp;
  }
}

const std::string& SymbolTable::getSymbol(SymbolId id) const {
  if (id >= m_id2SymbolMap.size())
    return s_badSymbol;
  return m_id2SymbolMap[id];
}
