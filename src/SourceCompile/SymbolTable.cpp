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
#include <iostream>
#include "SourceCompile/SymbolTable.h"
#include <mutex>
#include <vector>

using namespace SURELOG;

std::string SymbolTable::m_badSymbol("@@BAD_SYMBOL@@");
std::string SymbolTable::m_emptyMacroMarker("@@EMPTY_MACRO@@");
SymbolId SymbolTable::m_badId = 0;

SymbolTable::SymbolTable() : m_idCounter(1) {
  m_id2SymbolMap.push_back(m_badSymbol);
  m_symbol2IdMap.insert(std::make_pair(m_badSymbol, 0));
}

SymbolTable::~SymbolTable() {}

SymbolId SymbolTable::registerSymbol(const std::string symbol) {
  std::unordered_map<std::string, SymbolId>::iterator itr =
      m_symbol2IdMap.find(symbol);
  if (itr == m_symbol2IdMap.end()) {
    m_symbol2IdMap.insert(std::make_pair(symbol, m_idCounter));
    m_id2SymbolMap.push_back(symbol);
    m_idCounter++;
    SymbolId tmp = m_idCounter - 1;
    return (tmp);
  } else {
    SymbolId tmp = (*itr).second;
    return tmp;
  }
}

SymbolId SymbolTable::getId(const std::string symbol) {
  std::unordered_map<std::string, SymbolId>::iterator itr =
      m_symbol2IdMap.find(symbol);
  if (itr == m_symbol2IdMap.end()) {
    return 0;
  } else {
    SymbolId tmp = (*itr).second;
    return tmp;
  }
}

const std::string SymbolTable::getSymbol(SymbolId id) {
  if (id >= m_id2SymbolMap.size())
    return "@@BAD_SYMBOL@@";
  return m_id2SymbolMap[id];
}
