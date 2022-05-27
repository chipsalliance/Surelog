
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
 * File:   SymbolTable.h
 * Author: alain
 *
 * Created on March 6, 2017, 11:10 PM
 */

#ifndef SURELOG_SYMBOLTABLE_H
#define SURELOG_SYMBOLTABLE_H
#pragma once

#include <Surelog/Common/SymbolId.h>

#include <deque>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace SURELOG {

class SymbolTable final {
 public:
  SymbolTable();
  ~SymbolTable();

  // Create a snapshot of this symbol table. The returned SymbolTable contains
  // all the symbols this table has and allows to then continue using the new
  // copy without changing the original. Essentially a fork.
  // TODO: at some point, return std::unique_ptr<>
  SymbolTable* CreateSnapshot() const;

  // Register given "symbol" string as a symbol and return its id.
  // If this is an existing symbol, its ID is returned, otherwise a new one
  // is created.
  SymbolId registerSymbol(std::string_view symbol);

  // Find id of given "symbol" or return bad-ID (see #getBad()) if it doesn't
  // exist.
  SymbolId getId(std::string_view symbol) const;

  // Get symbol string identified by given ID or BadSymbol if it doesn't exist
  // (see #getBadSymbol()).
  const std::string& getSymbol(SymbolId id) const;

  // Get a vector of all symbols. As a special property, the SymbolID can be
  // used as an index into this  vector to get the corresponding text-symbol.
  std::vector<std::string_view> getSymbols() const;

  static const std::string& getBadSymbol();
  static SymbolId getBadId() { return BadSymbolId; }
  static const std::string& getEmptyMacroMarker();

 private:
  // Create a snapshot of the current symbol table. Private, as this
  // functionality should be explicitly accessed through CreateSnapshot().
  SymbolTable(const SymbolTable& parent)
      : m_parent(&parent), m_idOffset(parent.m_idCounter + parent.m_idOffset) {}

  void AppendSymbols(int64_t up_to, std::vector<std::string_view>* dest) const;

  const SymbolTable *const m_parent;
  const RawSymbolId m_idOffset;

  RawSymbolId m_idCounter = 0;

  // Stable strings whose address doesn't change with reallocations.
  std::deque<std::string> m_id2SymbolMap;

  // The key string_views point to the stable backing buffer provided in
  // m_id2SymbolMap
  std::unordered_map<std::string_view, RawSymbolId> m_symbol2IdMap;
};

};  // namespace SURELOG

#endif /* SURELOG_SYMBOLTABLE_H */
