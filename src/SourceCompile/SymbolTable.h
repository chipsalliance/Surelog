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

#ifndef SYMBOLTABLE_H
#define SYMBOLTABLE_H

#include <stdint.h>

#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace SURELOG {

typedef uint64_t SymbolId;

typedef uint32_t NodeId;

static constexpr NodeId InvalidNodeId = 969696;

class SymbolTable {
 public:
  SymbolTable();
  ~SymbolTable();

  // Unfortunately, currently the copy constructor is used in a few places.
  SymbolTable(const SymbolTable&) = default;

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
  // This is an expensive operation as all strings are copied into the vector,
  // but right now, this is only used in the Cache layer.
  // TODO: fix cache layer to deal with vector of string_views; this needs
  // to be upstream fixed in flatbuffers (CreateVectorOfStrings() needs to
  // accept a vector of string_views).
  std::vector<std::string> getSymbols() const;

  static const std::string& getBadSymbol();
  static SymbolId getBadId() { return 0; }
  static const std::string& getEmptyMacroMarker();

 private:
  SymbolId m_idCounter;

  // Stable allocated strings that don't change with vector reallocations.
  //
  // Unfortunately, since we have a copy-constructor, we also need to keep
  // track of number of references, so we use the undesirable std::shared_ptr
  // here; luckily we only need to worry about reference counting peformance
  // on copy or realloc.
  //
  // On the plus side, now symbol strings are even stable between copies of
  // symbol tables.
  // TODO: change the whole system to actually deal with absl::string_view
  // being returned as symbols, then have a block backing buffer here.
  std::vector<std::shared_ptr<std::string>> m_id2SymbolMap;

  // The key string_views point to the stable backing buffer provided in
  // m_id2SymbolMap
  std::unordered_map<std::string_view, SymbolId> m_symbol2IdMap;
};

};  // namespace SURELOG

#endif /* SYMBOLTABLE_H */
