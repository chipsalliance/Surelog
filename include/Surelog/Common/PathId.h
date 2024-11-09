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

#ifndef SURELOG_PATHID_H
#define SURELOG_PATHID_H
#pragma once

#include <Surelog/Common/SymbolId.h>

#include <cstdint>
#include <istream>
#include <set>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "Surelog/config.h"

namespace SURELOG {
/**
 * class PathId
 *
 * Used to uniquely represent a file or directory abstractly.
 * The context/value doesn't have to be a std::filesystem::path but
 * can be any printable (i.e. convertible to string) value. This pinned
 * value is stored in the PathId::m_symbolTable.
 *
 * All operations on/with PathId has to go through the SURELOG::FileSystem.
 * Logic in Surelog (or client application) shouldn't access/alter the value
 * of it outside of the SURELOG::FileSystem context.
 *
 */
using RawPathId = uint32_t;
inline static constexpr RawPathId BadRawPathId = 0;
inline static constexpr std::string_view BadRawPath = BadRawSymbol;

class SymbolTable;

class PathId final {
 public:
#if SURELOG_PATHID_DEBUG_ENABLED
  PathId() : m_symbolTable(nullptr), m_id(BadRawPathId), m_value(BadRawPath) {}
  PathId(const SymbolTable *const symbolTable, RawPathId id,
         std::string_view value)
      : m_symbolTable(symbolTable), m_id(id), m_value(value) {}
  PathId(const PathId &rhs)
      : PathId(rhs.m_symbolTable, rhs.m_id, rhs.m_value) {}
  PathId(const SymbolTable *const symbolTable, SymbolId id)
      : PathId(symbolTable, (RawSymbolId)id, (std::string_view)id) {}
#else
  PathId() : m_symbolTable(nullptr), m_id(BadRawPathId) {}
  PathId(const SymbolTable *const symbolTable, RawPathId id,
         std::string_view value)
      : m_symbolTable(symbolTable), m_id(id) {}
  PathId(const PathId &rhs) : PathId(rhs.m_symbolTable, rhs.m_id, BadRawPath) {}
  PathId(const SymbolTable *const symbolTable, SymbolId id)
      : PathId(symbolTable, (RawSymbolId)id, BadRawPath) {}
#endif

  PathId &operator=(const PathId &rhs) {
    if (this != &rhs) {
      m_symbolTable = rhs.m_symbolTable;
      m_id = rhs.m_id;
#if SURELOG_PATHID_DEBUG_ENABLED
      m_value = rhs.m_value;
#endif
    }
    return *this;
  }

  const SymbolTable *getSymbolTable() const { return m_symbolTable; }

  explicit operator RawPathId() const { return m_id; }
  explicit operator bool() const { return m_id != BadRawPathId; }
#if SURELOG_PATHID_DEBUG_ENABLED
  explicit operator SymbolId() const { return SymbolId(m_id, m_value); }
#else
  explicit operator SymbolId() const { return SymbolId(m_id, BadRawPath); }
#endif

  bool operator==(const PathId &rhs) const;
  bool operator!=(const PathId &rhs) const { return !operator==(rhs); }

 private:
  const SymbolTable *m_symbolTable = nullptr;
  RawPathId m_id = BadRawPathId;
#if SURELOG_PATHID_DEBUG_ENABLED
  std::string_view m_value;
#endif

  friend std::istream &operator>>(std::istream &strm, PathId &pathId);
  friend std::ostream &operator<<(std::ostream &strm, const PathId &pathId);
};

inline static const PathId BadPathId(nullptr, BadRawPathId, BadRawPath);

inline std::istream &operator>>(std::istream &strm, PathId &pathId) {
  return strm >> pathId.m_id;
}

inline std::ostream &operator<<(std::ostream &strm, const PathId &pathId) {
  return strm << pathId.m_id;
}

struct PathIdPP final {  // Pretty Printer
  const PathId &m_id;

  explicit PathIdPP(const PathId &id) : m_id(id) {}
};

std::ostream &operator<<(std::ostream &strm, const PathIdPP &id);

struct PathIdHasher final {
  inline size_t operator()(const PathId &value) const {
    return std::hash<RawPathId>()((RawPathId)value);
  }
};

struct PathIdEqualityComparer final {
  inline bool operator()(const PathId &lhs, const PathId &rhs) const {
    return (lhs == rhs);
  }
};

struct PathIdLessThanComparer final {
  inline bool operator()(const PathId &lhs, const PathId &rhs) const {
    return ((RawPathId)lhs < (RawPathId)rhs);
  }
};

using PathIdSet = std::set<PathId, PathIdLessThanComparer>;
using PathIdUnorderedSet =
    std::unordered_set<PathId, PathIdHasher, PathIdEqualityComparer>;
using PathIdVector = std::vector<PathId>;

}  // namespace SURELOG

#endif  // SURELOG_PATHID_H
