#ifndef SURELOG_PATHID_H
#define SURELOG_PATHID_H
#pragma once

#include <Surelog/Common/SymbolId.h>

#include <cstdint>
#include <filesystem>
#include <istream>
#include <ostream>
#include <set>
#include <string_view>
#include <unordered_set>
#include <vector>

#if !defined(PATHID_DEBUG_ENABLED)
#if defined(DEBUG) || defined(_DEBUG)
#define PATHID_DEBUG_ENABLED 1
#else
#define PATHID_DEBUG_ENABLED 0
#endif
#endif

namespace SURELOG {
typedef uint32_t RawPathId;
inline static constexpr RawPathId BadRawPathId = 0;
inline static constexpr std::string_view BadRawPath = BadRawSymbol;

class SymbolTable;

class PathId final {
 public:
#if PATHID_DEBUG_ENABLED
  PathId()
      : m_symbolTable(nullptr), m_id(BadRawPathId), m_value(BadRawPath) {}
  PathId(const SymbolTable *const symbolTable, RawPathId id,
         std::string_view value)
      : m_symbolTable(symbolTable), m_id(id), m_value(value) {}
  PathId(const PathId &rhs)
      : PathId(rhs.m_symbolTable, rhs.m_id, rhs.m_value) {}
  PathId(const SymbolTable *const symbolTable, SymbolId id)
      : PathId(symbolTable, id.id, id.value) {}
#else
  PathId() : m_symbolTable(nullptr), m_id(BadRawPathId) {}
  PathId(const SymbolTable *const symbolTable, RawPathId id,
         std::string_view value)
      : m_symbolTable(symbolTable), m_id(id) {}
  PathId(const PathId &rhs)
      : PathId(rhs.m_symbolTable, rhs.m_id, BadRawPath) {}
  PathId(const SymbolTable *const symbolTable, SymbolId id)
      : PathId(symbolTable, id.id, BadRawPath) {}
#endif

  PathId &operator=(const PathId &rhs) {
    if (this != &rhs) {
      m_symbolTable = rhs.m_symbolTable;
      m_id = rhs.m_id;
#if PATHID_DEBUG_ENABLED
      m_value = rhs.m_value;
#endif
    }
    return *this;
  }

  const SymbolTable *getSymbolTable() const { return m_symbolTable; }

  explicit operator RawPathId() const { return m_id; }
  explicit operator bool() const { return m_id != BadRawPathId; }
#if PATHID_DEBUG_ENABLED
  explicit operator SymbolId() const { return SymbolId(m_id, m_value); }
#else
  explicit operator SymbolId() const { return SymbolId(m_id, BadRawPath); }
#endif

  bool operator==(const PathId &rhs) const;
  bool operator!=(const PathId &rhs) const { return !operator==(rhs); }

 private:
  const SymbolTable *m_symbolTable = nullptr;
  RawPathId m_id = BadRawPathId;
#if PATHID_DEBUG_ENABLED
  std::string_view m_value;
#endif

  friend class SymbolId;
  friend std::istream &operator>>(std::istream &strm, PathId &pathId);
  friend std::ostream &operator<<(std::ostream &strm, const PathId &pathId);
};

inline static const PathId BadPathId(nullptr, BadRawPathId, BadRawPath);

inline SymbolId::SymbolId(const PathId &rhs)
#if SYMBOLID_DEBUG_ENABLED
    : id(rhs.m_id), value(rhs.m_value) {}
#else
    : id(rhs.m_id) {}
#endif

inline std::istream &operator>>(std::istream &strm, PathId &pathId) {
  return strm >> pathId.m_id;
}

inline std::ostream &operator<<(std::ostream &strm, const PathId &pathId) {
  return strm << pathId.m_id;
}

struct PathIdPP final { // Pretty Printer
  const PathId &m_id;

  PathIdPP(const PathId &id) : m_id(id) {}
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

typedef std::set<PathId, PathIdLessThanComparer> PathIdSet;
typedef std::unordered_set<PathId, PathIdHasher, PathIdEqualityComparer>
    PathIdUnorderedSet;
typedef std::vector<PathId> PathIdVector;

}  // namespace SURELOG

#endif  // SURELOG_PATHID_H
