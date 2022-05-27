#ifndef SURELOG_SYMBOLID_H
#define SURELOG_SYMBOLID_H
#pragma once

#include <cstdint>
#include <ostream>
#include <set>
#include <string_view>
#include <unordered_set>

#if !defined(SYMBOLID_DEBUG_ENABLED)
#if defined(DEBUG) || defined(_DEBUG)
#define SYMBOLID_DEBUG_ENABLED 1
#else
#define SYMBOLID_DEBUG_ENABLED 0
#endif
#endif

namespace SURELOG {
/**
 * class SymbolId
 *
 * Used to uniquely represent a string in SymbolTable. SymbolId can (and
 * should) be resolved only with the SymbolTable that it was generated with.
 * 
 */
typedef uint64_t RawSymbolId;
inline static constexpr RawSymbolId BadRawSymbolId = 0;
inline static constexpr std::string_view BadRawSymbol = "@@BAD_SYMBOL@@";
class SymbolId final {
 public:
#if SYMBOLID_DEBUG_ENABLED
  SymbolId() : id(BadRawSymbolId), value(BadRawSymbol) {}
  SymbolId(RawSymbolId id, std::string_view value)
      : id(id)
      , value(value)
  {
  }
#else
  SymbolId() : id(BadRawSymbolId) {}
  explicit SymbolId(RawSymbolId id) : id(id) {}
  SymbolId(RawSymbolId id, std::string_view value) : id(id) {}
#endif

  SymbolId(const SymbolId &rhs)
      : id(rhs.id)
#if SYMBOLID_DEBUG_ENABLED
      , value(rhs.value)
#endif
  {
  }

  SymbolId &operator=(const SymbolId &rhs) {
    if (this != &rhs) {
      id = rhs.id;
#if SYMBOLID_DEBUG_ENABLED
      value = rhs.value;
#endif
    }
    return *this;
  }

  explicit operator RawSymbolId() const { return id; }
  explicit operator bool() const { return id != BadRawSymbolId; }

  bool operator==(const SymbolId &rhs) const { return id == rhs.id; }
  bool operator!=(const SymbolId &rhs) const { return id != rhs.id; }

 private:
  RawSymbolId id;
#if SYMBOLID_DEBUG_ENABLED
  std::string_view value;
#endif

  friend std::ostream &operator<<(std::ostream &strm, const SymbolId &symbolId);
};

inline static const SymbolId BadSymbolId(BadRawSymbolId, BadRawSymbol);

inline std::ostream &operator<<(std::ostream &strm, const SymbolId &symbolId) {
  strm << (RawSymbolId)symbolId;
  return strm;
}

struct SymbolIdHasher final {
  inline size_t operator()(const SymbolId &value) const {
    return std::hash<RawSymbolId>()((RawSymbolId)value);
  }
};

struct SymbolIdEqualityComparer final {
  inline bool operator()(const SymbolId &lhs, const SymbolId &rhs) const {
    return (lhs == rhs);
  }
};

struct SymbolIdLessThanComparer final {
  inline bool operator()(const SymbolId &lhs, const SymbolId &rhs) const {
    return ((RawSymbolId)lhs < (RawSymbolId)rhs);
  }
};

typedef std::set<SymbolId, SymbolIdLessThanComparer> SymbolIdSet;
typedef std::unordered_set<SymbolId, SymbolIdHasher, SymbolIdEqualityComparer>
    SymbolIdUnorderedSet;

}  // namespace SURELOG

#endif  // SURELOG_SYMBOLID_H
