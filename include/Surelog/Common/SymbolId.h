#ifndef SURELOG_SYMBOLID_H
#define SURELOG_SYMBOLID_H
#pragma once

#include <cstdint>
#include <map>
#include <ostream>
#include <set>
#include <string_view>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>

#if !defined(SYMBOLID_DEBUG_ENABLED)
#if defined(DEBUG) || defined(_DEBUG)
#define SYMBOLID_DEBUG_ENABLED 1
#else
#define SYMBOLID_DEBUG_ENABLED 0
#endif
#endif

namespace SURELOG {
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

  operator RawSymbolId() const { return id; }
  operator bool() const { return id != BadRawSymbolId; }

  template <typename U, typename = typename std::enable_if<
                            std::is_integral<U>::value>::type>
  bool operator<(const U &rhs) const {
    return id < rhs;
  }
  template <typename U, typename = typename std::enable_if<
                            std::is_integral<U>::value>::type>
  bool operator<=(const U &rhs) const {
    return id <= rhs;
  }

  template <typename U, typename = typename std::enable_if<
                            std::is_integral<U>::value>::type>
  bool operator>(const U &rhs) const {
    return id > rhs;
  }
  template <typename U, typename = typename std::enable_if<
                            std::is_integral<U>::value>::type>
  bool operator>=(const U &rhs) const {
    return id >= rhs;
  }

// Avoid these comparison operations to prevent implicitly comparing against
// magic constants. Use defined "invalid" values instead of comparing against,
// say 0.
//   template <typename U, typename = typename std::enable_if<
//                             std::is_integral<U>::value>::type>
//   bool operator==(const U &rhs) const {
//     return id == rhs;
//   }
//   template <typename U, typename = typename std::enable_if<
//                             std::is_integral<U>::value>::type>
//   bool operator!=(const U &rhs) const {
//     return id != rhs;
//   }
//
// Don't implement the methematical comparison operators. Use the explicit
// comparators declared below for use with std containers.
//   bool operator<(const SymbolId &rhs) const { return id < rhs.id; }
//   bool operator<=(const SymbolId &rhs) const { return id <= rhs.id; }
// 
//   bool operator>(const SymbolId &rhs) const { return id > rhs.id; }
//   bool operator>=(const SymbolId &rhs) const { return id >= rhs.id; }

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

typedef uint32_t RawNodeId;
inline static constexpr RawNodeId InvalidRawNodeId = 0;  // Max of 28 bits as per cache!
class NodeId final {
 public:
  constexpr NodeId() : NodeId(InvalidRawNodeId) {}
  constexpr explicit NodeId(RawNodeId id) : id(id) {}
  constexpr NodeId(const NodeId &rhs) : id(rhs.id) {}

  operator RawNodeId() const { return id; }
  operator std::size_t() const { return id; }
  operator bool() const { return id != InvalidRawNodeId; }

  bool operator<(const NodeId &rhs) const { return id < rhs.id; }
  bool operator<=(const NodeId &rhs) const { return id <= rhs.id; }

  bool operator>(const NodeId &rhs) const { return id > rhs.id; }
  bool operator>=(const NodeId &rhs) const { return id >= rhs.id; }

  bool operator==(const NodeId &rhs) const { return id == rhs.id; }
  bool operator!=(const NodeId &rhs) const { return id != rhs.id; }

  NodeId operator-(const NodeId &rhs) const { return NodeId(id - rhs.id); }
  NodeId operator+(const NodeId &rhs) const { return NodeId(id + rhs.id); }

  NodeId &operator-=(const NodeId &rhs) { id -= rhs.id; return *this; }
  NodeId &operator+=(const NodeId &rhs) { id += rhs.id; return *this; }

  template <typename U, typename = typename std::enable_if<
                            std::is_integral<U>::value>::type>
  bool operator<(const U &rhs) const { return id < rhs; }
  template <typename U, typename = typename std::enable_if<
                            std::is_integral<U>::value>::type>
  bool operator<=(const U &rhs) const { return id <= rhs; }

  template <typename U, typename = typename std::enable_if<
                            std::is_integral<U>::value>::type>
  bool operator>(const U &rhs) const { return id > rhs; }
  template <typename U, typename = typename std::enable_if<
                            std::is_integral<U>::value>::type>
  bool operator>=(const U &rhs) const { return id >= rhs; }

  template <typename U, typename = typename std::enable_if<
                            std::is_integral<U>::value>::type>
  NodeId operator-(const U &rhs) const { return NodeId(id - rhs); }

  template <typename U, typename = typename std::enable_if<
                            std::is_integral<U>::value>::type>
  NodeId operator+(const U &rhs) const { return NodeId(id + rhs); }

  template <typename U, typename = typename std::enable_if<
                            std::is_integral<U>::value>::type>
  NodeId &operator-=(const U &rhs) { id -= rhs; return *this; }

  template <typename U, typename = typename std::enable_if<
                            std::is_integral<U>::value>::type>
  NodeId &operator+=(const U &rhs) { id += rhs; return *this; }

// Avoid these comparison operations to prevent implicitly comparing against
// magic constants. Use defined "invalid" values instead of comparing against,
// say 0.
//  template <typename U, typename = typename std::enable_if<
//                            std::is_integral<U>::value>::type>
//  bool operator==(const U &rhs) const {
//    return id == rhs;
//  }
//  template <typename U, typename = typename std::enable_if<
//                            std::is_integral<U>::value>::type>
//  bool operator!=(const U &rhs) const {
//    return id != rhs;
//  }

  NodeId &operator++() { ++id; return *this; }
  NodeId operator++(int) { const NodeId rid(id++); return rid; }

  NodeId &operator--() { --id; return *this; }
  NodeId operator--(int) { const NodeId rid(id--); return rid; }

  NodeId &operator=(const NodeId &rhs) {
    if (this != &rhs) {
      id = rhs.id;
    }
    return *this;
  }

  friend std::ostream &operator<<(std::ostream &strm, const NodeId &nodeId);

 private:
  RawNodeId id;
};

inline static constexpr NodeId InvalidNodeId(InvalidRawNodeId);

inline std::ostream &operator<<(std::ostream &strm, const NodeId &nodeId) {
  strm << (RawNodeId)nodeId;
  return strm;
}

struct NodeIdHasher final {
  inline size_t operator()(const NodeId &value) const {
    return std::hash<RawNodeId>()((RawNodeId)value);
  }
};

struct NodeIdEqualityComparer final {
  inline bool operator()(const NodeId &lhs, const NodeId &rhs) const {
    return (lhs == rhs);
  }
};

struct NodeIdLessThanComparer final {
  inline bool operator()(const NodeId &lhs, const NodeId &rhs) const {
    return (lhs < rhs);
  }
};

typedef std::set<NodeId, NodeIdLessThanComparer> NodeIdSet;
typedef std::unordered_set<NodeId, NodeIdHasher, NodeIdEqualityComparer>
    NodeIdUnorderedSet;

}  // namespace SURELOG

#endif  // SURELOG_SYMBOLID_H
