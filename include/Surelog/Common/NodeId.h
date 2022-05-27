#ifndef SURELOG_NODEID_H
#define SURELOG_NODEID_H
#pragma once

#include <cstdint>
#include <ostream>
#include <set>
#include <unordered_set>

namespace SURELOG {
/**
 * class NodeId
 *
 * Used as an index into the collection representing the AST tree,
 * currently owned by FileContent.
 *
 */
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

#endif  // SURELOG_NODEID_H
