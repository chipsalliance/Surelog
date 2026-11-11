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
 * File:   LoopCheck.cpp
 * Author: alain
 *
 * Created on May 2, 2017, 8:14 PM
 */

#include "Surelog/SourceCompile/LoopCheck.h"

#include <map>
#include <queue>
#include <vector>

#include "Surelog/Common/SymbolId.h"

namespace SURELOG {

LoopCheck::~LoopCheck() {
  for (const auto& itr : m_nodes) {
    delete itr.second;
  }
}

void LoopCheck::clear() {
  for (const auto& itr : m_nodes) {
    delete itr.second;
  }
  m_nodes.clear();
}

bool LoopCheck::addEdge(SymbolId from, SymbolId to) {
  // Create Graph
  std::map<SymbolId, Node*>::iterator fromIt = m_nodes.find(from);
  std::map<SymbolId, Node*>::iterator toIt = m_nodes.find(to);
  Node* nodeFrom = nullptr;
  Node* nodeTo = nullptr;
  if (fromIt == m_nodes.end()) {
    nodeFrom = new Node(from);
    m_nodes.emplace(from, nodeFrom);
  } else {
    nodeFrom = (*fromIt).second;
  }
  if (toIt == m_nodes.end()) {
    nodeTo = new Node(to);
    m_nodes.emplace(to, nodeTo);
  } else {
    nodeTo = (*toIt).second;
  }
  nodeFrom->m_toList.insert(nodeTo);

  for (auto& itr : m_nodes) {
    itr.second->m_visited = false;
  }

  // The new edge closes a cycle iff `from` is reachable from `to`.  Meeting a
  // node twice is NOT a cycle: two macros of one body that both expand a
  // common macro (`define A `B+`C, `define B `D, `define C `D) reconverge on
  // `D -- a diamond, which is legal and common in generated headers.
  if (nodeTo == nodeFrom) {
    nodeFrom->m_visited = true;
    return true;
  }
  std::queue<Node*> queue;
  queue.push(nodeTo);
  nodeTo->m_visited = true;
  while (!queue.empty()) {
    Node* tmp = queue.front();
    queue.pop();
    for (auto next : tmp->m_toList) {
      if (next == nodeFrom) {
        next->m_visited = true;
        return true;
      }
      if (!next->m_visited) {
        next->m_visited = true;
        queue.push(next);
      }
    }
  }

  return false;
}

std::vector<SymbolId> LoopCheck::reportLoop() const {
  std::vector<SymbolId> loop;
  for (const auto& itr : m_nodes) {
    if (itr.second->m_visited) {
      loop.push_back(itr.first);
    }
  }
  return loop;
}

}  // namespace SURELOG
