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
#include "SourceCompile/LoopCheck.h"

#include <queue>

using namespace SURELOG;

LoopCheck::LoopCheck() {}

LoopCheck::~LoopCheck() {
  for (auto itr : m_nodes) {
    delete itr.second;
  }
}

void LoopCheck::clear() {
  for (auto itr : m_nodes) {
    delete itr.second;
  }
  m_nodes.clear();
}

bool LoopCheck::addEdge(SymbolId from, SymbolId to) {
  // Create Graph
  std::map<SymbolId, Node*>::iterator fromIt = m_nodes.find(from);
  std::map<SymbolId, Node*>::iterator toIt = m_nodes.find(to);
  Node* nodeFrom = NULL;
  Node* nodeTo = NULL;
  if (fromIt == m_nodes.end()) {
    nodeFrom = new Node(from);
    m_nodes.insert(std::make_pair(from, nodeFrom));
  } else {
    nodeFrom = (*fromIt).second;
  }
  if (toIt == m_nodes.end()) {
    nodeTo = new Node(to);
    m_nodes.insert(std::make_pair(to, nodeTo));
  } else {
    nodeTo = (*toIt).second;
  }
  nodeFrom->m_toList.insert(nodeTo);

  for (auto &itr : m_nodes) {
    itr.second->m_visited = false;
  }

  // BFS
  std::queue<Node*> queue;
  queue.push(nodeTo);
  nodeTo->m_visited = true;
  while (!queue.empty()) {
    Node* tmp = queue.front();
    queue.pop();
    tmp->m_visited = true;
    for (auto next : tmp->m_toList) {
      if (next->m_visited)
        return true;
      else {
        queue.push(next);
      }
    }
  }

  return false;
}

std::vector<SymbolId> LoopCheck::reportLoop() const {
  std::vector<SymbolId> loop;
  for (const auto &itr : m_nodes) {
    if (itr.second->m_visited) {
      loop.push_back(itr.first);
    }
  }
  return loop;
}
