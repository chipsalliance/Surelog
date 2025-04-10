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
 * File:   LoopCheck.h
 * Author: alain
 *
 * Created on May 2, 2017, 8:14 PM
 */

#ifndef SURELOG_LOOPCHECK_H
#define SURELOG_LOOPCHECK_H
#pragma once

#include <Surelog/Common/SymbolId.h>

#include <map>
#include <set>
#include <vector>

namespace SURELOG {

class LoopCheck {
 public:
  LoopCheck() = default;
  LoopCheck(const LoopCheck& orig) = delete;
  ~LoopCheck();

  void clear();

  // return true if new edge creates a loop
  bool addEdge(SymbolId from, SymbolId to);

  std::vector<SymbolId> reportLoop() const;

 private:
  class Node {
   public:
    explicit Node(SymbolId objId) : m_objId(objId), m_visited(false) {}
    const SymbolId m_objId;
    std::set<Node*> m_toList;
    bool m_visited;
  };

  std::map<SymbolId, Node*, SymbolIdLessThanComparer> m_nodes;
};
}  // namespace SURELOG

#endif /* SURELOG_LOOPCHECK_H */
