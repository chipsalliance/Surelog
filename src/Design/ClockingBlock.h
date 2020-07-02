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
 * File:   ClockingBlock.h
 * Author: alain
 *
 * Created on May 26, 2018, 11:07 AM
 */

#ifndef CLOCKINGBLOCK_H
#define CLOCKINGBLOCK_H

#include <vector>

namespace SURELOG {

class ClockingBlock final {
 public:
  ClockingBlock(const FileContent* fileContent, NodeId blockId,
                NodeId clockingBlockId)
    : m_fileContent(fileContent),
      m_blockId(blockId),
      m_clockingBlockId(clockingBlockId) {}

  void addSignal(Signal& signal) { m_signals.push_back(signal); }
  NodeId getNodeId() const { return m_blockId; }
  const std::vector<Signal>& getAllSignals() const { return m_signals; }

 private:
  const FileContent* m_fileContent;
  NodeId m_blockId;
  NodeId m_clockingBlockId;
  std::vector<Signal> m_signals;
};

}  // namespace SURELOG

#endif /* CLOCKINGBLOCK_H */
