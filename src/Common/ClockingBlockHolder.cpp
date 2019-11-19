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
 * File:   ClockingBlockHolder.cpp
 * Author: alain
 *
 * Created on June 1, 2018, 9:08 PM
 */

#include "Common/ClockingBlockHolder.h"

using namespace SURELOG;

void ClockingBlockHolder::addClockingBlock(SymbolId blockId,
                                           ClockingBlock& block) {
  m_clockingBlockMap.insert(std::make_pair(blockId, block));
}

ClockingBlock* ClockingBlockHolder::getClockingBlock(SymbolId blockId) {
  ClockingBlockMap::iterator itr = m_clockingBlockMap.find(blockId);
  if (itr != m_clockingBlockMap.end()) {
    return &(*itr).second;
  } else {
    return NULL;
  }
}
