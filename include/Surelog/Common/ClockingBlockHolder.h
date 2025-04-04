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
 * File:   ClockingBlockHolder.h
 * Author: alain
 *
 * Created on June 1, 2018, 9:08 PM
 */

#ifndef SURELOG_CLOCKINGBLOCKHOLDER_H
#define SURELOG_CLOCKINGBLOCKHOLDER_H
#pragma once

#include <Surelog/Common/SymbolId.h>
#include <Surelog/Design/ClockingBlock.h>

#include <map>

namespace SURELOG {

class ClockingBlockHolder {
 public:
  using ClockingBlockMap =
      std::multimap<SymbolId, ClockingBlock, SymbolIdLessThanComparer>;

  virtual ~ClockingBlockHolder() = default;  // virtual as used as interface

  ClockingBlockMap& getClockingBlockMap() { return m_clockingBlockMap; }
  void addClockingBlock(SymbolId blockId, ClockingBlock& block);
  ClockingBlock* getClockingBlock(SymbolId blockId);

 private:
  ClockingBlockMap m_clockingBlockMap;
};

};  // namespace SURELOG

#endif /* SURELOG_CLOCKINGBLOCKHOLDER_H */
