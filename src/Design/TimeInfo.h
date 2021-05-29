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
 * File:   TimeInfo.h
 * Author: alain
 *
 * Created on June 8, 2017, 8:27 PM
 */

#ifndef TIMEINFO_H
#define TIMEINFO_H

#include <string_view>

#include "SourceCompile/SymbolTable.h"

namespace SURELOG {

class TimeInfo final {
 public:
  enum class Type { None, Timescale, TimeUnitTimePrecision };
  enum class Unit {
    Second,
    Millisecond,
    Microsecond,
    Nanosecond,
    Picosecond,
    Femtosecond
  };

  Type m_type = Type::None;
  SymbolId m_fileId = 0;
  unsigned int m_line = 0;
  Unit m_timeUnit = Unit::Second;
  double m_timeUnitValue = 0.0;
  Unit m_timePrecision = Unit::Second;
  double m_timePrecisionValue = 0.0;

  static Unit unitFromString(std::string_view s);
  static uint64_t femtoSeconds(Unit unit, int value);
};

}  // namespace SURELOG

#endif /* TIMEINFO_H */
