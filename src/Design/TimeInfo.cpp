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
 * File:   TimeInfo.cpp
 * Author: alain
 *
 * Created on June 8, 2017, 8:27 PM
 */
#include "Surelog/Design/TimeInfo.h"

#include <string>

#include "Surelog/SourceCompile/SymbolTable.h"

using namespace SURELOG;

TimeInfo::Unit TimeInfo::unitFromString(std::string_view s) {
  if (s == "s")
    return Unit::Second;
  else if (s == "ms")
    return Unit::Millisecond;
  else if (s == "us")
    return Unit::Microsecond;
  else if (s == "ns")
    return Unit::Nanosecond;
  else if (s == "ps")
    return Unit::Picosecond;
  else if (s == "fs")
    return Unit::Femtosecond;
  return Unit::Picosecond;
}

uint64_t TimeInfo::femtoSeconds(Unit unit, int value) {
  uint64_t result = value;
  switch (unit) {
    case Unit::Second:
      result *= 1e+15;
      break;
    case Unit::Millisecond:
      result *= 1e+12;
      break;
    case Unit::Microsecond:
      result *= 1e+9;
      break;
    case Unit::Nanosecond:
      result *= 1e+6;
      break;
    case Unit::Picosecond:
      result *= 1e+3;
      break;
    default:
      break;
  }
  return result;
}
