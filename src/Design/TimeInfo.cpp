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
#include <string>
#include "SourceCompile/SymbolTable.h"
#include "Design/TimeInfo.h"

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
