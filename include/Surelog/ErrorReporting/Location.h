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
 * File:   Location.h
 * Author: alain
 *
 * Created on March 6, 2017, 6:48 PM
 */

#ifndef SURELOG_LOCATION_H
#define SURELOG_LOCATION_H
#pragma once

#include <Surelog/Common/PathId.h>
#include <Surelog/Common/SymbolId.h>

#include <ostream>

namespace SURELOG {

class Location final {
 public:
  explicit Location(SymbolId object)
      : m_fileId(BadPathId), m_line(0), m_column(0), m_object(object) {}
  explicit Location(PathId fileId) : Location((SymbolId)fileId) {}
  Location(PathId fileId, uint32_t line, uint16_t column,
           SymbolId object = BadSymbolId)
      : m_fileId(fileId), m_line(line), m_column(column), m_object(object) {}

  /* Do not create a copy constructor, use default */
  // Location(const Location& orig);

  bool operator==(const Location& rhs) const;
  bool operator<(const Location& rhs) const;
  friend std::ostream& operator<<(std::ostream& strm, const Location& location);

  PathId m_fileId;
  uint32_t m_line;
  uint16_t m_column;
  SymbolId m_object;
};

};  // namespace SURELOG

#endif /* SURELOG_LOCATION_H */
