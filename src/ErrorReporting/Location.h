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

#ifndef LOCATION_H
#define LOCATION_H

#include "SourceCompile/SymbolTable.h"

namespace SURELOG {

class Location {
 public:
  Location(SymbolId object)
      : m_fileId(0), m_line(0), m_column(0), m_object(object){};
  Location(SymbolId fileId, unsigned int line, unsigned short int column,
           SymbolId object = 0)
      : m_fileId(fileId), m_line(line), m_column(column), m_object(object){};
  /* Do not create a copy constructor, use default*/
  // Location(const Location& orig);
  bool operator==(const Location& rhs) const;
  bool operator<(const Location& rhs) const;
  virtual ~Location();
  SymbolId m_fileId;
  unsigned int m_line;
  unsigned short int m_column;
  SymbolId m_object;

 private:
};

};  // namespace SURELOG

#endif /* LOCATION_H */
