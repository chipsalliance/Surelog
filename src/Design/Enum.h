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
 * File:   Enum.h
 * Author: alain
 *
 * Created on May 19, 2019, 11:55 AM
 */

#ifndef ENUM_H
#define ENUM_H
#include <string>
#include <map>
#include "Design/DataType.h"

namespace SURELOG {

class Value;
class FileContent;

class Enum : public DataType {
 public:
  Enum(std::string name, FileContent* fC, NodeId nodeId, VObjectType baseType);
  void addValue(std::string& name, Value* value) {
    m_values.insert(std::make_pair(name, value));
  }
  Value* getValue(std::string& name);
  VObjectType getBaseType() { return m_baseType; }
  typedef std::map<std::string, Value*> NameValueMap;

  virtual ~Enum();

 private:
  NameValueMap m_values;
  VObjectType m_baseType;
};

};  // namespace SURELOG

#endif /* ENUM_H */
