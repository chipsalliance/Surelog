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
 * File:   Struct.h
 * Author: alain
 *
 * Created on May 19, 2020, 11:55 AM
 */

#ifndef STRUCT_H
#define STRUCT_H
#include <string>
#include <map>
#include "Design/DataType.h"

namespace UHDM {
  class typespec;
};
namespace SURELOG {

class FileContent;

class Struct : public DataType {
 public:
  Struct(const FileContent* fC, NodeId nameId, NodeId structId);
  ~Struct() override;

  Category getCategory() const final { return Category::STRUCT; }

  void setTypespec(UHDM::typespec* type) { m_typespec = type; }
  UHDM::typespec* getTypespec() const { return m_typespec; }
  NodeId getNameId() { return m_nameId; }
 private:
  NodeId m_nameId;
  UHDM::typespec* m_typespec;
};

};  // namespace SURELOG

#endif /* STRUCT_H */
