/*
 Copyright 2020 Alain Dargelas

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
 * File:   Union.h
 * Author: alain
 *
 * Created on May 19, 2020, 11:55 AM
 */

#ifndef UNION_H
#define UNION_H
#include <string>
#include <map>
#include "Design/DataType.h"

namespace UHDM {
  class typespec;
};
namespace SURELOG {

class FileContent;

class Union : public DataType {
 public:
  Union(const FileContent* fC, NodeId nameId, NodeId structId);
  ~Union() override;

  Category getCategory() const final { return Category::UNION; }

  void setTypespec(UHDM::typespec* type) { m_typespec = type; }
  UHDM::typespec* getTypespec() const { return m_typespec; }
  NodeId getNameId() const { return m_nameId; }

 private:
  NodeId m_nameId;
  UHDM::typespec* m_typespec;
};

};  // namespace SURELOG

#endif /* UNION_H */
