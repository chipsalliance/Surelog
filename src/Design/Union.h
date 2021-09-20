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
#include <map>
#include <string>

#include "Design/DataType.h"

namespace SURELOG {

class FileContent;

class Union : public DataType {
  SURELOG_IMPLEMENT_RTTI(Union, DataType)
 public:
  Union(const FileContent* fC, NodeId nameId, NodeId structId);
  ~Union() override;

  NodeId getNameId() const { return m_nameId; }

 private:
  const NodeId m_nameId;
};

};  // namespace SURELOG

#endif /* UNION_H */
