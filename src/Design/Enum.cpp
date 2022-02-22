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
 * File:   Enum.cpp
 * Author: alain
 *
 * Created on May 19, 2019, 11:55 AM
 */

#include <Surelog/Design/Enum.h>
#include <Surelog/Design/FileContent.h>

namespace SURELOG {
Enum::Enum(const FileContent* fC, NodeId nameId, NodeId baseTypeId)
    : DataType(fC, baseTypeId, fC->SymName(nameId), fC->Type(baseTypeId)),
      m_nameId(nameId),
      m_baseTypespec(nullptr) {
  m_category = DataType::Category::ENUM;
}

Value* Enum::getValue(const std::string& name) const {
  NameValueMap::const_iterator itr = m_values.find(name);
  if (itr == m_values.end()) {
    return nullptr;
  } else {
    return (*itr).second.second;
  }
}
}  // namespace SURELOG
