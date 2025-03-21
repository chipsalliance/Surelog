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
 * File:   ClassObject.cpp
 * Author: alain
 *
 * Created on March 24, 2019, 7:38 PM
 */

#include "Surelog/Testbench/ClassObject.h"

#include <string_view>
#include <utility>

#include "Surelog/Testbench/ClassDefinition.h"

namespace SURELOG {

bool ClassObject::setValue(std::string_view property, Value* value) {
  PropertyValueMap::iterator itr = m_properties.find(property);
  if (itr == m_properties.end()) {
    Property* prop = m_class->getProperty(property);
    if (prop == nullptr) {
      return false;
    }
    m_properties.emplace(property, std::make_pair(prop, value));
  } else {
    (*itr).second.second = value;
  }
  return true;
}

Value* ClassObject::getValue(std::string_view property) const {
  auto found = m_properties.find(property);
  return found == m_properties.end() ? nullptr : found->second.second;
}

}  // namespace SURELOG
