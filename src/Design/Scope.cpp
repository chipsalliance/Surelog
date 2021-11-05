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
 * File:   Scope.cpp
 * Author: alain
 *
 * Created on August 31, 2019, 11:24 AM
 */

#include "Design/Scope.h"

using namespace SURELOG;

Variable* Scope::getVariable(std::string_view name) const {
  auto itr = m_variables.find(name);
  if (itr == m_variables.end()) {
    if (m_parentScope) {
      Variable* var = m_parentScope->getVariable(name);
      if (var) return var;
    }
    return NULL;
  } else {
    return (*itr).second;
  }
}

DataType* Scope::getUsedDataType(std::string_view name) const {
  auto itr = m_usedDataTypes.find(name);
  if (itr == m_usedDataTypes.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}
