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
 * File:   ValuedComponentI.cpp
 * Author: alain
 *
 * Created on May 20, 2019, 21:03 PM
 */

#include <string>
#include "../Expression/ExprBuilder.h"
#include "ValuedComponentI.h"

using namespace SURELOG;

Value* ValuedComponentI::getValue(std::string name) {
  std::map<std::string, Value*>::iterator itr = m_paramMap.find(name);
  if (itr == m_paramMap.end()) {
    if (m_parentScope) {
      return m_parentScope->getValue(name);
    } else
      return NULL;
  } else {
    return (*itr).second;
  }
}

void ValuedComponentI::setValue(std::string name, Value* val,
                                ExprBuilder& exprBuilder) {
  m_paramValues.push_back(val);
  std::map<std::string, Value*>::iterator itr = m_paramMap.find(name);
  if (itr == m_paramMap.end()) {
    m_paramMap.insert(std::make_pair(name, val));
  } else {
    exprBuilder.deleteValue((*itr).second);
    (*itr).second = val;
  }
}
