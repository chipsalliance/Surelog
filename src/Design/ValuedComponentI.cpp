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
#include "Expression/ExprBuilder.h"
#include "Design/ValuedComponentI.h"

using namespace SURELOG;

Value* ValuedComponentI::getValue(const std::string& name) const {
  auto itr = m_paramMap.find(name);
  if (itr == m_paramMap.end()) {
    if (m_definition) {
      itr = m_definition->m_paramMap.find(name);
      if (itr != m_definition->m_paramMap.end()) {
        return (*itr).second.first;
      }
    }

    if (m_parentScope) {
      return m_parentScope->getValue(name);
    } else
      return NULL;
  } else {
    return (*itr).second.first;
  }
}

void ValuedComponentI::deleteValue(const std::string& name, ExprBuilder& exprBuilder) {
  std::map<std::string, std::pair<Value*, int>>::iterator itr = m_paramMap.find(name);
  if (itr != m_paramMap.end()) {
    exprBuilder.deleteValue((*itr).second.first);
    m_paramMap.erase(itr);
  }
}

void ValuedComponentI::setValue(const std::string& name, Value* val,
                                ExprBuilder& exprBuilder, int lineNb) {
  m_paramValues.push_back(val);
  deleteValue(name, exprBuilder);
  m_paramMap.insert(std::make_pair(name, std::make_pair(val, lineNb)));
}
