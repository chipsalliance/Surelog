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
 * File:   DefParam.cpp
 * Author: alain
 *
 * Created on January 7, 2018, 8:55 PM
 */

#include "SourceCompile/SymbolTable.h"
#include "Library/Library.h"
#include "Design/FileContent.h"
#include "Design/DefParam.h"

using namespace SURELOG;

std::string DefParam::getFullName() const {
  std::string name;
  std::vector<std::string> chunks;
  const DefParam* parent = this;
  while (parent) {
    chunks.push_back(parent->m_name);
    parent = parent->m_parent;
  }
  name = chunks[chunks.size() - 1];
  for (int i = chunks.size() - 2; i >= 0; i--) {
    name += "." + chunks[i];
  }
  return name;
}
