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
 * File:   Program.cpp
 * Author: alain
 *
 * Created on June 1, 2018, 8:58 PM
 */
#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"
#include "Design/DesignComponent.h"
#include "Program.h"

using namespace SURELOG;

Program::~Program() {}

unsigned int Program::getSize() const {
  NodeId end = m_nodeIds[0];
  NodeId begin = m_fileContents[0]->Child(end);
  unsigned int size = end - begin;
  return size;
}

ClassDefinition* Program::getClassDefinition(const std::string& name) {
  ClassNameClassDefinitionMultiMap::iterator itr =
      m_classDefinitions.find(name);
  if (itr == m_classDefinitions.end()) {
    return NULL;
  } else {
    return (*itr).second;
  }
}
