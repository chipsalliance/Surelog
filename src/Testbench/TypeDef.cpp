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
 * File:   TypeDef.cpp
 * Author: alain
 *
 * Created on March 6, 2019, 9:14 PM
 */
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/VObjectTypes.h"
#include "Design/FileContent.h"
#include "TypeDef.h"

using namespace SURELOG;

TypeDef::TypeDef(const FileContent* fC, NodeId id, NodeId the_def,
                 const std::string& name)
    : DataType(fC, id, name, fC->Type(id)), m_the_def(the_def), m_datatype(NULL) {
  m_category = DataType::Category::TYPEDEF;
}

TypeDef::~TypeDef() {}
