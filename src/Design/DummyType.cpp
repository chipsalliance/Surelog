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
 * File:   SimpleType.cpp
 * Author: alain
 *
 * Created on May 19, 2020, 11:55 AM
 */
#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"
#include "Design/DummyType.h"
#include "uhdm.h"
using namespace SURELOG;

DummyType::DummyType(const FileContent* fC, NodeId nameId, NodeId structId)
    : DataType(fC, structId, fC->SymName(nameId), fC->Type(structId)),
      m_nameId(nameId) {
  m_category = DataType::Category::DUMMY;
}

DummyType::~DummyType() {}
