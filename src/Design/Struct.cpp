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
 * File:   Struct.cpp
 * Author: alain
 *
 * Created on May 19, 2020, 11:55 AM
 */
#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"
#include "Design/Struct.h"
#include "uhdm.h"

using namespace SURELOG;

Struct::Struct(const FileContent* fC, NodeId nameId, NodeId structId)
    : DataType(fC, structId, fC->SymName(nameId), fC->Type(structId)), m_nameId(nameId) {
    m_category = DataType::Category::STRUCT;
}

Struct::~Struct() {}

bool Struct::isNet() {
  if (!m_typespec) {
    return false;
  }
  if (m_typespec->UhdmType() != UHDM::uhdmstruct_typespec) return false;
  const UHDM::struct_typespec* tps = (const UHDM::struct_typespec*)m_typespec;
  if (tps->Members()) {
    for (UHDM::typespec_member* member : *tps->Members()) {
      const UHDM::typespec* tm = member->Typespec();
      if (!tm) return false;
      UHDM::UHDM_OBJECT_TYPE type = tm->UhdmType();
      if (type != UHDM::uhdmlogic_typespec) return false;
    }
  }
  return true;
}
