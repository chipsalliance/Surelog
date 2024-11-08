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

#include "Surelog/Design/Struct.h"

#include "Surelog/Design/FileContent.h"

// UHDM
#include <uhdm/ref_typespec.h>
#include <uhdm/struct_typespec.h>
#include <uhdm/typespec_member.h>

namespace SURELOG {

Struct::Struct(const FileContent* fC, NodeId nameId, NodeId structId)
    : DataType(fC, structId, fC->SymName(nameId), fC->Type(structId)),
      m_nameId(nameId) {
  m_category = DataType::Category::STRUCT;
}

bool Struct::isNet() const {
  if (!m_typespec) {
    return false;
  }
  if (m_typespec->UhdmType() != UHDM::uhdmstruct_typespec) return false;
  const UHDM::struct_typespec* tps = (const UHDM::struct_typespec*)m_typespec;
  if (tps->Members()) {
    for (UHDM::typespec_member* member : *tps->Members()) {
      if (const UHDM::ref_typespec* rt = member->Typespec()) {
        if (const UHDM::typespec* ag = rt->Actual_typespec()) {
          if (ag->UhdmType() != UHDM::uhdmlogic_typespec) {
            return false;
          }
        } else {
          return false;
        }
      } else {
        return false;
      }
    }
  }
  return true;
}

}  // namespace SURELOG
