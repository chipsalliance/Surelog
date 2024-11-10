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
#include "Surelog/Design/DataType.h"

/*
 * File:   DataType.cpp
 * Author: alain
 *
 * Created on June 14, 2018, 10:07 PM
 */

#include <string>

#include "Surelog/Expression/Value.h"
#include "Surelog/SourceCompile/VObjectTypes.h"

namespace SURELOG {

const DataType* DataType::getActual() const {
  const DataType* actual = this;
  const DataType* tmp = actual;
  while (tmp) {
    actual = tmp;
    tmp = tmp->getDefinition();
  }
  return actual;
}

bool DataType::isInteger_type(VObjectType type) {
  return (isInteger_vector_type(type) || isInteger_atom_type(type));
}

bool DataType::isInteger_atom_type(VObjectType type) {
  return (type == VObjectType::paIntegerAtomType_Byte ||
          type == VObjectType::paIntegerAtomType_Shortint ||
          type == VObjectType::paIntegerAtomType_Integer ||
          type == VObjectType::paIntegerAtomType_LongInt ||
          type == VObjectType::paIntegerAtomType_Int ||
          type == VObjectType::paIntegerAtomType_Time);
}

bool DataType::isInteger_vector_type(VObjectType type) {
  return (type == VObjectType::paIntVec_TypeBit ||
          type == VObjectType::paIntVec_TypeLogic ||
          type == VObjectType::paIntVec_TypeReg);
}

bool DataType::isNon_integer_type(VObjectType type) {
  return (type == VObjectType::paNonIntType_ShortReal ||
          type == VObjectType::paNonIntType_Real ||
          type == VObjectType::paNonIntType_RealTime);
}

bool DataType::isNet_type(VObjectType type) {
  return (type == VObjectType::paNetType_Supply0 ||
          type == VObjectType::paNetType_Supply1 ||
          type == VObjectType::paNetType_Tri ||
          type == VObjectType::paNetType_TriAnd ||
          type == VObjectType::paNetType_TriOr ||
          type == VObjectType::paNetType_TriReg ||
          type == VObjectType::paNetType_Tri0 ||
          type == VObjectType::paNetType_Tri1 ||
          type == VObjectType::paNetType_Uwire ||
          type == VObjectType::paNetType_Wire ||
          type == VObjectType::paNetType_Wand ||
          type == VObjectType::paNetType_Wor);
}

bool DataType::isData_type(VObjectType type) {
  return (isInteger_vector_type(type) || isInteger_atom_type(type) ||
          isNon_integer_type(type) || type == VObjectType::paString_type ||
          type == VObjectType::paChandle_type ||
          type == VObjectType::paEvent_type ||
          type == VObjectType::paType_reference);
}

bool DataType::isString_type(VObjectType type) {
  return (type == VObjectType::paString_type ||
          type == VObjectType::slStringConst ||
          type == VObjectType::slStringLiteral);
}

bool DataType::isNumber(VObjectType type) {
  return (type == VObjectType::slRealConst ||
          type == VObjectType::paInteger_type ||
          type == VObjectType::paNumber_1Tickb0 ||
          type == VObjectType::paNumber_1Tickb1 ||
          type == VObjectType::paNumber_1TickB0 ||
          type == VObjectType::paNumber_1TickB1 ||
          type == VObjectType::paNumber_Tickb0 ||
          type == VObjectType::paNumber_Tickb1 ||
          type == VObjectType::paNumber_TickB0 ||
          type == VObjectType::paNumber_TickB1 ||
          type == VObjectType::paNumber_Tick0 ||
          type == VObjectType::paNumber_Tick1 ||
          type == VObjectType::paNumber_1Tickbx ||
          type == VObjectType::paNumber_1TickbX ||
          type == VObjectType::paNumber_1TickBx ||
          type == VObjectType::paNumber_1TickBX);
}

bool DataType::isCompatible(const Value* value) const {
  bool result = true;
  VObjectType dtype = getType();
  if (m_definition) {
    dtype = m_definition->getType();
  }
  Value::Type vtype = value->getType();
  if (vtype == Value::Type::String) {
    std::string st = value->getValueS();
    if (st.size() == 3)  // "\"c\""
    {
      result = false;
      if (isString_type(dtype) || isInteger_atom_type(dtype)) result = true;
    } else if (!isString_type(dtype)) {
      result = false;
    }
  } else if (vtype == Value::Type::Double) {
    if (isString_type(dtype)) result = false;
  } else if (vtype == Value::Type::Unsigned) {
    if (value->getValueL(0) == 0) {
      // Null
    } else {
      if (isString_type(dtype)) result = false;
    }
  } else {
    if (isString_type(dtype)) result = false;
  }
  return result;
}
}  // namespace SURELOG
