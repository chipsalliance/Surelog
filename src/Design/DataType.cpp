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
 * File:   DataType.cpp
 * Author: alain
 *
 * Created on June 14, 2018, 10:07 PM
 */

#include <Surelog/Design/DataType.h>
#include <Surelog/Expression/Value.h>

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
  return (type == VObjectType::slIntegerAtomType_Byte ||
          type == VObjectType::slIntegerAtomType_Shortint ||
          type == VObjectType::slIntegerAtomType_Integer ||
          type == VObjectType::slIntegerAtomType_LongInt ||
          type == VObjectType::slIntegerAtomType_Int ||
          type == VObjectType::slIntegerAtomType_Time);
}

bool DataType::isInteger_vector_type(VObjectType type) {
  return (type == VObjectType::slIntVec_TypeBit ||
          type == VObjectType::slIntVec_TypeLogic ||
          type == VObjectType::slIntVec_TypeReg);
}

bool DataType::isNon_integer_type(VObjectType type) {
  return (type == VObjectType::slNonIntType_ShortReal ||
          type == VObjectType::slNonIntType_Real ||
          type == VObjectType::slNonIntType_RealTime);
}

bool DataType::isNet_type(VObjectType type) {
  return (type == VObjectType::slNetType_Supply0 ||
          type == VObjectType::slNetType_Supply1 ||
          type == VObjectType::slNetType_Tri ||
          type == VObjectType::slNetType_TriAnd ||
          type == VObjectType::slNetType_TriOr ||
          type == VObjectType::slNetType_TriReg ||
          type == VObjectType::slNetType_Tri0 ||
          type == VObjectType::slNetType_Tri1 ||
          type == VObjectType::slNetType_Uwire ||
          type == VObjectType::slNetType_Wire ||
          type == VObjectType::slNetType_Wand ||
          type == VObjectType::slNetType_Wor);
}

bool DataType::isData_type(VObjectType type) {
  return (isInteger_vector_type(type) || isInteger_atom_type(type) ||
          isNon_integer_type(type) || type == VObjectType::slString_type ||
          type == VObjectType::slChandle_type ||
          type == VObjectType::slEvent_type ||
          type == VObjectType::slType_reference);
}

bool DataType::isString_type(VObjectType type) {
  return (type == VObjectType::slString_type ||
          type == VObjectType::slStringConst ||
          type == VObjectType::slStringLiteral);
}

bool DataType::isNumber(VObjectType type) {
  return (type == VObjectType::slRealConst ||
          type == VObjectType::slInteger_type ||
          type == VObjectType::slNumber_1Tickb0 ||
          type == VObjectType::slNumber_1Tickb1 ||
          type == VObjectType::slNumber_1TickB0 ||
          type == VObjectType::slNumber_1TickB1 ||
          type == VObjectType::slNumber_Tickb0 ||
          type == VObjectType::slNumber_Tickb1 ||
          type == VObjectType::slNumber_TickB0 ||
          type == VObjectType::slNumber_TickB1 ||
          type == VObjectType::slNumber_Tick0 ||
          type == VObjectType::slNumber_Tick1 ||
          type == VObjectType::slNumber_1Tickbx ||
          type == VObjectType::slNumber_1TickbX ||
          type == VObjectType::slNumber_1TickBx ||
          type == VObjectType::slNumber_1TickBX);
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
