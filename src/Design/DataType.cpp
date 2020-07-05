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
#include "Design/DataType.h"

#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"
#include "Expression/Value.h"

using namespace SURELOG;

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
  return (type == slIntegerAtomType_Byte ||
          type == slIntegerAtomType_Shortint ||
          type == slIntegerAtomType_Int || type == slIntegerAtomType_LongInt ||
          type == slIntegerAtomType_Int || type == slIntegerAtomType_Time);
}

bool DataType::isInteger_vector_type(VObjectType type) {
  return (type == slIntVec_TypeBit || type == slIntVec_TypeLogic ||
          type == slIntVec_TypeReg);
}

bool DataType::isNon_integer_type(VObjectType type) {
  return (type == slNonIntType_ShortReal || type == slNonIntType_Real ||
          type == slNonIntType_RealTime);
}

bool DataType::isNet_type(VObjectType type) {
  return (type == slNetType_Supply0 || type == slNetType_Supply1 ||
          type == slNetType_Tri || type == slNetType_TriAnd ||
          type == slNetType_TriOr || type == slNetType_TriReg ||
          type == slNetType_Tri0 || type == slNetType_Tri1 ||
          type == slNetType_Uwire || type == slNetType_Wire ||
          type == slNetType_Wand || type == slNetType_Wor);
}

bool DataType::isData_type(VObjectType type) {
  return (isInteger_vector_type(type) || isInteger_atom_type(type) ||
          isNon_integer_type(type) || type == slString_type ||
          type == slChandle_type || type == slEvent_type ||
          type == slType_reference);
}

bool DataType::isString_type(VObjectType type) {
  return (type == slString_type || type == slStringConst ||
          type == slStringLiteral);
}

bool DataType::isNumber(VObjectType type) {
  return (type == VObjectType::slRealConst ||
          type == VObjectType::slInteger_type ||
          type == slNumber_1Tickb0 || type == slNumber_1Tickb1 ||
          type == slNumber_1TickB0 || type == slNumber_1TickB1 ||
          type == slNumber_Tickb0 || type == slNumber_Tickb1 ||
          type == slNumber_TickB0 || type == slNumber_TickB1 ||
          type == slNumber_Tick0 || type == slNumber_Tick1 ||
          type == slNumber_1Tickbx || type == slNumber_1TickbX ||
          type == slNumber_1TickBx || type == slNumber_1TickBX);
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
