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
 * File:   Value.cpp
 * Author: alain
 *
 * Created on October 29, 2017, 10:33 PM
 */
#include <string>
#include <cmath>
#include <cstdint>
#include <cstring>
#include "Expression/Value.h"
#include <math.h>    
#include "vpi_user.h"
using namespace SURELOG;

unsigned int Value::nbWords_(unsigned int size) {
  uint64_t nb = size / 64;
  if ((nb * 64) != size) nb++;
  return nb;
}

SValue::~SValue() {}

LValue::~LValue() { delete[] m_valueArray; }

StValue::~StValue() {}

bool LValue::operator<(const Value& rhs) const {
  if (!isValid() || !rhs.isValid()) return false;
  switch (m_type) {
    case Value::Type::Integer:
      for (unsigned int i = 0; i < m_nbWords; i++) {
        if (getValueL(i) >= rhs.getValueL(i)) return false;
      }
      break;
    case Value::Type::Double:
      for (unsigned int i = 0; i < m_nbWords; i++) {
        if (getValueD(i) >= rhs.getValueD(i)) return false;
      }
      break;
    default:
      for (unsigned int i = 0; i < m_nbWords; i++) {
        if (getValueUL(i) >= rhs.getValueUL(i)) return false;
      }
      break;
  }
  return true;
}

bool LValue::operator==(const Value& rhs) const {
  if (!isValid() || !rhs.isValid()) 
    return false;  
  if (getNbWords() != rhs.getNbWords())
    return false;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    if (getValueL(i) != rhs.getValueL(i))
      return false;
  }  
  return true;
}

ValueFactory::ValueFactory() : m_headFree(nullptr), m_headInUse(nullptr) {}

Value* ValueFactory::newSValue() { return new SValue(); }

Value* ValueFactory::newStValue() { return new StValue(); }

Value* ValueFactory::newLValue() {
  //if (m_headFree == nullptr) {
    LValue* val = new LValue();
    val->setValueFactory(this);
    return val;
  /*
  } else {
    LValue* ret = m_headFree;
    LValue* next = m_headFree->m_next;
    LValue* prev = m_headFree->m_prev;
    m_headFree = next;
    if (prev == next) {
      m_headFree = nullptr;
    } else {
      next->m_prev = prev;
      prev->m_next = next;
    }
    ret->m_prev = nullptr;
    ret->m_next = nullptr;
    return ret;
  }
  */
}

Value* ValueFactory::newValue(SValue& initVal) { return new SValue(initVal); }

Value* ValueFactory::newValue(StValue& initVal) { return new StValue(initVal); }

Value* ValueFactory::newValue(LValue& initVal) {
 // if (m_headFree == nullptr) {
    LValue* val = new LValue(initVal);
    val->setValueFactory(this);
    return val;
 /* } else {
    LValue* ret = m_headFree;
    LValue* next = m_headFree->m_next;
    LValue* prev = m_headFree->m_prev;
    m_headFree = next;
    if (prev == next) {
      m_headFree = nullptr;
    } else {
      next->m_prev = prev;
      prev->m_next = next;
    }
    ret->m_prev = nullptr;
    ret->m_next = nullptr;
    ret->adjust(&initVal);
    for (unsigned int i = 0; i < ret->m_nbWords; i++) {
      if (initVal.m_valueArray)
        ret->m_valueArray[i] = initVal.m_valueArray[i];
    }

    return ret;
  }
  */
}

void ValueFactory::deleteValue(Value* value) {
  delete value;
  /*
  if (value->getType() == Value::Type::String) {
    // TODO: investigate memory corruption
    // delete (StValue*) value;
    return;
  }
  */
  /*
  LValue* val = (LValue*)value;
  const Value* prev = value->m_valueFactory->m_headFree;
  if (prev == nullptr) {
    value->m_valueFactory->m_headFree = (LValue*)val;
    value->m_valueFactory->m_headFree->m_next = value->m_valueFactory->m_headFree;
    value->m_valueFactory->m_headFree->m_prev = value->m_valueFactory->m_headFree;
  } else {
    LValue* next1 = value->m_valueFactory->m_headFree;
    LValue* prev1 = value->m_valueFactory->m_headFree->m_prev;
    next1->m_prev = val;
    prev1->m_next = val;
    val->m_next = next1;
    val->m_prev = prev1;
    value->m_valueFactory->m_headFree = val;
  }
  */
}

void SValue::set(uint64_t val) {
  m_type = Value::Type::Unsigned;
  m_value.u_int = val;
  m_size = 64;
  m_valid = 1;
  m_negative = 0;
}
void SValue::set(int64_t val) {
  m_type = Value::Type::Integer;
  m_value.s_int = val;
  m_size = 64;
  m_valid = 1;
  m_negative = val < 0;
}
void SValue::set(double val) {
  m_type = Value::Type::Double;
  m_value.d_int = val;
  m_size = 64;
  m_valid = 1;
  m_negative = val < 0;
}
void SValue::set(uint64_t val, Type type, unsigned short size) {
  m_type = type;
  m_value.u_int = val;
  m_size = size;
  m_valid = 1;
  m_negative = 0;
}

void SValue::u_plus(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_type = aval->m_type;
  m_size = aval->m_size;
  m_value = aval->m_value;
  m_valid = a->isValid();
  m_negative = a->isNegative();
}

void SValue::incr() {
  switch (m_type) {
    case Value::Type::Integer:
      m_value.s_int++;
      break;
    case Value::Type::Double:
      m_value.d_int++;
      break;
    default:
      m_value.u_int++;
      break;
  }
  if (m_value.s_int == 0) m_negative = false;
}

void SValue::decr() {
  if (m_value.s_int == 0) m_negative = true;
  switch (m_type) {
    case Value::Type::Integer:
      m_value.s_int--;
      break;
    case Value::Type::Double:
      m_value.d_int--;
      break;
    default:
      m_value.u_int--;
      break;
  }
}

void SValue::u_minus(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_size = aval->m_size;
  switch (aval->m_type) {
    case Value::Type::Integer:
      m_value.s_int = -aval->m_value.s_int;
      m_type = Value::Type::Integer;
      break;
    case Value::Type::Double:
      m_value.d_int = -aval->m_value.d_int;
      m_type = Value::Type::Double;
      break;
    default:
      m_value.s_int = -aval->m_value.u_int;
      m_type = Value::Type::Integer;
      break;
  }
  m_negative = !aval->m_negative;
  m_valid = a->isValid();
}

std::string SValue::uhdmValue() {
  Value::Type valueType = getType();
  std::string result;
  switch (valueType) {
    case Value::Type::Scalar:
      result = "SCAL:";
      result += std::to_string(m_value.u_int);
      break;
    case Value::Type::Double:
      result = "REAL:";
      result += std::to_string(m_value.d_int);
      break;
    case Value::Type::Integer:
      result = "INT:";
      result += std::to_string(m_value.s_int);
      break;
    case Value::Type::Unsigned:
      result = "UINT:";
      result += std::to_string(m_value.u_int);
      break;     
    default:
      result = "INT:";
      result += std::to_string(m_value.u_int);
      break;
  }
  return result;
}

std::string SValue::decompiledValue() {
  Value::Type valueType = getType();
  std::string result;
  switch (valueType) {
    case Value::Type::Scalar:
      result += std::to_string(m_value.u_int);
      break;
    case Value::Type::Double:
      result += std::to_string(m_value.d_int);
      break;
    case Value::Type::Integer:
      result += std::to_string(m_value.s_int);
      break;
    default:
      result += std::to_string(m_value.u_int);
      break;
  }
  return result;
}

int SValue::vpiValType() {
  Value::Type valueType = getType();
  switch (valueType) {
    case Value::Type::Scalar:
      return vpiIntConst;
      break;
    case Value::Type::Double:
      return vpiRealConst;
      break;
    case Value::Type::Integer:
      return vpiIntConst;
      break;
    case Value::Type::Unsigned:
      return vpiUIntConst;
      break;  
    default:
      return vpiIntConst;
      break;
  }
}

void SValue::u_not(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_type = aval->m_type;
  m_size = aval->m_size;
  switch (aval->getType()) {
    case Value::Type::Scalar:
      m_value.u_int = !aval->m_value.u_int;
      m_negative = 0;
      break;
    case Value::Type::Double:
       m_value.d_int = !aval->m_value.d_int;
       m_negative = m_value.d_int < 0;
      break;
    case Value::Type::Integer:
      m_value.s_int = !aval->m_value.s_int;
      m_negative = m_value.s_int < 0;
      break;
    default:
      m_value.u_int = !aval->m_value.u_int;
      m_negative = 0;
      break;
  }  
  m_valid = a->isValid();
}

void SValue::u_tilda(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_type = aval->m_type;
  m_size = aval->m_size; 
  switch (aval->getType()) {
    case Value::Type::Scalar:
      m_value.u_int = ~aval->m_value.u_int;
      m_negative = 0;
      break;
    case Value::Type::Double:
       m_value.d_int = ~ (int64_t)aval->m_value.d_int;
       m_negative = m_value.d_int < 0;
      break;
    case Value::Type::Integer:
      m_value.s_int = ~aval->m_value.s_int;
      m_negative = m_value.s_int < 0;
      break;
    default:
      m_value.u_int = ~aval->m_value.u_int;
      m_negative = 0;
      break;
  }  
  m_valid = a->isValid();
}

void SValue::u_bitwAnd(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_type = Value::Type::Unsigned;
  m_size = aval->m_size; 
  uint64_t val = aval->m_value.u_int;
  int res = val & 1;
  for (unsigned int i = 1; i <  m_size; i++) {
    res = res & ((val & (1 << i)) >> i);
  }
  m_value.u_int = res;
  m_valid = a->isValid();
  m_negative = a->isNegative();
}

void SValue::u_bitwNand(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_type = Value::Type::Unsigned;
  m_size = aval->m_size; 
  uint64_t val = aval->m_value.u_int;
  uint64_t res = val & 1;
  for (unsigned int i = 1; i <  m_size; i++) {
    res = res & ((val & (1 << i)) >> i);
  }
  m_value.u_int = !res;
  m_valid = a->isValid();
  m_negative = a->isNegative();
}

void SValue::u_bitwOr(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_type = Value::Type::Unsigned;
  m_size = aval->m_size; 
  uint64_t val = aval->m_value.u_int;
  int res = val & 1;
  for (unsigned int i = 1; i <  m_size; i++) {
    res = res | ((val & (1 << i)) >> i);
  }
  m_value.u_int = res;
  m_valid = a->isValid();
  m_negative = a->isNegative();
}

void SValue::u_bitwNor(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_type = Value::Type::Unsigned;
  m_size = aval->m_size; 
  uint64_t val = aval->m_value.u_int;
  int res = val & 1;
  for (unsigned int i = 1; i <  m_size; i++) {
    res = res | ((val & (1 << i)) >> i);
  }
  m_value.u_int = !res;
  m_valid = a->isValid();
  m_negative = a->isNegative();
}

void SValue::u_bitwXor(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_type = Value::Type::Unsigned;
  m_size = aval->m_size; 
  uint64_t val = aval->m_value.u_int;
  int res = val & 1;
  for (unsigned int i = 1; i <  m_size; i++) {
    res = res ^ ((val & (1 << i)) >> i);
  }
  m_value.u_int = res;
  m_valid = a->isValid();
  m_negative = a->isNegative();
}

void SValue::u_bitwXnor(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_type = Value::Type::Unsigned;
  m_size = aval->m_size; 
  uint64_t val = aval->m_value.u_int;
  int res = val & 1;
  for (unsigned int i = 1; i <  m_size; i++) {
    res = res ^ ((val & (1 << i)) >> i);
  }
  m_value.u_int = !res;
  m_valid = a->isValid();
  m_negative = a->isNegative();
}

void SValue::plus(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  switch (aval->getType()) {
    case Value::Type::Scalar:
      m_negative = 0; 
      m_value.u_int = aval->m_value.u_int + bval->m_value.u_int;
      m_type = Value::Type::Unsigned;
      break;
    case Value::Type::Double:
      m_negative = ((aval->m_value.d_int + bval->m_value.d_int) < 0); 
      m_value.d_int = aval->m_value.d_int + bval->m_value.d_int;
      m_type = Value::Type::Double;
      break;
    case Value::Type::Integer:
      m_negative = ((aval->m_value.s_int + bval->m_value.s_int) < 0); 
      m_value.s_int = aval->m_value.s_int + bval->m_value.s_int;
      m_type = Value::Type::Integer;
      break;
    default:
      m_negative = 0; 
      m_value.u_int = aval->m_value.u_int + bval->m_value.u_int;
      m_type = Value::Type::Unsigned;
      break;
  }  
  m_valid = a->isValid() && b->isValid();
}

void SValue::minus(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  switch (aval->getType()) {
    case Value::Type::Scalar:
      m_negative = 0; 
      m_value.u_int = aval->m_value.u_int - bval->m_value.u_int;
      m_type = Value::Type::Unsigned;
      break;
    case Value::Type::Double:
      m_negative = ((aval->m_value.d_int - bval->m_value.d_int) < 0); 
      m_value.d_int = aval->m_value.d_int - bval->m_value.d_int;
      m_type = Value::Type::Double;
      break;
    case Value::Type::Integer:
      m_negative = ((aval->m_value.s_int - bval->m_value.s_int) < 0); 
      m_value.s_int = aval->m_value.s_int - bval->m_value.s_int;
      m_type = Value::Type::Integer;
      break;
    default:
      m_negative = 0; 
      m_value.u_int = aval->m_value.u_int - bval->m_value.u_int;
      m_type = Value::Type::Unsigned;
      break;
  }  
  m_valid = a->isValid() && b->isValid();
}

void SValue::mult(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  switch (aval->getType()) {
    case Value::Type::Scalar:
      m_negative = 0; 
      m_value.u_int = aval->m_value.u_int * bval->m_value.u_int;
      m_type = Value::Type::Unsigned;
      break;
    case Value::Type::Double:
      m_negative = ((aval->m_value.d_int * bval->m_value.d_int) < 0); 
      m_value.d_int = aval->m_value.d_int * bval->m_value.d_int;
      m_type = Value::Type::Double;
      break;
    case Value::Type::Integer:
      m_negative = ((aval->m_value.s_int * bval->m_value.s_int) < 0); 
      m_value.s_int = aval->m_value.s_int * bval->m_value.s_int;
      m_type = Value::Type::Integer;
      break;
    default:
      m_negative = 0; 
      m_value.u_int = aval->m_value.u_int * bval->m_value.u_int;
      m_type = Value::Type::Unsigned;
      break;
  }  
  m_valid = a->isValid() && b->isValid();
}

void SValue::div(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  if (bval->m_value.s_int == 0) {
    m_valid = 0;
    m_value.s_int = 0;
    m_negative = 0;
  } else {
    switch (aval->getType()) {
      case Value::Type::Scalar:
        m_negative = 0;
        m_value.u_int = aval->m_value.u_int / bval->m_value.u_int;
        m_type = Value::Type::Unsigned;
        break;
      case Value::Type::Double:
        m_negative = ((aval->m_value.d_int / bval->m_value.d_int) < 0);
        m_value.d_int = aval->m_value.d_int / bval->m_value.d_int;
        m_type = Value::Type::Double;
        break;
      case Value::Type::Integer:
        m_negative = ((aval->m_value.s_int / bval->m_value.s_int) < 0);
        m_value.s_int = aval->m_value.s_int / bval->m_value.s_int;
        m_type = Value::Type::Integer;
        break;
      default:
        m_negative = 0;
        m_value.u_int = aval->m_value.u_int / bval->m_value.u_int;
        m_type = Value::Type::Unsigned;
        break;
    }
    m_valid = a->isValid() && b->isValid();
  }
}

void SValue::mod(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  switch (aval->getType()) {
    case Value::Type::Scalar:
      m_negative = 0; 
      m_value.u_int = aval->m_value.u_int % bval->m_value.u_int;
      m_type = Value::Type::Unsigned;
      break;
    case Value::Type::Double:
      m_negative = (((int64_t) aval->m_value.d_int % (int64_t)bval->m_value.d_int) < 0); 
      m_value.s_int = (int64_t)aval->m_value.d_int % (int64_t)bval->m_value.d_int;
      m_type = Value::Type::Integer;
      break;
    case Value::Type::Integer:
      m_negative = ((aval->m_value.s_int % bval->m_value.s_int) < 0); 
      m_value.s_int = aval->m_value.s_int % bval->m_value.s_int;
      m_type = Value::Type::Integer;
      break;
    default:
      m_negative = 0; 
      m_value.u_int = aval->m_value.u_int % bval->m_value.u_int;
      m_type = Value::Type::Unsigned;
      break;
  }  
  m_valid = a->isValid() && b->isValid();
}

void SValue::power(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  switch (aval->getType()) {
    case Value::Type::Scalar:
      m_negative = 0; 
      m_value.u_int = pow(aval->m_value.u_int , bval->m_value.u_int);
      m_type = Value::Type::Unsigned;
      break;
    case Value::Type::Double:
      m_negative = pow(aval->m_value.d_int , bval->m_value.d_int) < 0; 
      m_value.d_int = pow(aval->m_value.d_int , bval->m_value.d_int);
      m_type = Value::Type::Double;
      break;
    case Value::Type::Integer:
      m_negative = pow(aval->m_value.s_int , bval->m_value.s_int) < 0; 
      m_value.s_int = pow(aval->m_value.s_int , bval->m_value.s_int);
      m_type = Value::Type::Integer;
      break;
    default:
      m_negative = 0; 
      m_value.u_int = pow(aval->m_value.u_int , bval->m_value.u_int);
      m_type = Value::Type::Unsigned;
      break;
  }  
  m_valid = a->isValid() && b->isValid();
}

void SValue::greater(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_type = Value::Type::Unsigned;
  m_negative = 0; 
  m_size = 1;
  switch (aval->getType()) {
    case Value::Type::Scalar:
      m_value.u_int = aval->m_value.u_int > bval->m_value.u_int;
      break;
    case Value::Type::Double:
      m_value.u_int = aval->m_value.d_int > bval->m_value.d_int;
      break;
    case Value::Type::Integer:
      m_value.u_int = aval->m_value.s_int > bval->m_value.s_int;
      break;
    default:
      m_value.u_int = aval->m_value.u_int > bval->m_value.u_int;
      break;
  }  
  m_valid = a->isValid() && b->isValid();
}

void SValue::greater_equal(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_type = Value::Type::Unsigned;
  m_negative = 0; 
  m_size = 1;
  switch (aval->getType()) {
    case Value::Type::Scalar:
      m_value.u_int = aval->m_value.u_int >= bval->m_value.u_int;
      break;
    case Value::Type::Double:
      m_value.u_int = aval->m_value.d_int >= bval->m_value.d_int;
      break;
    case Value::Type::Integer:
      m_value.u_int = aval->m_value.s_int >= bval->m_value.s_int;
      break;
    default:
      m_value.u_int = aval->m_value.u_int >= bval->m_value.u_int;
      break;
  }  
  m_valid = a->isValid() && b->isValid();
}

void SValue::lesser(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_type = Value::Type::Unsigned;
  m_negative = 0; 
  m_size = 1;
  switch (aval->getType()) {
    case Value::Type::Scalar:
      m_value.u_int = aval->m_value.u_int < bval->m_value.u_int;
      break;
    case Value::Type::Double:
      m_value.u_int = aval->m_value.d_int < bval->m_value.d_int;
      break;
    case Value::Type::Integer:
      m_value.u_int = aval->m_value.s_int < bval->m_value.s_int;
      break;
    default:
      m_value.u_int = aval->m_value.u_int < bval->m_value.u_int;
      break;
  }  
  m_valid = a->isValid() && b->isValid();
}

void SValue::lesser_equal(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_type = Value::Type::Unsigned;
  m_negative = 0; 
  m_size = 1;
  switch (aval->getType()) {
    case Value::Type::Scalar:
      m_value.u_int = aval->m_value.u_int <= bval->m_value.u_int;
      break;
    case Value::Type::Double:
      m_value.u_int = aval->m_value.d_int <= bval->m_value.d_int;
      break;
    case Value::Type::Integer:
      m_value.u_int = aval->m_value.s_int <= bval->m_value.s_int;
      break;
    default:
      m_value.u_int = aval->m_value.u_int <= bval->m_value.u_int;
      break;
  }  
  m_valid = a->isValid() && b->isValid();
}

void SValue::equiv(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_type = Value::Type::Unsigned;
  m_negative = 0; 
  m_size = 1;
  switch (aval->getType()) {
    case Value::Type::Scalar:
      m_value.u_int = aval->m_value.u_int == bval->m_value.u_int;
      break;
    case Value::Type::Double:
      m_value.u_int = aval->m_value.d_int == bval->m_value.d_int;
      break;
    case Value::Type::Integer:
      m_value.u_int = aval->m_value.s_int == bval->m_value.s_int;
      break;
    default:
      m_value.u_int = aval->m_value.u_int == bval->m_value.u_int;
      break;
  }  
  m_valid = a->isValid() && b->isValid();
}

void SValue::logAnd(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_type = Value::Type::Unsigned;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value.u_int = aval->m_value.u_int && bval->m_value.u_int;
  m_negative = 0;
  m_valid = a->isValid() && b->isValid();
}

void SValue::logOr(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_type = Value::Type::Unsigned;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value.u_int = aval->m_value.u_int || bval->m_value.u_int;
  m_negative = 0;
  m_valid = a->isValid() && b->isValid();
}

void SValue::bitwAnd(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_type = Value::Type::Unsigned;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value.u_int = aval->m_value.u_int & bval->m_value.u_int;
  m_negative = 0;
  m_valid = a->isValid() && b->isValid();
}

void SValue::bitwOr(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_type = Value::Type::Unsigned;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value.u_int = aval->m_value.u_int | bval->m_value.u_int;
  m_negative = 0;
  m_valid = a->isValid() && b->isValid();
}

void SValue::bitwXor(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_type = Value::Type::Unsigned;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value.u_int = aval->m_value.u_int ^ bval->m_value.u_int;
  m_negative = 0;
  m_valid = a->isValid() && b->isValid();
}

void SValue::notEqual(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_type = Value::Type::Unsigned;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value.u_int = aval->m_value.u_int != bval->m_value.u_int;
  m_negative = 0;
  m_valid = a->isValid() && b->isValid();
}

void SValue::shiftLeft(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_type = Value::Type::Unsigned;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value.u_int = aval->m_value.u_int << bval->m_value.u_int;
  m_negative = 0;
  m_valid = a->isValid() && b->isValid();
}

void SValue::shiftRight(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_type = Value::Type::Unsigned;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value.u_int = aval->m_value.u_int >> bval->m_value.u_int;
  m_negative = 0;
  m_valid = a->isValid() && b->isValid();
}

unsigned short LValue::getSize() const {
  unsigned short size = 0;
  for (int i = 0; i < m_nbWords; i++) {
    size += m_valueArray[i].m_size;
  }
  return size;
}

std::string LValue::uhdmValue() {
  std::string result = "INT:";
  // The value is encoded in int form for the most part.

  // if (m_type == Type::Binary)
  //  result = "BIN:";
  // else if (m_type == Type::Hexadecimal)
  //  result = "HEX:";
  // else if (m_type == Type::Octal)
  //  result = "OCT:";
  switch (m_type) {
    case Value::Type::Scalar:
      result = "SCAL:";
      for (int i = 0; i < m_nbWords; i++) {
        result += std::to_string(m_valueArray[i].m_value.u_int);
      }
      break;
    case Value::Type::Double:
      result = "REAL:";
      for (int i = 0; i < m_nbWords; i++) {
        result += std::to_string(m_valueArray[i].m_value.d_int);
      }
      break;
    case Value::Type::Integer:
      result = "INT:";
      for (int i = 0; i < m_nbWords; i++) {
        result += std::to_string(m_valueArray[i].m_value.s_int);
      }
      break;
    case Value::Type::Unsigned:
      result = "UINT:";
      for (int i = 0; i < m_nbWords; i++) {
        result += std::to_string(m_valueArray[i].m_value.u_int);
      }
      break;  
    default:
      result = "INT:";
      for (int i = 0; i < m_nbWords; i++) {
        result += std::to_string(m_valueArray[i].m_value.u_int);
      }
      break;
  }
  return result;
}

std::string LValue::decompiledValue() {
  std::string result;
  switch (m_type) {
    case Value::Type::Scalar:
      for (int i = 0; i < m_nbWords; i++) {
        result += std::to_string(m_valueArray[i].m_value.u_int);
      }
      break;
    case Value::Type::Double:
      for (int i = 0; i < m_nbWords; i++) {
        result += std::to_string(m_valueArray[i].m_value.d_int);
      }
      break;
    case Value::Type::Integer:
      for (int i = 0; i < m_nbWords; i++) {
        result += std::to_string(m_valueArray[i].m_value.s_int);
      }
      break;
    default:
      for (int i = 0; i < m_nbWords; i++) {
        result += std::to_string(m_valueArray[i].m_value.u_int);
      }
      break;
  }
  return result;
}

int LValue::vpiValType() {
  // The value is encoded in int form for the most part.
  switch (m_type) {
    case Type::Binary:
      //return vpiBinaryConst;
      return vpiIntConst;
    case Type::Double:
      return vpiRealConst;
    case Type::Hexadecimal:
      //return vpiHexConst;
      return vpiIntConst;
    case Type::Integer:
      return vpiIntConst;
    case Type::Octal:
      //return vpiOctConst;
      return vpiIntConst;
    case Type::Scalar:
      return vpiScalar;
    case Type::String:
      return vpiStringConst;
    case Type::Unsigned:
      return vpiUIntConst;
    case Type::None:
      return 0;
  }
  return 0;
}


LValue::LValue(const LValue& val)
  : m_type(val.m_type), m_nbWords(val.m_nbWords),
    m_valueArray(new SValue[val.m_nbWords]),
    m_valid(val.isValid()), m_negative(val.isNegative()),
    m_prev(nullptr), m_next(nullptr) {
  for (int i = 0; i < val.m_nbWords; i++) {
    m_valueArray[i] = val.m_valueArray[i];
  }
}

LValue::LValue(uint64_t val)
  : m_type(Type::Unsigned), m_nbWords(1),
    m_valueArray(new SValue[1]), m_valid(1), m_prev(nullptr), m_next(nullptr) {
  m_valueArray[0].m_type = m_type;    
  m_valueArray[0].m_value.u_int = val;
  m_valueArray[0].m_size = 64;
  m_valueArray[0].m_negative = 0;
  m_valid = 1;
  m_negative = 0;
}

LValue::LValue(int64_t val)
  : m_type(Type::Integer), m_nbWords(1), m_valueArray(new SValue[1]), m_valid(1),
    m_prev(nullptr), m_next(nullptr) {
  m_valueArray[0].m_type = m_type;    
  m_valueArray[0].m_value.s_int = val;
  m_valueArray[0].m_size = 64;
  m_valueArray[0].m_negative = (val < 0);
  m_valid = 1;
  m_negative = (val < 0);
}

LValue::LValue(double val)
  : m_type(Type::Double), m_nbWords(1), m_valueArray(new SValue[1]), m_valid(1),
    m_prev(nullptr), m_next(nullptr) {
  m_valueArray[0].m_type = m_type;    
  m_valueArray[0].m_value.d_int = val;
  m_valueArray[0].m_size = 64;
  m_valueArray[0].m_negative = (val < 0);
  m_valid = 1;
  m_negative = (val < 0);
}

LValue::LValue(int64_t val, Type type, unsigned short size)
  : m_type(type), m_nbWords(1), m_valueArray(new SValue[1]), m_valid(1),
    m_prev(nullptr), m_next(nullptr) {
  m_valueArray[0].m_type = m_type;
  m_valueArray[0].m_value.s_int = val;
  m_valueArray[0].m_size = size;
  m_valueArray[0].m_negative = (val < 0);
  m_valid = 1;
  m_negative = (val < 0);
}

void LValue::set(uint64_t val) {
  m_type = Type::Unsigned;
  m_nbWords = 1;
  if (!m_valueArray) m_valueArray = new SValue[1];
  m_valueArray[0].m_type = m_type;
  m_valueArray[0].m_value.u_int = val;
  m_valueArray[0].m_size = 64;
  m_valueArray[0].m_negative = 0;
  m_valid = 1;
  m_negative = 0;
}

void LValue::set(int64_t val) {
  m_type = Type::Integer;
  m_nbWords = 1;
  if (!m_valueArray) m_valueArray = new SValue[1];
  m_valueArray[0].m_type = m_type;
  m_valueArray[0].m_value.s_int = val;
  m_valueArray[0].m_size = 64;
  m_valueArray[0].m_negative = (val < 0);
  m_valid = 1;
  m_negative = (val < 0);
}

void LValue::set(double val) {
  double intpart;
  m_nbWords = 1;
  if (!m_valueArray) m_valueArray = new SValue[1];
  if (modf(val, &intpart) == 0.0) {
    if (val < 0) {
      m_type = Type::Integer;
      m_valueArray[0].m_value.s_int = val;
    } else {
      m_type = Type::Unsigned;
      m_valueArray[0].m_value.u_int = val;
    }
  } else {
    m_type = Type::Double;
    m_valueArray[0].m_value.d_int = val;
  }
  m_valueArray[0].m_type = m_type;
  m_valueArray[0].m_size = 64;
  m_valueArray[0].m_negative = (val < 0);
  m_valid = 1;
  m_negative = (val < 0);
}

void LValue::set(uint64_t val, Type type, unsigned short size) {
  m_type = type;
  m_nbWords = 1;
  if (!m_valueArray) m_valueArray = new SValue[1];
  m_valueArray[0].m_type = m_type;
  m_valueArray[0].m_value.u_int = val;
  m_valueArray[0].m_size = size;
  m_valueArray[0].m_negative = 0;
  m_valid = 1;
  m_negative = 0;
}

void LValue::adjust(const Value* a) {
  m_type = a->getType();
  if (a->getNbWords() != getNbWords()) {
    if (m_nbWords && m_valueArray) {
      delete[] m_valueArray;
      m_valueArray = nullptr;
    }
    m_nbWords = a->getNbWords();
    if (m_nbWords)
      m_valueArray = new SValue[m_nbWords];  
  }
  if (m_valueArray == nullptr) {
    m_valueArray = new SValue[1];
    m_nbWords = 1;
  }
  for (unsigned short i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_value.u_int = 0;
  }
}

void LValue::u_plus(const Value* a) {
  adjust(a);
  Type type = a->getType();
  m_type = type;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_size = a->getSize(i);
    m_valueArray[i].m_type = type;
    switch (a->getType()) {
      case Value::Type::Scalar:
        m_valueArray[i].m_value.u_int = a->getValueUL(i);
        break;
      case Value::Type::Double:
        m_valueArray[i].m_value.d_int = a->getValueD(i);
        break;
      case Value::Type::Integer:
        m_valueArray[i].m_value.s_int = a->getValueL(i);
        break;
      default:
        m_valueArray[i].m_value.u_int = a->getValueUL(i);
        break;
    }
    m_valid = a->isValid();
    m_negative = a->isNegative();
  }
}

void LValue::incr() {
  if (!m_valid || !m_valueArray) return;
  switch (m_type) {
    case Value::Type::Integer:
      m_valueArray[0].m_value.s_int++;
      break;
    case Value::Type::Double:
      m_valueArray[0].m_value.d_int++;
      break;
    default:
      m_valueArray[0].m_value.u_int++;
      break;
  }
  if (m_valueArray[0].m_value.s_int == 0) m_negative = false;
}

void LValue::decr() {
  if (!m_valid || !m_valueArray) return;
  if (m_valueArray[0].m_value.s_int == 0) {
    m_negative = true;
    m_type = Value::Type::Integer;
  }
  switch (m_type) {
    case Value::Type::Integer:
      m_valueArray[0].m_value.s_int--;
      break;
    case Value::Type::Double:
      m_valueArray[0].m_value.d_int--;
      break;
    default:
      m_valueArray[0].m_value.u_int--;
      break;
  }
}

void LValue::u_minus(const Value* a) {
  adjust(a);
  for (unsigned short i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_size = a->getSize(i);
    switch (a->getType()) {
      case Value::Type::Scalar:
        m_valueArray[i].m_value.u_int = -a->getValueUL(i);
        break;
      case Value::Type::Double:
        m_valueArray[i].m_value.d_int = -a->getValueD(i);
        break;
      case Value::Type::Integer:
        m_valueArray[i].m_value.s_int = -a->getValueL(i);
        break;
      default:
        m_valueArray[i].m_value.s_int = -a->getValueUL(i);
        m_type = Value::Type::Integer;
        m_valueArray[i].m_type = m_type;
        break;
    }
    m_valueArray[i].m_type = m_type;
  }
  m_valid = a->isValid();
  m_negative = !a->isNegative();
}

void LValue::u_not(const Value* a) {
  adjust(a);
  m_type = Value::Type::Unsigned;
  m_valid = a->isValid();
  if (!m_valid) return;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    m_valueArray[0].m_value.u_int |= a->getValueUL(i);
    m_valueArray[i].m_size = a->getSize(i);
  }
  m_valueArray[0].m_value.u_int = !m_valueArray[0].m_value.u_int;
  m_valueArray[0].m_size = a->getSize(0);
  m_valueArray[0].m_negative = a->isNegative();
  m_negative = a->isNegative();
}

void LValue::u_tilda(const Value* a) {
  adjust(a);
  m_type = Value::Type::Unsigned;
  m_valid = a->isValid();
  if (!m_valid) return;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_value.u_int = ~a->getValueUL(i);
    m_valueArray[i].m_size = a->getSize(i);
  }
  m_negative = 0;
}

void LValue::u_bitwAnd(const Value* a) {
  adjust(a);
  m_type = Value::Type::Unsigned;
  m_valid = a->isValid();
  if (!m_valid) return;
  int res = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    uint64_t val = a->getValueUL(i);
    if (i == 0) res = val & 1;
    for (unsigned int j = 1; j < a->getSize(i); j++) {
      res = res & ((val & (1 << j)) >> j);
    }
  }
  m_valueArray[0].m_value.u_int = res;
  m_valueArray[0].m_size = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
}

void LValue::u_bitwNand(const Value* a) {
  adjust(a);
  m_type = Value::Type::Unsigned;
  m_valid = a->isValid();
  if (!m_valid) return;
  int res = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    uint64_t val = a->getValueUL(i);
    if (i == 0) res = val & 1;
    for (unsigned int j = 1; j < a->getSize(i); j++) {
      res = res & ((val & (1 << j)) >> j);
    }
  }
  m_valueArray[0].m_value.u_int = !res;
  m_valueArray[0].m_size = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
  m_type = Value::Type::Unsigned;
}

void LValue::u_bitwOr(const Value* a) {
  adjust(a);
  m_type = Value::Type::Unsigned;
  m_valid = a->isValid();
  if (!m_valid) return;
  int res = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    uint64_t val = a->getValueUL(i);
    if (i == 0) res = val & 1;
    for (unsigned int j = 1; j < a->getSize(i); j++) {
      res = res | ((val & (1 << j)) >> j);
    }
  }
  m_valueArray[0].m_value.u_int = res;
  m_valueArray[0].m_size = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
  m_type = Value::Type::Unsigned;
}

void LValue::u_bitwNor(const Value* a) {
  adjust(a);
  m_type = Value::Type::Unsigned;
  m_valid = a->isValid();
  if (!m_valid) return;
  uint64_t res = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    uint64_t val = a->getValueUL(i);
    if (i == 0) res = val & 1;
    for (unsigned int j = 1; j < a->getSize(i); j++) {
      res = res | ((val & (1 << j)) >> j);
    }
  }
  m_valueArray[0].m_value.u_int = !res;
  m_valueArray[0].m_size = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
}

void LValue::u_bitwXor(const Value* a) {
  adjust(a);
  m_type = Value::Type::Unsigned;
  m_valid = a->isValid();
  if (!m_valid) return;
  uint64_t res = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    uint64_t val = a->getValueUL(i);
    if (i == 0) res = val & 1;
    for (unsigned int j = 1; j < a->getSize(i); j++) {
      res = res ^ ((val & (1 << j)) >> j);
    }
  }
  m_valueArray[0].m_value.u_int = res;
  m_valueArray[0].m_size = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
}

void LValue::u_bitwXnor(const Value* a) {
  adjust(a);
  m_type = Value::Type::Unsigned;
  m_valid = a->isValid();
  if (!m_valid) return;
  uint64_t res = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    uint64_t val = a->getValueUL(i);
    if (i == 0) res = val & 1;
    for (unsigned int j = 1; j < a->getSize(i); j++) {
      res = res ^ ((val & (1 << j)) >> j);
    }
  }
  m_valueArray[0].m_value.u_int = !res;
  m_valueArray[0].m_size = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
}

void LValue::plus(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valueArray[0].m_size = a->getSize(0);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;

  switch (a->getType()) {
    case Value::Type::Scalar:
      m_negative = 0; 
      m_valueArray[0].m_value.u_int = a->getValueUL(0) + b->getValueUL(0);
      m_type = Value::Type::Unsigned;
      break;
    case Value::Type::Double:
      m_negative = ((a->getValueD(0) + b->getValueD(0)) < 0); 
      m_valueArray[0].m_value.d_int = a->getValueD(0) + b->getValueD(0);
      m_type = Value::Type::Double;
      break;
    case Value::Type::Integer:
      m_negative = ((a->getValueL(0) + b->getValueL(0)) < 0); 
      m_valueArray[0].m_value.s_int = a->getValueL(0) + b->getValueL(0);
      m_type = Value::Type::Integer;
      break;
    default:
      m_negative = 0; 
      m_valueArray[0].m_value.u_int = a->getValueUL(0) + b->getValueUL(0);
      m_type = Value::Type::Unsigned;
      break;
  }  
  m_valueArray[0].m_negative = m_negative;
  m_valueArray[0].m_type = m_type;
}

void LValue::minus(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  m_valueArray[0].m_size = a->getSize(0);
  if (!m_valid) return;
  switch (a->getType()) {
    case Value::Type::Scalar:
      m_negative = 0; 
      m_valueArray[0].m_value.u_int = a->getValueUL(0) - b->getValueUL(0);
      m_type = Value::Type::Unsigned;
      break;
    case Value::Type::Double:
      m_negative = ((a->getValueD(0) - b->getValueD(0)) < 0); 
      m_valueArray[0].m_value.d_int = a->getValueD(0) - b->getValueD(0);
      m_type = Value::Type::Double;
      break;
    case Value::Type::Integer:
      m_negative = ((a->getValueL(0) - b->getValueL(0)) < 0); 
      m_valueArray[0].m_value.s_int = a->getValueL(0) - b->getValueL(0);
      m_type = Value::Type::Integer;
      break;
    default:
      m_negative = 0; 
      m_valueArray[0].m_value.u_int = a->getValueUL(0) - b->getValueUL(0);
      m_type = Value::Type::Unsigned;
      break;
  }  
  m_valueArray[0].m_negative = m_negative;
  m_valueArray[0].m_type = m_type;
}

void LValue::mult(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  m_valueArray[0].m_size = a->getSize(0);
  if (!m_valid) return;

  switch (a->getType()) {
    case Value::Type::Scalar:
      m_negative = 0; 
      m_valueArray[0].m_value.u_int = a->getValueUL(0) * b->getValueUL(0);
      m_type = Value::Type::Unsigned;
      break;
    case Value::Type::Double:
      m_negative = ((a->getValueD(0) * b->getValueD(0)) < 0); 
      m_valueArray[0].m_value.d_int = a->getValueD(0) * b->getValueD(0);
      m_type = Value::Type::Double;
      break;
    case Value::Type::Integer:
      m_negative = ((a->getValueL(0) * b->getValueL(0)) < 0); 
      m_valueArray[0].m_value.s_int = a->getValueL(0) * b->getValueL(0);
      m_type = Value::Type::Integer;
      break;
    default:
      m_negative = 0; 
      m_valueArray[0].m_value.u_int = a->getValueUL(0) * b->getValueUL(0);
      m_type = Value::Type::Unsigned;
      break;
  }  
  m_valueArray[0].m_negative = m_negative;
  m_valueArray[0].m_type = m_type;
}

void LValue::div(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  m_valueArray[0].m_size = a->getSize(0);
  if (!m_valid) return;
  if (b->getValueL(0)) {
    switch (a->getType()) {
      case Value::Type::Scalar:
        m_negative = 0;
        m_valueArray[0].m_value.u_int = a->getValueUL(0) / b->getValueUL(0);
        m_type = Value::Type::Unsigned;
        break;
      case Value::Type::Double:
        m_negative = ((a->getValueD(0) / b->getValueD(0)) < 0);
        m_valueArray[0].m_value.d_int = a->getValueD(0) / b->getValueD(0);
        m_type = Value::Type::Double;
        break;
      case Value::Type::Integer:
        m_negative = ((a->getValueL(0) / b->getValueL(0)) < 0);
        m_valueArray[0].m_value.s_int = a->getValueL(0) / b->getValueL(0);
        m_type = Value::Type::Integer;
        break;
      default:
        m_negative = 0;
        m_valueArray[0].m_value.u_int = a->getValueUL(0) / b->getValueUL(0);
        m_type = Value::Type::Unsigned;
        break;
    }
    m_valueArray[0].m_negative = m_negative;
    m_valueArray[0].m_type = m_type;
  } else {
    m_valueArray[0].m_value.s_int = 0;
    m_valid = 0;
    m_negative = 0;
    m_type = Value::Type::Unsigned;
  }
}

void LValue::mod(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  m_valueArray[0].m_size = a->getSize(0);
  if (!m_valid) return;
  switch (a->getType()) {
    case Value::Type::Scalar:
      m_negative = 0;
      m_valueArray[0].m_value.u_int = a->getValueUL(0) % b->getValueUL(0);
      m_type = Value::Type::Unsigned;
      break;
    case Value::Type::Double:
      m_negative = (((int64_t) a->getValueD(0) % (int64_t) b->getValueD(0)) < 0);
      m_valueArray[0].m_value.d_int = (int64_t) a->getValueD(0) % (int64_t) b->getValueD(0);
      m_type = Value::Type::Double;
      break;
    case Value::Type::Integer:
      m_negative = ((a->getValueL(0) % b->getValueL(0)) < 0);
      m_valueArray[0].m_value.s_int = a->getValueL(0) % b->getValueL(0);
      m_type = Value::Type::Integer;
      break;
    default:
      m_negative = 0;
      m_valueArray[0].m_value.u_int = a->getValueUL(0) % b->getValueUL(0);
      m_type = Value::Type::Unsigned;
      break;
  }
  m_valueArray[0].m_negative = m_negative;
  m_valueArray[0].m_type = m_type;
}

void LValue::power(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  m_valueArray[0].m_size = a->getSize(0);
  if (!m_valid) return;
  switch (a->getType()) {
    case Value::Type::Scalar:
      m_negative = 0;
      m_valueArray[0].m_value.u_int = pow(a->getValueUL(0), b->getValueUL(0));
      m_type = Value::Type::Unsigned;
      break;
    case Value::Type::Double:
      m_negative = pow(a->getValueD(0), b->getValueD(0)) < 0;
      m_valueArray[0].m_value.d_int = pow(a->getValueD(0), b->getValueD(0));
      m_type = Value::Type::Double;
      break;
    case Value::Type::Integer:
      m_negative = pow(a->getValueL(0), b->getValueL(0)) < 0;
      m_valueArray[0].m_value.s_int = pow(a->getValueL(0), b->getValueL(0));
      m_type = Value::Type::Integer;
      break;
    default:
      m_negative = 0;
      m_valueArray[0].m_value.u_int = pow(a->getValueUL(0), b->getValueUL(0));
      m_type = Value::Type::Unsigned;
      break;
  }
  m_valueArray[0].m_negative = m_negative;
  m_valueArray[0].m_type = m_type;

}

void LValue::greater(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;
  switch (a->getType()) {
    case Value::Type::Scalar:
      m_valueArray[0].m_value.u_int = a->getValueUL(0) > b->getValueUL(0);
      break;
    case Value::Type::Double:
      m_valueArray[0].m_value.u_int = a->getValueD(0) > b->getValueD(0);
      break;
    case Value::Type::Integer:
      m_valueArray[0].m_value.u_int = a->getValueL(0) > b->getValueL(0);
      break;
    default:
      m_valueArray[0].m_value.u_int = a->getValueUL(0) > b->getValueUL(0);
      break;
  }  
  m_valueArray[0].m_size = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
  m_type = Value::Type::Unsigned;
}

void LValue::greater_equal(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;
  switch (a->getType()) {
    case Value::Type::Scalar:
      m_valueArray[0].m_value.u_int = a->getValueUL(0) >= b->getValueUL(0);
      break;
    case Value::Type::Double:
      m_valueArray[0].m_value.u_int = a->getValueD(0) >= b->getValueD(0);
      break;
    case Value::Type::Integer:
      m_valueArray[0].m_value.u_int = a->getValueL(0) >= b->getValueL(0);
      break;
    default:
      m_valueArray[0].m_value.u_int = a->getValueUL(0) >= b->getValueUL(0);
      break;
  }  
  m_valueArray[0].m_size = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
  m_type = Value::Type::Unsigned;
}

void LValue::lesser(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;
  switch (a->getType()) {
    case Value::Type::Scalar:
      m_valueArray[0].m_value.u_int = a->getValueUL(0) < b->getValueUL(0);
      break;
    case Value::Type::Double:
      m_valueArray[0].m_value.u_int = a->getValueD(0) < b->getValueD(0);
      break;
    case Value::Type::Integer:
      m_valueArray[0].m_value.u_int = a->getValueL(0) < b->getValueL(0);
      break;
    default:
      m_valueArray[0].m_value.u_int = a->getValueUL(0) < b->getValueUL(0);
      break;
  }  
  m_valueArray[0].m_size = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
  m_type = Value::Type::Unsigned;
}

void LValue::lesser_equal(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;
  switch (a->getType()) {
    case Value::Type::Scalar:
      m_valueArray[0].m_value.u_int = a->getValueUL(0) <= b->getValueUL(0);
      break;
    case Value::Type::Double:
      m_valueArray[0].m_value.u_int = a->getValueD(0) <= b->getValueD(0);
      break;
    case Value::Type::Integer:
      m_valueArray[0].m_value.u_int = a->getValueL(0) <= b->getValueL(0);
      break;
    default:
      m_valueArray[0].m_value.u_int = a->getValueUL(0) <= b->getValueUL(0);
      break;
  }  
  m_valueArray[0].m_size = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
  m_type = Value::Type::Unsigned;
}

void LValue::equiv(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_size = a->getSize(i);
    if (a->getValueUL(i) != b->getValueUL(i)) {
      m_valueArray[0].m_value.u_int = 0;
      return;
    }
  }
  m_valueArray[0].m_value.u_int = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
  m_type = Value::Type::Unsigned;
}

void LValue::logAnd(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;
  uint64_t tmp1 = 0;
  uint64_t tmp2 = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    tmp1 |= a->getValueUL(i);
    tmp2 |= b->getValueUL(i);
  }
  m_valueArray[0].m_value.u_int = tmp1 && tmp2;
  m_valueArray[0].m_size = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
  m_type = Value::Type::Unsigned;
}

void LValue::logOr(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;
  uint64_t tmp1 = 0;
  uint64_t tmp2 = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    tmp1 |= a->getValueUL(i);
    tmp2 |= b->getValueUL(i);
  }
  m_valueArray[0].m_value.u_int = tmp1 || tmp2;
  m_valueArray[0].m_size = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
  m_type = Value::Type::Unsigned;
}

void LValue::bitwAnd(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_value.u_int = a->getValueUL(i) & b->getValueUL(i);
    m_valueArray[i].m_size = a->getSize(i);
  }
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
  m_type = Value::Type::Unsigned;
}

void LValue::bitwOr(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_value.u_int = a->getValueUL(i) | b->getValueUL(i);
    m_valueArray[i].m_size = a->getSize(i);
  }
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
  m_type = Value::Type::Unsigned;
}

void LValue::bitwXor(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_value.u_int = a->getValueUL(i) ^ b->getValueUL(i);
    m_valueArray[i].m_size = a->getSize(i);
  }
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
  m_type = Value::Type::Unsigned;
}

void LValue::notEqual(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;
  equiv(a, b);
  m_valueArray[0].m_value.u_int = !m_valueArray[0].m_value.u_int;
  m_valueArray[0].m_size = 1;
  m_valueArray[0].m_negative = 0;
  m_negative = 0;
  m_type = Value::Type::Unsigned;
}

void LValue::shiftLeft(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;
  m_valueArray[0].m_value.u_int = a->getValueUL(0) << b->getValueUL(0);
  m_valueArray[0].m_size = a->getSize(0) + b->getValueL(0);
  m_valueArray[0].m_negative = 0;
  m_negative = m_valueArray[0].m_negative;
  m_type = Value::Type::Unsigned;
}

void LValue::shiftRight(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid) return;
  m_valueArray[0].m_value.u_int = a->getValueUL(0) >> b->getValueUL(0);
  m_valueArray[0].m_size = a->getSize(0) - b->getValueL(0);
  m_valueArray[0].m_negative = 0;
  m_negative = m_valueArray[0].m_negative;
  m_type = Value::Type::Unsigned;
}

std::string StValue::uhdmValue() {
  std::string result = "STRING:";
  if (m_type == Type::Binary)
    result = "BIN:";
  else if (m_type == Type::Double)
    result = "REAL:";
  else if (m_type == Type::Hexadecimal)
    result = "HEX:";
  else if (m_type == Type::Octal)
    result = "OCT:";
  else if (m_type == Type::Scalar)
    result = "SCAL:";
  // Remove '"' from the string
  if (result == "STRING:" && m_value.front() == '"' && m_value.back() == '"')
    m_value = m_value.substr(1, m_value.length() - 2);
  result += m_value;
  return result;
}

std::string StValue::decompiledValue() { return m_value; }

void StValue::equiv(const Value* a, const Value* b) {
  const StValue* aval = (const StValue*)a;
  const StValue* bval = (const StValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = (aval->m_value == bval->m_value) ? "1" : "0";
  m_valid = a->isValid() && b->isValid();
}

void StValue::notEqual(const Value* a, const Value* b) {
  const StValue* aval = (const StValue*)a;
  const StValue* bval = (const StValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = (aval->m_value == bval->m_value) ? "0" : "1";
  m_valid = a->isValid() && b->isValid();
}

int StValue::vpiValType() {
  switch (m_type) {
    case Type::Binary:
      return vpiBinaryConst;
    case Type::Double:
      return vpiRealConst;
    case Type::Hexadecimal:
      return vpiHexConst;
    case Type::Integer:
      return vpiIntConst;
    case Type::Octal:
      return vpiOctConst;
    case Type::Scalar:
      return vpiScalar;
    case Type::String:
      return vpiStringConst;
    case Type::Unsigned:
      return vpiUIntConst;
    case Type::None:
      return 0;
  }
  return 0;
}
