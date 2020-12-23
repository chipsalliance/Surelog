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
  if (!isValid() || !rhs.isValid()) 
    return false;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    if (getValueUL(i) >= rhs.getValueUL(i))
      return false;
  }
  return true;
}

bool LValue::operator==(const Value& rhs) const {
  if (!isValid() || !rhs.isValid()) 
    return false;
  if (getNbWords() != rhs.getNbWords())
    return false;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    if (getValueUL(i) != rhs.getValueUL(i))
      return false;
  }  
  return true;
}

ValueFactory::ValueFactory() : m_headFree(nullptr), m_headInUse(nullptr) {}

Value* ValueFactory::newSValue() { return new SValue(); }

Value* ValueFactory::newStValue() { return new StValue(); }

Value* ValueFactory::newLValue() {
  if (m_headFree == nullptr) {
    return new LValue();
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
}

Value* ValueFactory::newValue(SValue& initVal) { return new SValue(initVal); }

Value* ValueFactory::newValue(StValue& initVal) { return new StValue(initVal); }

Value* ValueFactory::newValue(LValue& initVal) {
  if (m_headFree == nullptr) {
    return new LValue(initVal);
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
    ret->adjust(&initVal);
    for (unsigned int i = 0; i < ret->m_nbWords; i++) {
      if (initVal.m_valueArray)
        ret->m_valueArray[i] = initVal.m_valueArray[i];
    }

    return ret;
  }
}

void ValueFactory::deleteValue(Value* value) {
  if (value->getType() == Value::Type::String) {
    // TODO: investigate memory corruption
    // delete (StValue*) value;
    return;
  }
  LValue* val = (LValue*)value;
  const Value* prev = m_headFree;
  if (prev == nullptr) {
    m_headFree = (LValue*)val;
    m_headFree->m_next = m_headFree;
    m_headFree->m_prev = m_headFree;
  } else {
    LValue* next = m_headFree;
    LValue* prev = m_headFree->m_prev;
    next->m_prev = val;
    prev->m_next = val;
    val->m_next = next;
    val->m_prev = prev;
    m_headFree = val;
  }
}

void SValue::set(uint64_t val) {
  m_value = val;
  m_size = 64;
  m_valid = 1;
}
void SValue::set(int64_t val) {
  m_value = val;
  m_size = 64;
  m_valid = 1;
}
void SValue::set(double val) {
  m_value = (uint64_t)val;
  m_size = 64;
  m_valid = 1;
}
void SValue::set(uint64_t val, Type type, unsigned short size) {
  m_value = val;
  m_size = size;
  m_valid = 1;
}

void SValue::u_plus(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_size = aval->m_size;
  m_value = aval->m_value;
  m_valid = a->isValid();
}

void SValue::incr() { m_value++; }

void SValue::decr() { m_value--; }

void SValue::u_minus(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_size = aval->m_size;
  m_value = -aval->m_value;
  m_valid = a->isValid();
}

std::string SValue::uhdmValue() {
  Value::Type valueType = getType();
  std::string result;
  switch (valueType) {
    case (Value::Type::Scalar):
      result = "SCAL:";
      break;
    default:
      result = "INT:";
      break;
  }
  result += std::to_string(m_value);
  return result;
}

std::string SValue::decompiledValue() {
  std::string result = std::to_string(m_value);
  return result;
}

void SValue::u_not(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_size = aval->m_size;  
  m_value = !aval->m_value;
  m_valid = a->isValid();
}

void SValue::u_tilda(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_size = aval->m_size; 
  m_value = ~aval->m_value;
  m_valid = a->isValid();
}

void SValue::u_bitwAnd(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_size = aval->m_size; 
  uint64_t val = aval->m_value;
  int res = val & 1;
  for (unsigned int i = 1; i <  m_size; i++) {
    res = res & ((val & (1 << i)) >> i);
  }
  m_value = res;
  m_valid = a->isValid();
}

void SValue::u_bitwNand(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_size = aval->m_size; 
  uint64_t val = aval->m_value;
  int res = val & 1;
  for (unsigned int i = 1; i <  m_size; i++) {
    res = res & ((val & (1 << i)) >> i);
  }
  m_value = ~res;
  m_valid = a->isValid();
}

void SValue::u_bitwOr(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_size = aval->m_size; 
  uint64_t val = aval->m_value;
  int res = val & 1;
  for (unsigned int i = 1; i <  m_size; i++) {
    res = res | ((val & (1 << i)) >> i);
  }
  m_value = res;
  m_valid = a->isValid();
}

void SValue::u_bitwNor(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_size = aval->m_size; 
  uint64_t val = aval->m_value;
  int res = val & 1;
  for (unsigned int i = 1; i <  m_size; i++) {
    res = res | ((val & (1 << i)) >> i);
  }
  m_value = ~res;
  m_valid = a->isValid();
}

void SValue::u_bitwXor(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_size = aval->m_size; 
  uint64_t val = aval->m_value;
  int res = val & 1;
  for (unsigned int i = 1; i <  m_size; i++) {
    res = res ^ ((val & (1 << i)) >> i);
  }
  m_value = res;
  m_valid = a->isValid();
}

void SValue::u_bitwXnor(const Value* a) {
  const SValue* aval = (const SValue*)a;
  m_size = aval->m_size; 
  uint64_t val = aval->m_value;
  int res = val & 1;
  for (unsigned int i = 1; i <  m_size; i++) {
    res = res ^ ((val & (1 << i)) >> i);
  }
  m_value = ~res;
  m_valid = a->isValid();
}

void SValue::plus(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value + bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::minus(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value - bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::mult(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value * bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::div(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  if (bval->m_value == 0) {
    m_valid = 0;
    m_value = 0;
  } else {
    m_value = aval->m_value / bval->m_value;
    m_valid = a->isValid() && b->isValid();
  }
}

void SValue::mod(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value % bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::power(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = pow(aval->m_value , bval->m_value);
  m_valid = a->isValid() && b->isValid();
}

void SValue::greater(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value > bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::greater_equal(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value >= bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::lesser(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value < bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::lesser_equal(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value <= bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::equiv(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value == bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::logAnd(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value && bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::logOr(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value || bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::bitwAnd(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value & bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::bitwOr(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value | bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::bitwXor(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value ^ bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::notEqual(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value != bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::shiftLeft(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value << bval->m_value;
  m_valid = a->isValid() && b->isValid();
}

void SValue::shiftRight(const Value* a, const Value* b) {
  const SValue* aval = (const SValue*)a;
  const SValue* bval = (const SValue*)b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value = aval->m_value >> bval->m_value;
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
  for (int i = 0; i < m_nbWords; i++) {
    result += std::to_string(m_valueArray[i].m_value);
  }
  return result;
}

std::string LValue::decompiledValue() {
  std::string result;
  for (int i = 0; i < m_nbWords; i++) {
    result += std::to_string(m_valueArray[i].m_value);
  }
  return result;
}

LValue::LValue(const LValue& val)
  : m_type(val.m_type), m_nbWords(val.m_nbWords),
    m_valueArray(new SValue[val.m_nbWords]),
    m_valid(val.isValid()),
    m_prev(nullptr), m_next(nullptr) {
  for (int i = 0; i < val.m_nbWords; i++) {
    m_valueArray[i] = val.m_valueArray[i];
  }
}

LValue::LValue(uint64_t val)
  : m_type(Type::Unsigned), m_nbWords(1),
    m_valueArray(new SValue[1]), m_valid(1), m_prev(nullptr), m_next(nullptr) {
  m_valueArray[0].m_value = val;
  m_valueArray[0].m_size = 64;
  m_valid = 1;
}

LValue::LValue(int64_t val)
  : m_type(Type::Integer), m_nbWords(1), m_valueArray(new SValue[1]), m_valid(1),
    m_prev(nullptr), m_next(nullptr) {
  m_valueArray[0].m_value = (uint64_t)val;
  m_valueArray[0].m_size = 64;
  m_valid = 1;
}

LValue::LValue(double val)
  : m_type(Type::Double), m_nbWords(1), m_valueArray(new SValue[1]), m_valid(1),
    m_prev(nullptr), m_next(nullptr) {
  m_valueArray[0].m_value = (uint64_t)val;
  m_valueArray[0].m_size = 64;
  m_valid = 1;
}

LValue::LValue(uint64_t val, Type type, unsigned short size)
  : m_type(type), m_nbWords(1), m_valueArray(new SValue[1]), m_valid(1),
    m_prev(nullptr), m_next(nullptr) {
  m_valueArray[0].m_value = val;
  m_valueArray[0].m_size = size;
  m_valid = 1;
}

void LValue::set(uint64_t val) {
  m_type = Type::Unsigned;
  m_nbWords = 1;
  if (!m_valueArray) m_valueArray = new SValue[1];
  m_valueArray[0].m_value = val;
  m_valueArray[0].m_size = 64;
  m_valid = 1;
}

void LValue::set(int64_t val) {
  m_type = Type::Integer;
  m_nbWords = 1;
  if (!m_valueArray) m_valueArray = new SValue[1];
  m_valueArray[0].m_value = (uint64_t)val;
  m_valueArray[0].m_size = 64;
  m_valid = 1;
}

void LValue::set(double val) {
  m_type = Type::Double;
  m_nbWords = 1;
  if (!m_valueArray) m_valueArray = new SValue[1];
  m_valueArray[0].m_value = (uint64_t)val;
  m_valueArray[0].m_size = 64;
  m_valid = 1;
}

void LValue::set(uint64_t val, Type type, unsigned short size) {
  m_type = type;
  m_nbWords = 1;
  if (!m_valueArray) m_valueArray = new SValue[1];
  m_valueArray[0].m_value = val;
  m_valueArray[0].m_size = size;
  m_valid = 1;
}

void LValue::adjust(const Value* a) {
  m_type = a->getType();
  if (a->getNbWords() != getNbWords()) {
    if (m_nbWords && m_valueArray) 
      delete[] m_valueArray;
    m_nbWords = a->getNbWords();
    if (m_nbWords)
      m_valueArray = new SValue[m_nbWords];  
  }
  if (m_valueArray == nullptr) {
    m_valueArray = new SValue[1];
    m_nbWords = 1;
  }
}

void LValue::u_plus(const Value* a) {
  adjust(a);
  for (unsigned int i = 0; i < m_nbWords; i++) {
    long long tmp = a->getValueL(i);
    m_valueArray[i].m_size = a->getSize(i);
    if (tmp >= 0)
      m_valueArray[i].m_value = tmp;
    else {
      m_valueArray[i].m_value = 0;
      m_valid = false;
      return;
    }
  }
  m_valid = a->isValid();
}

void LValue::incr() { 
  if (!m_valid || !m_valueArray)
    return;
  m_valueArray[0].m_value++; 
}

void LValue::decr() { 
  if (!m_valid || !m_valueArray)
    return;
  m_valueArray[0].m_value--; 
}

void LValue::u_minus(const Value* a) {
  adjust(a);
  for (unsigned short i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_value = a->getValueL(i);
    m_valueArray[i].m_size = a->getSize(i);
    if (i == (m_nbWords - 1)) {
      m_valueArray[i].m_value = ~m_valueArray[i].m_value + 1;
    }
  }
  m_valid = a->isValid();
}

void LValue::u_not(const Value* a) {
  adjust(a);
  m_valid = a->isValid();
  if (!m_valid)
    return;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    m_valueArray[0].m_value |= a->getValueUL(i);
    m_valueArray[i].m_size = a->getSize(i);
  }
  m_valueArray[0].m_value = !m_valueArray[0].m_value;
  m_valueArray[0].m_size = a->getSize(0);
}

void LValue::u_tilda(const Value* a) {
  adjust(a);
  m_valid = a->isValid();
  if (!m_valid)
    return;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_value = ~a->getValueUL(i);
    m_valueArray[i].m_size = a->getSize(i);
  }
}

void LValue::u_bitwAnd(const Value* a) {
  adjust(a);
  m_valid = a->isValid();
  if (!m_valid)
    return;
  int res = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    uint64_t val = a->getValueUL(i);
    if (i == 0)
      res = val & 1;
    for (unsigned int j = 1; j < a->getSize(i); j++) {
      res = res & ((val & (1 << j)) >> j);
    }
  }
  m_valueArray[0].m_value = res;
  m_valueArray[0].m_size = 1;
}

void LValue::u_bitwNand(const Value* a) {
  adjust(a);
  m_valid = a->isValid();
  if (!m_valid)
    return;
  int res = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    uint64_t val = a->getValueUL(i);
    if (i == 0)
      res = val & 1;
    for (unsigned int j = 1; j < a->getSize(i); j++) {
      res = res & ((val & (1 << j)) >> j);
    }
  }
  m_valueArray[0].m_value = ~res;
  m_valueArray[0].m_size = 1;
}

void LValue::u_bitwOr(const Value* a) {
  adjust(a);
  m_valid = a->isValid();
  if (!m_valid)
    return;
  int res = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    uint64_t val = a->getValueUL(i);
    if (i == 0)
      res = val & 1;
    for (unsigned int j = 1; j < a->getSize(i); j++) {
      res = res | ((val & (1 << j)) >> j);
    }
  }
  m_valueArray[0].m_value = res;
  m_valueArray[0].m_size = 1;
}

void LValue::u_bitwNor(const Value* a) {
  adjust(a);
  m_valid = a->isValid();
  if (!m_valid)
    return;
  int res = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    uint64_t val = a->getValueUL(i);
    if (i == 0)
      res = val & 1;
    for (unsigned int j = 1; j < a->getSize(i); j++) {
      res = res | ((val & (1 << j)) >> j);
    }
  }
  m_valueArray[0].m_value = ~res;
  m_valueArray[0].m_size = 1;
}

void LValue::u_bitwXor(const Value* a) {
  adjust(a);
  m_valid = a->isValid();
  if (!m_valid)
    return;
  int res = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    uint64_t val = a->getValueUL(i);
    if (i == 0)
      res = val & 1;
    for (unsigned int j = 1; j < a->getSize(i); j++) {
      res = res ^ ((val & (1 << j)) >> j);
    }
  }
  m_valueArray[0].m_value = res;
  m_valueArray[0].m_size = 1;
}

void LValue::u_bitwXnor(const Value* a) {
  adjust(a);
  m_valid = a->isValid();
  if (!m_valid)
    return;
  int res = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    uint64_t val = a->getValueUL(i);
    if (i == 0)
      res = val & 1;
    for (unsigned int j = 1; j < a->getSize(i); j++) {
      res = res ^ ((val & (1 << j)) >> j);
    }
  }
  m_valueArray[0].m_value = ~res;
  m_valueArray[0].m_size = 1;
}

void LValue::plus(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  m_valueArray[0].m_value = a->getValueL(0) + b->getValueL(0);
  m_valueArray[0].m_size = a->getSize(0);
}

void LValue::minus(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  m_valueArray[0].m_value = a->getValueL(0) - b->getValueL(0);
  m_valueArray[0].m_size = a->getSize(0);
}

void LValue::mult(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  m_valueArray[0].m_value = a->getValueL(0) * b->getValueL(0);
  m_valueArray[0].m_size = a->getSize(0);
}

void LValue::div(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  if (b->getValueL(0))
    m_valueArray[0].m_value = a->getValueL(0) / b->getValueL(0);
  else {
    m_valueArray[0].m_value = 0;
    m_valid = 0;
  }
  m_valueArray[0].m_size = a->getSize(0);
}

void LValue::mod(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  m_valueArray[0].m_value = a->getValueL(0) % b->getValueL(0);
  m_valueArray[0].m_size = a->getSize(0);
}


void LValue::power(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  m_valueArray[0].m_value = pow(a->getValueL(0), b->getValueL(0));
  m_valueArray[0].m_size = a->getSize(0);
}


void LValue::greater(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  m_valueArray[0].m_value = a->getValueL(0) > b->getValueL(0);
  m_valueArray[0].m_size = a->getSize(0);
}

void LValue::greater_equal(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  m_valueArray[0].m_value = a->getValueL(0) >= b->getValueL(0);
  m_valueArray[0].m_size = a->getSize(0);
}

void LValue::lesser(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  m_valueArray[0].m_value = a->getValueL(0) < b->getValueL(0);
  m_valueArray[0].m_size = a->getSize(0);
}

void LValue::lesser_equal(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  m_valueArray[0].m_value = a->getValueL(0) <= b->getValueL(0);
  m_valueArray[0].m_size = a->getSize(0);
}

void LValue::equiv(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_size = a->getSize(i);
    if (a->getValueUL(i) != b->getValueUL(i)) {
      m_valueArray[0].m_value = 0;
      return;
    }
  }
  m_valueArray[0].m_value = 1;
}

void LValue::logAnd(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  uint64_t tmp1 = 0;
  uint64_t tmp2 = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    tmp1 |= a->getValueUL(i);
    tmp2 |= b->getValueUL(i);
  }
  m_valueArray[0].m_value = tmp1 && tmp2;
  m_valueArray[0].m_size = 1;
}

void LValue::logOr(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  uint64_t tmp1 = 0;
  uint64_t tmp2 = 0;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    tmp1 |= a->getValueUL(i);
    tmp2 |= b->getValueUL(i);
  }
  m_valueArray[0].m_value = tmp1 || tmp2;
  m_valueArray[0].m_size = 1;
}

void LValue::bitwAnd(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_value = a->getValueUL(i) & b->getValueUL(i);
    m_valueArray[i].m_size = a->getSize(i);
  }
}

void LValue::bitwOr(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_value = a->getValueUL(i) | b->getValueUL(i);
    m_valueArray[i].m_size = a->getSize(i);
  }
}

void LValue::bitwXor(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  for (unsigned int i = 0; i < m_nbWords; i++) {
    m_valueArray[i].m_value = a->getValueUL(i) ^ b->getValueUL(i);
    m_valueArray[i].m_size = a->getSize(i);
  }
}

void LValue::notEqual(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  equiv(a, b);
  m_valueArray[0].m_value = !m_valueArray[0].m_value;
  m_valueArray[0].m_size = 1;
}

void LValue::shiftLeft(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  m_valueArray[0].m_value = a->getValueL(0) << b->getValueL(0);
  m_valueArray[0].m_size =  a->getSize(0) + b->getValueL(0);
}

void LValue::shiftRight(const Value* a, const Value* b) {
  adjust(a);
  adjust(b);
  m_valid = a->isValid() && b->isValid();
  if (!m_valid)
    return;
  m_valueArray[0].m_value = a->getValueL(0) >> b->getValueL(0);
  m_valueArray[0].m_size =  a->getSize(0) - b->getValueL(0);
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
  //Remove '"' from the string
  if (result == "STRING:" && m_value.front() == '"' && m_value.back() == '"')
    m_value = m_value.substr(1, m_value.length() - 2);
  result += m_value;
  return result;
}

std::string StValue::decompiledValue() {
  return m_value;
}

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
