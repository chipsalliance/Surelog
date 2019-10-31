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
#include "Value.h"

using namespace SURELOG;

unsigned int Value::nbWords_(unsigned int size) {
  unsigned long nb = size / 64;
  if ((nb * 64) != size) nb++;
  return nb;
}


SValue::~SValue () { }

LValue::~LValue () 
{ 
  delete [] m_valueArray; 
}

StValue::~StValue () { }

bool LValue::operator< (Value& rhs) {
  // TODO 
  return true;
}

bool LValue::operator==(Value& rhs) {
  // TODO 
  return true;
}

ValueFactory::ValueFactory() {
  m_headFree = NULL;
  m_headInUse = NULL;
}

Value* ValueFactory::newSValue() {
  return new SValue();
}

Value* ValueFactory::newStValue() {
  return new StValue();
}

Value* ValueFactory::newLValue() {
  if (m_headFree == NULL)
    {
      return new LValue();
    }
  else 
    {
      LValue* ret = m_headFree;
      LValue* next =  m_headFree->m_next;
      LValue* prev = m_headFree->m_prev;
      m_headFree = next;
      if (prev == next)
        {
          m_headFree = NULL;
        }
      else 
        {
          next->m_prev = prev;
          prev->m_next = next;
        }
      ret->m_prev = NULL;
      ret->m_next = NULL;
      return ret;
    }
}

Value* ValueFactory::newValue(SValue& initVal) {
    return new SValue(initVal);
}

Value* ValueFactory::newValue(StValue& initVal) {
    return new StValue(initVal);
}

Value* ValueFactory::newValue(LValue& initVal) {
   if (m_headFree == NULL)
    {
      return new LValue(initVal);
    }
  else 
    {
      LValue* ret = m_headFree;
      LValue* next =  m_headFree->m_next;
      LValue* prev = m_headFree->m_prev;
      m_headFree = next;
      if (prev == next)
        {
          m_headFree = NULL;
        }
      else 
        {
          next->m_prev = prev;
          prev->m_next = next;
        }
      ret->m_prev = NULL;
      ret->m_next = NULL;
      ret->adjust(&initVal);
      for (unsigned int i = 0; i < ret->m_nbWords; i++)
        {
          ret->m_valueArray[i] = initVal.m_valueArray[i];
        }
      
      return ret;
    }
}

void ValueFactory::deleteValue(Value* value) {
  if (value->getType () == Value::String)
    {
      //TODO: investigate memory corruption
      //delete (StValue*) value;
      return;
    }
  LValue* val = (LValue*) value;
  Value* prev = m_headFree;
  if (prev == NULL)
    {
      m_headFree = (LValue*) val;
      m_headFree->m_next = m_headFree;
      m_headFree->m_prev = m_headFree;
    }
  else 
    {
      LValue* next =  m_headFree;
      LValue* prev = m_headFree->m_prev;
      next->m_prev = val;
      prev->m_next = val;
      val->m_next = next;
      val->m_prev = prev;
      m_headFree = val;
    }
}

void SValue::set (unsigned long val){
   m_value = val; m_size = 64; 
}
void SValue::set (long val){
  m_value = val; m_size = 64;
}
void SValue::set (double val){
 m_value = (unsigned long) val;  m_size = 64; 
}
void SValue::set (unsigned long val, ValueType type, unsigned short size){
  m_value = val; m_size = size;
}


void SValue::u_plus (Value* a) {
  SValue* aval = (SValue*) a;
  m_size = aval->m_size;
  m_value = aval->m_value;
}

void SValue::incr() {
  m_value++;
}

void SValue::decr() {
  m_value--;   
}

void SValue::u_minus (Value* a) {
  SValue* aval = (SValue*) a;
  m_size = aval->m_size;
  m_value =  - aval->m_value;
}

void SValue::u_not (Value* a) {
  SValue* aval = (SValue*) a;
  m_size = aval->m_size;
  m_value = ! aval->m_value;
}

void SValue::u_tilda (Value* a) {
  SValue* aval = (SValue*) a;
  m_size = aval->m_size;
  m_value =  ~ aval->m_value;
}

void SValue::plus (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value + bval->m_value;
}

void SValue::minus (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value - bval->m_value;
}

void SValue::mult (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value * bval->m_value;
}

void SValue::div (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value / bval->m_value;
}

void SValue::mod (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value % bval->m_value;
}

void SValue::greater (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value > bval->m_value;
}

void SValue::greater_equal (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value >= bval->m_value;
}

void SValue::lesser (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value < bval->m_value;
}

void SValue::lesser_equal (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value <= bval->m_value;
}

void SValue::equiv (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value == bval->m_value;
}

void SValue::logAnd (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value && bval->m_value;
}

void SValue::logOr (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value || bval->m_value; 
}

void SValue::bitwAnd (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value & bval->m_value;
}

void SValue::bitwOr (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value | bval->m_value; 
}

void SValue::bitwXor (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value ^ bval->m_value;
}

void SValue::notEqual (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value != bval->m_value;
}

void SValue::shiftLeft (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value << bval->m_value;
}

void SValue::shiftRight (Value* a, Value* b) {
  SValue* aval = (SValue*) a;
  SValue* bval = (SValue*) b;
  m_size = (aval->m_size > bval->m_size) ? aval->m_size : bval->m_size;
  m_value =  aval->m_value >> bval->m_value;
}


unsigned short LValue::getSize() {
  unsigned short size = 0;
  for (int i = 0; i < m_nbWords; i++)
    {
      size +=  m_valueArray[i].m_size;
    }
  return size;
}

LValue::LValue(LValue& val) {
  m_type = val.m_type;
  m_prev = NULL;
  m_next = NULL;
  m_nbWords = val.m_nbWords;
  m_valueArray = new SValue[val.m_nbWords];
  for (int i = 0; i < val.m_nbWords; i++)
    {
      m_valueArray[i] = val.m_valueArray[i];
    }
}

LValue::LValue(unsigned long val) { 
  m_type = Unsigned; 
  m_nbWords = 1;
  m_valueArray = new SValue [1];
  m_valueArray[0].m_value = val; 
  m_valueArray[0].m_size = 64; 
  m_prev = NULL;
  m_next = NULL;
}

LValue::LValue(long val) { 
  m_type = Integer; 
  m_nbWords = 1;
  m_valueArray = new SValue [1];
  m_valueArray[0].m_value = (unsigned long) val; 
  m_valueArray[0].m_size = 64; 
  m_prev = NULL;
  m_next = NULL;
}

LValue::LValue(double val) {
  m_type = Double; 
  m_nbWords = 1;
  m_valueArray = new SValue [1];
  m_valueArray[0].m_value = (unsigned long) val; 
  m_valueArray[0].m_size = 64; 
  m_prev = NULL;
  m_next = NULL;
}

LValue::LValue(unsigned long val, ValueType type, unsigned short size) { 
  m_type = type; 
  m_nbWords = 1;
  m_valueArray = new SValue [1];
  m_valueArray[0].m_value = val; 
  m_valueArray[0].m_size = size; 
  m_prev = NULL;
  m_next = NULL;
} 

void
LValue::set (unsigned long val) {
  m_type = Unsigned;
  m_nbWords = 1;
  if (!m_valueArray)
    m_valueArray = new SValue [1];
  m_valueArray[0].m_value = val; 
  m_valueArray[0].m_size = 64; 
}

void LValue::set (long val){
  m_type = Integer;
  m_nbWords = 1;
  if (!m_valueArray)
    m_valueArray = new SValue [1];
  m_valueArray[0].m_value = (unsigned long) val; 
  m_valueArray[0].m_size = 64; 
}

void LValue::set (double val){
  m_type = Double;
  m_nbWords = 1;
  if (!m_valueArray)
    m_valueArray = new SValue [1];
  m_valueArray[0].m_value = (unsigned long) val; 
  m_valueArray[0].m_size = 64; 
}

void LValue::set (unsigned long val, ValueType type, unsigned short size){
  m_type = type;
  m_nbWords = 1;
  if (!m_valueArray)
    m_valueArray = new SValue [1];
  m_valueArray[0].m_value = val; 
  m_valueArray[0].m_size = size; 
}

void LValue::adjust(Value* a)
{
  m_type = a->getType ();
  if (a->getNbWords () > getNbWords ())
    {
      if (m_valueArray)
        delete [] m_valueArray;
      m_nbWords = a->getNbWords ();
      m_valueArray = new SValue [m_nbWords];
    }
}

void LValue::u_plus (Value* a) {
  adjust(a);
  for (unsigned int i = 0; i < m_nbWords; i++)
    {
      m_valueArray[i].m_value = a->getValueUL (i);
    }
}


void LValue::incr() {
  m_valueArray[0].m_value++;
}

void LValue::decr() {
  m_valueArray[0].m_value--;   
}

void LValue::u_minus (Value* a) {
  adjust(a);
  for (unsigned short i = 0; i < m_nbWords; i++)
    {
      m_valueArray[i].m_value = a->getValueUL (i);
      if (i == (m_nbWords -1))
        {
          m_valueArray[i].m_value = ~m_valueArray[i].m_value + 1;
        }
    }
  
}

void LValue::u_not (Value* a) {
  adjust(a);
  for (unsigned int i = 0; i < m_nbWords; i++)
    {
      m_valueArray[0].m_value |= a->getValueUL (i);
    }
  m_valueArray[0].m_value = ! m_valueArray[0].m_value;
}

void LValue::u_tilda (Value* a) {
  adjust(a);
  for (unsigned int i = 0; i < m_nbWords; i++)
    {
      m_valueArray[i].m_value = ~ a->getValueUL (i);
    }
}

void LValue::plus (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  m_valueArray[0].m_value = a->getValueL (0) + b->getValueL (0); 
}

void LValue::minus (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  m_valueArray[0].m_value = a->getValueL (0) - b->getValueL (0); 
}

void LValue::mult (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  m_valueArray[0].m_value = a->getValueL (0) * b->getValueL (0); 
}

void LValue::div (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  m_valueArray[0].m_value = a->getValueL (0) / b->getValueL (0);  
}

void LValue::mod (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  m_valueArray[0].m_value = a->getValueL (0) % b->getValueL (0); 
}

void LValue::greater (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  m_valueArray[0].m_value = a->getValueL (0) > b->getValueL (0); 
}

void LValue::greater_equal (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  m_valueArray[0].m_value = a->getValueL (0) >= b->getValueL (0); 
}

void LValue::lesser (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  m_valueArray[0].m_value = a->getValueL (0) < b->getValueL (0); 
}

void LValue::lesser_equal (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  m_valueArray[0].m_value = a->getValueL (0) <= b->getValueL (0); 
}

void LValue::equiv (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  for (unsigned int i = 0; i < m_nbWords; i++)
    {
      if (a->getValueUL (i) != b->getValueUL (i)) 
        {
          m_valueArray[0].m_value = 0;
          return;
        }
    }
  m_valueArray[0].m_value = 1;
}

void LValue::logAnd (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  unsigned long tmp1 = 0;
  unsigned long tmp2 = 0;
  for (unsigned int i = 0; i < m_nbWords; i++)
    {
      tmp1 |= a->getValueUL (i);
      tmp2 |= b->getValueUL (i);
    }
  m_valueArray[0].m_value = tmp1 && tmp2;
}

void LValue::logOr (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  unsigned long tmp1 = 0;
  unsigned long tmp2 = 0;
  for (unsigned int i = 0; i < m_nbWords; i++)
    {
      tmp1 |= a->getValueUL (i);
      tmp2 |= b->getValueUL (i);
    }
  m_valueArray[0].m_value = tmp1 || tmp2;
}

void LValue::bitwAnd (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  for (unsigned int i = 0; i < m_nbWords; i++)
    {
      m_valueArray[i].m_value  = a->getValueUL (i) & b->getValueUL (i);
    }
}

void LValue::bitwOr (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  for (unsigned int i = 0; i < m_nbWords; i++)
    {
      m_valueArray[i].m_value  = a->getValueUL (i) | b->getValueUL (i);
    }

}

void LValue::bitwXor (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  for (unsigned int i = 0; i < m_nbWords; i++)
    {
      m_valueArray[i].m_value  = a->getValueUL (i) ^ b->getValueUL (i);
    }

}

void LValue::notEqual (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  equiv(a,b);
  m_valueArray[0].m_value = !m_valueArray[0].m_value;
}

void LValue::shiftLeft (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  m_valueArray[0].m_value = a->getValueUL (0) << b->getValueUL (0);
}

void LValue::shiftRight (Value* a, Value* b) {
  adjust(a);
  adjust(b);
  m_valueArray[0].m_value = a->getValueUL (0) >> b->getValueUL (0);
}


