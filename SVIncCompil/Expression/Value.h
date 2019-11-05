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
 * File:   Value.h
 * Author: alain
 *
 * Created on October 29, 2017, 10:33 PM
 */

#ifndef VALUE_H
#define VALUE_H

#include <string>

namespace SURELOG {

class Expr;
class LValue;
class StValue;
class ValueFactory;

class Value {
 public:
  friend Expr;
  friend ValueFactory;

  typedef enum {
    None,
    Binary,
    Hexadecimal,
    Octal,
    Unsigned,
    Integer,
    Double,
    String
  } ValueType;

  virtual unsigned short getSize() = 0;  // size in bits
  virtual unsigned short
  getNbWords() = 0;  // nb of 64 bits words necessary to encode the size
  virtual ValueType getType() = 0;
  virtual bool isLValue() = 0;  // is large value (more than one 64 bit word)
  virtual unsigned long getValueUL(unsigned short index = 0) = 0;
  virtual long getValueL(unsigned short index = 0) = 0;
  virtual double getValueD(unsigned short index = 0) = 0;
  virtual std::string getValueS() = 0;
  virtual void set(unsigned long val) = 0;
  virtual void set(long val) = 0;
  virtual void set(double val) = 0;
  virtual void set(unsigned long val, ValueType type, unsigned short size) = 0;
  virtual void set(std::string val) = 0;
  virtual bool operator<(Value& rhs) = 0;
  bool operator>(Value& rhs) { return rhs < (*this); }
  bool operator<=(Value& rhs) { return !(*this > rhs); }
  bool operator>=(Value& rhs) { return !(*this < rhs); }
  virtual bool operator==(Value& rhs) = 0;
  bool operator!=(Value& rhs) { return !((*this) == rhs); }
  virtual void u_plus(Value* a) = 0;
  virtual void u_minus(Value* a) = 0;
  virtual void u_not(Value* a) = 0;
  virtual void u_tilda(Value* a) = 0;
  virtual void incr() = 0;
  virtual void decr() = 0;
  virtual void plus(Value* a, Value* b) = 0;
  virtual void minus(Value* a, Value* b) = 0;
  virtual void mult(Value* a, Value* b) = 0;
  virtual void div(Value* a, Value* b) = 0;
  virtual void mod(Value* a, Value* b) = 0;
  virtual void greater(Value* a, Value* b) = 0;
  virtual void greater_equal(Value* a, Value* b) = 0;
  virtual void lesser(Value* a, Value* b) = 0;
  virtual void lesser_equal(Value* a, Value* b) = 0;
  virtual void equiv(Value* a, Value* b) = 0;
  virtual void logAnd(Value* a, Value* b) = 0;
  virtual void logOr(Value* a, Value* b) = 0;
  virtual void bitwAnd(Value* a, Value* b) = 0;
  virtual void bitwOr(Value* a, Value* b) = 0;
  virtual void bitwXor(Value* a, Value* b) = 0;
  virtual void notEqual(Value* a, Value* b) = 0;
  virtual void shiftLeft(Value* a, Value* b) = 0;
  virtual void shiftRight(Value* a, Value* b) = 0;

 protected:
  unsigned int nbWords_(unsigned int size);
};

class SValue : public Value {
  friend LValue;

 public:
  SValue() {
    m_value = 0;
    m_size = 0;
  }
  SValue(unsigned long val) {
    m_value = val;
    m_size = 64;
  }
  SValue(long val) {
    m_value = val;
    m_size = 64;
  }
  SValue(double val) {
    m_value = (unsigned long)val;
    m_size = 64;
  }
  SValue(unsigned long val, unsigned short size) {
    m_value = val;
    m_size = size;
  }
  unsigned short getSize() { return m_size; }
  unsigned short getNbWords() { return 1; }
  bool isLValue() { return false; }
  ValueType getType() { return None; }
  void set(unsigned long val);
  void set(long val);
  void set(double val);
  void set(unsigned long val, ValueType type, unsigned short size);
  void set(std::string val) {
    m_value = 6969696969;
    m_size = 6969;
  }
  bool operator<(Value& rhs) {
    return m_value < (dynamic_cast<SValue*>(&rhs))->m_value;
  }
  bool operator==(Value& rhs) {
    return m_value == (dynamic_cast<SValue*>(&rhs))->m_value;
  }
  unsigned long getValueUL(unsigned short index = 0) { return m_value; }
  long getValueL(unsigned short index = 0) { return (long)m_value; }
  double getValueD(unsigned short index = 0) { return (double)m_value; }
  std::string getValueS() { return "NOT_A_STRING_VALUE"; }
  virtual ~SValue();

  void u_plus(Value* a);
  void u_minus(Value* a);
  void u_not(Value* a);
  void u_tilda(Value* a);
  void incr();
  void decr();
  void plus(Value* a, Value* b);
  void minus(Value* a, Value* b);
  void mult(Value* a, Value* b);
  void div(Value* a, Value* b);
  void mod(Value* a, Value* b);
  void greater(Value* a, Value* b);
  void greater_equal(Value* a, Value* b);
  void lesser(Value* a, Value* b);
  void lesser_equal(Value* a, Value* b);
  void equiv(Value* a, Value* b);
  void logAnd(Value* a, Value* b);
  void logOr(Value* a, Value* b);
  void bitwAnd(Value* a, Value* b);
  void bitwOr(Value* a, Value* b);
  void bitwXor(Value* a, Value* b);
  void notEqual(Value* a, Value* b);
  void shiftLeft(Value* a, Value* b);
  void shiftRight(Value* a, Value* b);

 private:
  unsigned long m_value;
  unsigned short m_size;
};

class ValueFactory {
 public:
  ValueFactory();
  Value* newSValue();
  Value* newLValue();
  Value* newStValue();
  Value* newValue(SValue& initVal);
  Value* newValue(LValue& initVal);
  Value* newValue(StValue& initVal);
  void deleteValue(Value*);

 protected:
  LValue* m_headFree;
  LValue* m_headInUse;
};

class LValue : public Value {
  friend ValueFactory;

 public:
  LValue(LValue&);
  LValue() {
    m_type = None;
    m_nbWords = 0;
    m_valueArray = NULL;
  }
  LValue(ValueType type, SValue* values, unsigned short nbWords) {
    m_type = type, m_valueArray = values;
    m_nbWords = nbWords;
  }
  LValue(unsigned long val);
  LValue(long val);
  LValue(double val);
  LValue(unsigned long val, ValueType type, unsigned short size);
  unsigned short getSize();
  unsigned short getNbWords() { return m_nbWords; }
  bool isLValue() { return true; }
  ValueType getType() { return (ValueType)m_type; }
  virtual ~LValue();

  void set(unsigned long val);
  void set(long val);
  void set(double val);
  void set(unsigned long val, ValueType type, unsigned short size);
  void set(std::string val) {}
  bool operator<(Value& rhs);
  bool operator==(Value& rhs);

  unsigned long getValueUL(unsigned short index = 0) {
    return ((index < m_nbWords) ? m_valueArray[index].m_value : 0);
  }
  long getValueL(unsigned short index = 0) {
    return ((index < m_nbWords) ? (long)m_valueArray[index].m_value : 0);
  }
  double getValueD(unsigned short index = 0) {
    return ((index < m_nbWords) ? (double)m_valueArray[index].m_value : 0);
  }
  std::string getValueS() { return "NOT_A_STRING_VALUE"; }
  void u_plus(Value* a);
  void u_minus(Value* a);
  void u_not(Value* a);
  void u_tilda(Value* a);
  void incr();
  void decr();
  void plus(Value* a, Value* b);
  void minus(Value* a, Value* b);
  void mult(Value* a, Value* b);
  void div(Value* a, Value* b);
  void mod(Value* a, Value* b);
  void greater(Value* a, Value* b);
  void greater_equal(Value* a, Value* b);
  void lesser(Value* a, Value* b);
  void lesser_equal(Value* a, Value* b);
  void equiv(Value* a, Value* b);
  void logAnd(Value* a, Value* b);
  void logOr(Value* a, Value* b);
  void bitwAnd(Value* a, Value* b);
  void bitwOr(Value* a, Value* b);
  void bitwXor(Value* a, Value* b);
  void notEqual(Value* a, Value* b);
  void shiftLeft(Value* a, Value* b);
  void shiftRight(Value* a, Value* b);

  void adjust(Value* a);

 private:
  unsigned short m_type;
  unsigned short m_nbWords;
  SValue* m_valueArray;
  LValue* m_prev;
  LValue* m_next;
};

class StValue : public Value {
  friend LValue;

 public:
  StValue() {
    m_value = "";
    m_size = 0;
  }
  StValue(std::string val) {
    m_value = val;
    m_size = val.size();
  }
  unsigned short getSize() { return m_size; }
  unsigned short getNbWords() { return 1; }
  bool isLValue() { return false; }
  ValueType getType() { return String; }
  void set(unsigned long val) { m_value = std::to_string(val); }
  void set(long val) { m_value = std::to_string(val); }
  void set(double val) { m_value = std::to_string(val); }
  void set(unsigned long val, ValueType type, unsigned short size) {
    m_value = std::to_string(val);
  }
  void set(std::string val) {
    m_value = val;
    m_size = val.size();
  }
  bool operator<(Value& rhs) {
    return m_value < (dynamic_cast<StValue*>(&rhs))->m_value;
  }
  bool operator==(Value& rhs) {
    return m_value == (dynamic_cast<StValue*>(&rhs))->m_value;
  }
  unsigned long getValueUL(unsigned short index = 0) {
    return atol(m_value.c_str());
  }
  long getValueL(unsigned short index = 0) {
    return (long)atol(m_value.c_str());
  }
  double getValueD(unsigned short index = 0) {
    return (double)atof(m_value.c_str());
  }
  std::string getValueS() { return m_value; }
  virtual ~StValue();

  void u_plus(Value* a) {}
  void u_minus(Value* a) {}
  void u_not(Value* a) {}
  void u_tilda(Value* a) {}
  void incr() {}
  void decr() {}
  void plus(Value* a, Value* b) {}
  void minus(Value* a, Value* b) {}
  void mult(Value* a, Value* b) {}
  void div(Value* a, Value* b) {}
  void mod(Value* a, Value* b) {}
  void greater(Value* a, Value* b) {}
  void greater_equal(Value* a, Value* b) {}
  void lesser(Value* a, Value* b) {}
  void lesser_equal(Value* a, Value* b) {}
  void equiv(Value* a, Value* b) {}
  void logAnd(Value* a, Value* b) {}
  void logOr(Value* a, Value* b) {}
  void bitwAnd(Value* a, Value* b) {}
  void bitwOr(Value* a, Value* b) {}
  void bitwXor(Value* a, Value* b) {}
  void notEqual(Value* a, Value* b) {}
  void shiftLeft(Value* a, Value* b) {}
  void shiftRight(Value* a, Value* b) {}

 private:
  std::string m_value;
  unsigned short m_size;
};

};  // namespace SURELOG

#endif /* VALUE_H */
