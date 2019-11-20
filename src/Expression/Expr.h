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
 * File:   Expr.h
 * Author: alain
 *
 * Created on October 29, 2017, 10:21 PM
 */

#ifndef EXPR_H
#define EXPR_H
#include <string>
#include "Expression/Value.h"

namespace SURELOG {

class ExprFactory;
class ExprBuilder;

class Expr {
 public:
  friend ExprFactory;
  Expr()
      : m_val(NULL),
        m_valR(NULL),
        m_leftExpr(NULL),
        m_rightExpr(NULL),
        m_type(None) {}
  Expr(Value* val)
      : m_val(val),
        m_valR(NULL),
        m_leftExpr(NULL),
        m_rightExpr(NULL),
        m_type(Scalar) {}
  Expr(Value* valL, Value* valR)
      : m_val(valL),
        m_valR(valR),
        m_leftExpr(NULL),
        m_rightExpr(NULL),
        m_type(Range) {}
  Expr(const Expr& orig);
  typedef enum {
    None,
    Scalar,
    Range,
    Add,
    Minus,
    Mult,
    Div,
    Modulo,
    Neg
  } ExprType;

  Expr* makeExpr(Expr* leftExpr, Expr* rightExpr, ExprType type) {
    m_leftExpr = leftExpr;
    m_rightExpr = rightExpr;
    m_type = type;
    return this;
  }
  ExprType getType() { return m_type; }
  Value* eval();
  std::pair<Value*, Value*> evalRange();
  virtual ~Expr();

 private:
  Value* m_val;
  Value* m_valR;
  Expr* m_leftExpr;
  Expr* m_rightExpr;
  ExprType m_type;
  ExprFactory* m_factory;
};

class ExprFactory {
 public:
  friend Expr;
  friend ExprBuilder;
  ExprFactory();

  Expr* newExpr();
  Expr* newExpr(Value* val);
  Expr* newExpr(Value* valL, Value* valR);

  void deleteExpr(Expr*);

 private:
  ValueFactory m_valueFactory;
};

};  // namespace SURELOG

#endif /* EXPR_H */
