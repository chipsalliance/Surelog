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
 * File:   Expr.cpp
 * Author: alain
 *
 * Created on October 29, 2017, 10:21 PM
 */

#include "Expression/Expr.h"

using namespace SURELOG;

Expr::Expr(const Expr& orig) {}

Expr::~Expr() {}

ExprFactory::ExprFactory() {}

Expr* ExprFactory::newExpr() {
  Expr* expr = new Expr();
  expr->m_factory = this;
  return expr;
}

Expr* ExprFactory::newExpr(Value* val) {
  Expr* expr = new Expr(val);
  expr->m_factory = this;
  return expr;
}

Expr* ExprFactory::newExpr(Value* valL, Value* valR) {
  Expr* expr = new Expr(valL, valR);
  expr->m_factory = this;
  return expr;
}

void ExprFactory::deleteExpr(Expr* expr) { delete expr; }

Value* Expr::eval() {
  if (m_val && !m_valR) {
    return m_val;
  } else if (m_val && m_valR) {
    return NULL;
  }
  Value* val = m_factory->m_valueFactory.newSValue();
  return val;
}

std::pair<Value*, Value*> Expr::evalRange() {
  std::pair<Value*, Value*> result(NULL, NULL);
  if (m_type != Range) return result;
  std::pair<Value*, Value*> result2(m_val, m_valR);
  return result2;
}
