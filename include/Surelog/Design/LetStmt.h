/*
 Copyright 2022 Alain Dargelas

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
 * File:   LetStmt.h
 * Author: alain
 *
 * Created on April 4, 2022, 10:00 PM
 */

#ifndef SURELOG_LETSTMT_H
#define SURELOG_LETSTMT_H
#pragma once

#include <Surelog/Common/SymbolId.h>

// UHDM
#include <uhdm/containers.h>
#include <uhdm/uhdm_forward_decl.h>

#include <map>
#include <string>

namespace SURELOG {

class FileContent;

class LetStmt final {
 public:
  LetStmt(uhdm::LetDecl* decl, uhdm::SeqFormalDeclCollection* ios,
          uhdm::Expr* expr)
      : m_decl(decl), m_ios(ios), m_expr(expr) {}
  ~LetStmt() = default;
  const uhdm::LetDecl* getDecl() { return m_decl; }
  const uhdm::SeqFormalDeclCollection* getIos() { return m_ios; }
  const uhdm::Expr* getExpr() { return m_expr; }

 private:
  uhdm::LetDecl* const m_decl = nullptr;
  uhdm::SeqFormalDeclCollection* const m_ios = nullptr;
  uhdm::Expr* const m_expr = nullptr;
};

}  // namespace SURELOG

#endif /* SURELOG_LETSTMT_H */
