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
#include <uhdm/uhdm_forward_decl.h>
#include <uhdm/containers.h>

#include <map>
#include <string>

namespace SURELOG {

class FileContent;

class LetStmt final {
 public:
  LetStmt(UHDM::let_decl* decl, UHDM::VectorOfseq_formal_decl* ios, UHDM::expr* expr) : m_decl(decl), m_ios(ios), m_expr(expr) {}
  ~LetStmt() = default;
  const UHDM::let_decl* Decl() { return m_decl; }
  const UHDM::VectorOfseq_formal_decl* Ios() { return m_ios; }
  const UHDM::expr* Expr() { return m_expr; }
 private:
  UHDM::let_decl* m_decl;
  UHDM::VectorOfseq_formal_decl* m_ios;
  UHDM::expr* m_expr;
};

}  // namespace SURELOG

#endif /* SURELOG_LETSTMT_H */
