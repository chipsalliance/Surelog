
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
 * File:   SymbolTable.h
 * Author: alain
 *
 * Created on March 6, 2017, 11:10 PM
 */

#ifndef SURELOG_SYMBOLTABLE_H
#define SURELOG_SYMBOLTABLE_H
#pragma once

#include <uhdm/SymbolFactory.h>

namespace SURELOG {
class SymbolTable final : public UHDM::SymbolFactory {
 public:
  // Create a snapshot of this symbol table. The returned SymbolTable contains
  // all the symbols this table has and allows to then continue using the new
  // copy without changing the original. Essentially a fork.
  // TODO: at some point, return std::unique_ptr<>
  SymbolTable* CreateSnapshot() const { return new SymbolTable(*this); }

 public:
  SymbolTable() = default;
  SymbolTable& operator=(const SymbolTable&) = delete;
  SymbolTable(SymbolTable&& s) = delete;
  SymbolTable& operator=(SymbolTable&&) = delete;

 private:
  // Create a snapshot of the current symbol table. Private, as this
  // functionality should be explicitly accessed through CreateSnapshot().
  SymbolTable(const SymbolTable& parent) : SymbolFactory(parent) {}
};
}  // namespace SURELOG

#endif /* SURELOG_SYMBOLTABLE_H */
