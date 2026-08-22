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
 * File:   LibrarySet.h
 * Author: alain
 *
 * Created on January 27, 2018, 5:28 PM
 */

#ifndef SURELOG_LIBRARYSET_H
#define SURELOG_LIBRARYSET_H
#pragma once

#include <Surelog/Common/PathId.h>
// Library must be complete here: std::deque -- unlike std::vector -- is not
// one of the containers the standard allows to instantiate with an incomplete
// element type, and MSVC's implementation takes sizeof(Library) eagerly.
#include <Surelog/Library/Library.h>

#include <deque>
#include <ostream>
#include <string_view>

namespace SURELOG {

class ErrorContainer;
class SymbolTable;

class LibrarySet final {
 public:
  LibrarySet() = default;

  Library* addLibrary(std::string_view name, SymbolTable* symbolTable);
  std::deque<Library>& getLibraries() { return m_libraries; }
  Library* getLibrary(std::string_view libName);
  Library* getLibrary(PathId fileId);
  void checkErrors(SymbolTable* symbols, ErrorContainer* errors) const;
  std::ostream& report(std::ostream& out) const;

 private:
  LibrarySet(const LibrarySet& orig) = default;
  // A deque (not a vector) so that Library* pointers handed out by
  // addLibrary()/getLibrary() stay valid when a later library is added -- a
  // library map file may recursively parse a nested .map/.cfg that appends
  // more libraries while an earlier Library* is still in use.
  std::deque<Library> m_libraries;
};

}  // namespace SURELOG

#endif /* SURELOG_LIBRARYSET_H */
