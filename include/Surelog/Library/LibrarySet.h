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

#include <Surelog/Common/SymbolId.h>

#include <string_view>
#include <vector>

namespace SURELOG {

class ErrorContainer;
class Library;
class SymbolTable;

class LibrarySet final {
 public:
  LibrarySet() = default;

  void addLibrary(const Library& lib);
  std::vector<Library>& getLibraries() { return m_libraries; }
  Library* getLibrary(std::string_view libName);
  Library* getLibrary(SymbolId fileId);
  void checkErrors(SymbolTable* symbols, ErrorContainer* errors) const;
  std::string report(SymbolTable* symbols) const;

 private:
  LibrarySet(const LibrarySet& orig) = default;
  std::vector<Library> m_libraries;
};

}  // namespace SURELOG

#endif /* SURELOG_LIBRARYSET_H */
