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
 * File:   LibrarySet.cpp
 * Author: alain
 *
 * Created on January 27, 2018, 5:28 PM
 */

#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/Library/Library.h>
#include <Surelog/Library/LibrarySet.h>
#include <Surelog/SourceCompile/SymbolTable.h>

namespace SURELOG {

void LibrarySet::addLibrary(const Library& lib) {
  m_libraries.emplace_back(lib);
}

Library* LibrarySet::getLibrary(std::string_view libName) {
  for (auto& library : m_libraries) {
    if (library.getName() == libName) return &library;
  }
  return nullptr;
}

Library* LibrarySet::getLibrary(SymbolId fileId) {
  Library* lib = nullptr;
  for (auto& library : m_libraries) {
    if (library.isMember(fileId)) {
      lib = &library;
      break;
    }
  }
  if (lib == nullptr) {
    getLibrary("work")->addFileId(fileId);
    lib = getLibrary("work");
  }
  return lib;
}

std::string LibrarySet::report(SymbolTable* symbols) const {
  std::string report;
  for (const auto& library : m_libraries) {
    report += library.report(symbols) + "\n";
  }
  return report;
}

void LibrarySet::checkErrors(SymbolTable* symbols,
                             ErrorContainer* errors) const {
  std::map<SymbolId, std::string, SymbolIdLessThanComparer> fileSet;
  for (const auto& library : m_libraries) {
    for (const auto& file : library.getFiles()) {
      std::map<SymbolId, std::string>::iterator itr = fileSet.find(file);
      if (itr == fileSet.end()) {
        fileSet.insert(std::make_pair(file, library.getName()));
      } else {
        Location loc1(
            symbols->registerSymbol((*itr).second + ", " + library.getName()));
        Location loc2(file);
        Error err(ErrorDefinition::LIB_FILE_MAPS_TO_MULTIPLE_LIBS, loc1, loc2);
        errors->addError(err);
      }
    }
  }
}

}  // namespace SURELOG
