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

#include "Surelog/Library/LibrarySet.h"

#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <string_view>

#include "Surelog/Common/PathId.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Library/Library.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Utils/StringUtils.h"

namespace SURELOG {

Library* LibrarySet::addLibrary(std::string_view name,
                                SymbolTable* symbolTable) {
  Library* lib = getLibrary(name);
  if (lib == nullptr) {
    lib = &m_libraries.emplace_back(name, symbolTable);
  }
  return lib;
}

Library* LibrarySet::getLibrary(std::string_view libName) {
  for (auto& library : m_libraries) {
    if (library.getName() == libName) return &library;
  }
  return nullptr;
}

Library* LibrarySet::getLibrary(PathId fileId) {
  Library* lib = nullptr;
  for (auto& library : m_libraries) {
    if (library.isMember(fileId)) {
      lib = &library;
      break;
    }
  }
  if (lib == nullptr) {
    lib = getLibrary("work");
    lib->addFileId(fileId);
  }
  return lib;
}

std::ostream& LibrarySet::report(std::ostream& out) const {
  for (const auto& library : m_libraries) {
    library.report(out) << std::endl;
  }
  return out;
}

void LibrarySet::checkErrors(SymbolTable* symbols,
                             ErrorContainer* errors) const {
  std::map<PathId, std::string, PathIdLessThanComparer> fileSet;
  for (const auto& library : m_libraries) {
    for (const auto& file : library.getFiles()) {
      auto itr = fileSet.find(file);
      if (itr == fileSet.end()) {
        fileSet.emplace(file, library.getName());
      } else {
        Location loc1(symbols->registerSymbol(
            StrCat(itr->second, ", ", library.getName())));
        Location loc2(file);
        Error err(ErrorDefinition::LIB_FILE_MAPS_TO_MULTIPLE_LIBS, loc1, loc2);
        errors->addError(err);
      }
    }
  }
}

}  // namespace SURELOG
