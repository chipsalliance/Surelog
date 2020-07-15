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
#include <vector>
#include <set>
#include <iostream>
#include "SourceCompile/SymbolTable.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Library/LibrarySet.h"

using namespace SURELOG;

LibrarySet::LibrarySet() {}

Library* LibrarySet::getLibrary(std::string_view libName) {
  for (unsigned int i = 0; i < m_libraries.size(); i++) {
    if (m_libraries[i].getName() == libName) return &m_libraries[i];
  }
  return NULL;
}

Library* LibrarySet::getLibrary(SymbolId fileId) {
  Library* lib = NULL;
  for (unsigned int i = 0; i < m_libraries.size(); i++) {
    if (m_libraries[i].isMember(fileId)) {
      lib = &m_libraries[i];
      break;
    }
  }
  if (lib == NULL) {
    getLibrary("work")->addFileId(fileId);
    lib = getLibrary("work");
  }
  return lib;
}

std::string LibrarySet::report(SymbolTable* symbols) {
  std::string report;
  for (unsigned int i = 0; i < m_libraries.size(); i++) {
    report += m_libraries[i].report(symbols) + "\n";
  }
  return report;
}

void LibrarySet::checkErrors(SymbolTable* symbols, ErrorContainer* errors) {
  std::map<SymbolId, std::string> fileSet;
  for (unsigned int i = 0; i < m_libraries.size(); i++) {
    for (auto file : m_libraries[i].getFiles()) {
      std::map<SymbolId, std::string>::iterator itr = fileSet.find(file);
      if (itr == fileSet.end()) {
        fileSet.insert(std::make_pair(file, m_libraries[i].getName()));
      } else {
        Location loc1(symbols->registerSymbol((*itr).second + ", " +
                                              m_libraries[i].getName()));
        Location loc2(file);
        Error err(ErrorDefinition::LIB_FILE_MAPS_TO_MULTIPLE_LIBS, loc1, loc2);
        errors->addError(err);
      }
    }
  }
}
