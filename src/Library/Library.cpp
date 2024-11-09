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
 * File:   Library.cpp
 * Author: alain
 *
 * Created on January 27, 2018, 5:25 PM
 */

#include "Surelog/Library/Library.h"

#include <string_view>

#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/SourceCompile/SymbolTable.h"

namespace SURELOG {

Library::Library(std::string_view name, SymbolTable* symbols)
    : m_nameId(symbols->registerSymbol(name)), m_symbols(symbols) {}

std::string_view Library::getName() const {
  return m_symbols->getSymbol(m_nameId);
}

void Library::addModuleDefinition(ModuleDefinition* def) {
  m_modules.emplace(m_symbols->registerSymbol(def->getName()), def);
}

ModuleDefinition* Library::getModule(std::string_view name) const {
  auto itr = m_modules.find(m_symbols->registerSymbol(name));
  return (itr == m_modules.end()) ? nullptr : itr->second;
}

std::ostream& Library::report(std::ostream& out) const {
  out << "LIB: " << m_symbols->getSymbol(m_nameId) << std::endl;
  for (const auto& id : m_fileIds) {
    out << "     " << PathIdPP(id) << std::endl;
  }
  return out;
}

}  // namespace SURELOG
