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
 * File:   SymbolId.cpp
 * Author: HS
 *
 * Created on July 4, 2022, 1:30 AM
 */

#include <Surelog/Common/SymbolId.h>
#include <Surelog/SourceCompile/SymbolTable.h>

namespace SURELOG {
inline std::ostream &operator<<(std::ostream &strm, const SymbolIdPP &id) {
  return strm << id.symbolTable->getSymbol(id.id);
}
}  // namespace SURELOG
