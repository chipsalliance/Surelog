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
 * File:   PathId.cpp
 * Author: HS
 *
 * Created on July 4, 2022, 1:30 AM
 */

#include <Surelog/Common/FileSystem.h>
#include <Surelog/Common/PathId.h>

namespace SURELOG {
std::ostream &operator<<(std::ostream &strm, const PathIdPP &id) {
  return strm << FileSystem::getInstance()->toPath(id.m_id);
}

bool PathId::operator==(const PathId &rhs) const {
  // IMPORTANT: The logic to compare two PathId instances cannot use
  // std::filesystem::equivalent (or FileSystem::areEquivalent) since those
  // API expects both the paths to exist. PathId doesn't have the same
  // restriction or guarantee. String comparison is the only viable option
  // and potentially good enough since the paths stored in the SymbolTable are
  // expected to be *normalized*.
  if ((m_id == rhs.m_id) && (m_symbolTable == rhs.m_symbolTable)) {
    return true;
  }

  if ((m_symbolTable != nullptr) && (rhs.m_symbolTable != nullptr) &&
      (m_id != BadRawPathId) && (rhs.m_id != BadRawPathId)) {
    FileSystem *const fileSystem = FileSystem::getInstance();
    return fileSystem->toPath(*this) == fileSystem->toPath(rhs);
  }

  return false;
}
}  // namespace SURELOG
