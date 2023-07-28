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
 * File:   Cache.h
 * Author: alain
 *
 * Created on April 28, 2017, 9:32 PM
 */

#ifndef SURELOG_CACHE_H
#define SURELOG_CACHE_H
#pragma once

#include <Surelog/Cache/Cache.capnp.h>
#include <Surelog/Common/PathId.h>
#include <Surelog/ErrorReporting/Error.h>

#include <string_view>
#include <vector>

namespace SURELOG {

class ErrorContainer;
class FileContent;
class SymbolTable;
class VObject;

// A cache class used as a base for various other caches persisting
// things in Cap'n'Proto.
// All methods are protected as they are meant for derived classes to use.
//
// The cache is storing a symbol table on disk; these typically only contain
// all the symbols that are exported.

class Cache {
 public:
  static constexpr uint64_t Capacity = 0x000000000FFFFFFF;

 protected:
  Cache() = default;

  std::string_view getExecutableTimeStamp() const;

  bool checkIfCacheIsValid(const Header::Reader& header,
                           std::string_view schemaVersion, PathId cacheFileId,
                           PathId sourceFileId) const;

  void cacheHeader(Header::Builder builder, std::string_view schemaVersion);

  void cacheErrors(
      ::capnp::List<::Error, ::capnp::Kind::STRUCT>::Builder targetErrors,
      SymbolTable& targetSymbols, const std::vector<Error>& sourceErrors,
      const SymbolTable& sourceSymbols);

  void cacheVObjects(
      ::capnp::List<::VObject, ::capnp::Kind::STRUCT>::Builder targetVObjects,
      SymbolTable& targetSymbols, const std::vector<VObject>& sourceVObjects,
      const SymbolTable& sourceSymbols);

  void cacheSymbols(
      ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Builder targetSymbols,
      const std::vector<std::string_view>& sourceSymbols);

  // Restores errors and the cache symbol table (to be used in other restore
  // operations).
  // References in the error container to local symbols will be entered into
  // the local symbol table.
  void restoreErrors(ErrorContainer* errorContainer, SymbolTable& targetSymbols,
                     const ::capnp::List<::Error>::Reader& sourceErrors,
                     const SymbolTable& sourceSymbols);

  // Restore objects coming from the flatbuffer cache and with the corresponding
  // "cacheSymbols" into "fileContent", with IDs relevant in the local
  // symbol table "localSymbols" (which is updated).
  void restoreVObjects(std::vector<VObject>& targetVObjects,
                       SymbolTable& targetSymbols,
                       const ::capnp::List<::VObject>::Reader& sourceVObjects,
                       const SymbolTable& sourceSymbols);

  void restoreSymbols(
      SymbolTable& targetSymbols,
      const ::capnp::List<::capnp::Text>::Reader& sourceSymbols);

 private:
  Cache(const Cache& orig) = delete;
};

}  // namespace SURELOG

#endif /* SURELOG_CACHE_H */
