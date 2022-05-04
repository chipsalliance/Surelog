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

#include <Surelog/Cache/header_generated.h>
#include <Surelog/Common/SymbolId.h>
#include <flatbuffers/flatbuffers.h>

#include <filesystem>
#include <memory>

namespace SURELOG {

class ErrorContainer;
class FileContent;
class SymbolTable;

// A cache class used as a base for various other cashes persisting
// things in flatbuffers.
// All methods are protected as they are ment for derived classes to use.
//
// The cache is storing a symbol table on disk, which we call "cacheSymbols";
// these typically only contain all the symbols that are exported.
// The "localSymbols" in the process will differ from "cacheSymbols" as it
// typically contains more.
class Cache {
 public:
  static constexpr uint64_t Capacity = 0x000000000FFFFFFF;

 protected:
  using VectorOffsetError =
      flatbuffers::Vector<flatbuffers::Offset<SURELOG::CACHE::Error>>;
  using VectorOffsetString =
      flatbuffers::Vector<flatbuffers::Offset<flatbuffers::String>>;

  Cache() = default;

  time_t get_mtime(const std::filesystem::path& path);

  const std::string& getExecutableTimeStamp();

  // Open file and read contents into a buffer.
  std::unique_ptr<uint8_t[]> openFlatBuffers(const std::filesystem::path& cacheFileName);

  bool saveFlatbuffers(flatbuffers::FlatBufferBuilder& builder,
                       const std::filesystem::path& cacheFileName);

  bool checkIfCacheIsValid(const SURELOG::CACHE::Header* header,
                           std::string_view schemaVersion,
                           const std::filesystem::path& cacheFileName);

  flatbuffers::Offset<SURELOG::CACHE::Header> createHeader(
      flatbuffers::FlatBufferBuilder& builder, std::string_view schemaVersion,
      const std::filesystem::path& origFileName);

  // Store errors in cache. Canonicalize strings and store in "cacheSymbols".
  flatbuffers::Offset<VectorOffsetError>
  cacheErrors(flatbuffers::FlatBufferBuilder& builder,
              SymbolTable* cacheSymbols,
              const ErrorContainer* errorContainer,
              const SymbolTable& localSymbols, SymbolId subjectId);

  // Given the symbol table (that we've accumulated while emitting cached
  // items), convert it to a flatbuffer cache vector.
  flatbuffers::Offset<Cache::VectorOffsetString> createSymbolCache(
    flatbuffers::FlatBufferBuilder& builder,
    const SymbolTable &cacheSymbols);

  // Restores errors and the cache symbol table (to be used in other restore
  // operations).
  // References in the error container to local symbols will be entered into
  // the local symbol table.
  void restoreErrors(const VectorOffsetError* errorsBuf,
                     const VectorOffsetString* symbolBuf,
                     SymbolTable* cacheSymbols,
                     ErrorContainer* errorContainer,
                     SymbolTable* localSymbols);

  // Convert vobjects from "fcontent" into cachable VObjects.
  // Uses "localSymbols" and "cacheSymbols" to map symbols found in "fcontent"
  // to IDs used on the cache on disk.
  // Updates "cacheSymbols" if new IDs are needed.
  std::vector<CACHE::VObject> cacheVObjects(const FileContent* fcontent,
                                            SymbolTable* cacheSymbols,
                                            const SymbolTable& localSymbols,
                                            SymbolId fileId);

  // Restore objects coming from the flatbuffer cache and with the corresponding
  // "cacheSymbols" into "fileContent", with IDs relevant in the local
  // symbol table "localSymbols" (which is updated).
  void restoreVObjects(
      const flatbuffers::Vector<const SURELOG::CACHE::VObject*>* objects,
      const SymbolTable& cacheSymbols,
      SymbolTable* localSymbols, SymbolId fileId,
      FileContent* fileContent);

 private:
  Cache(const Cache& orig) = delete;
};

}  // namespace SURELOG

#endif /* SURELOG_CACHE_H */
