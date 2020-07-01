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

#ifndef CACHE_H
#define CACHE_H

#include "flatbuffers/flatbuffers.h"
#include "Cache/header_generated.h"
#include <cstdio>  // For printing and file access.

namespace SURELOG {

// A cache class used as a base for various other cashes persisting
// things in flatbuffers.
// All methods are protected as they are ment for derived classes to use.
class Cache {
protected:
  using VectorOffsetError = flatbuffers::Vector<
    flatbuffers::Offset<SURELOG::CACHE::Error>>;
  using VectorOffsetString = flatbuffers::Vector<
    flatbuffers::Offset<flatbuffers::String>>;

  Cache() = default;

  time_t get_mtime(const char* path);

  std::string getExecutableTimeStamp();

  uint8_t* openFlatBuffers(std::string cacheFileName);

  bool saveFlatbuffers(flatbuffers::FlatBufferBuilder& builder,
                       std::string cacheFileName);

  bool checkIfCacheIsValid(const SURELOG::CACHE::Header* header,
                           std::string schemaVersion,
                           std::string cacheFileName);

  const flatbuffers::Offset<SURELOG::CACHE::Header> createHeader(
    flatbuffers::FlatBufferBuilder& builder, std::string schemaVersion,
    std::string origFileName);

  std::pair<flatbuffers::Offset<VectorOffsetError>,
            flatbuffers::Offset<VectorOffsetString>>
  cacheErrors(flatbuffers::FlatBufferBuilder& builder,
              SymbolTable& canonicalSymbols, ErrorContainer* errorContainer,
              SymbolTable* symbols, SymbolId subjectId);

  void restoreErrors(
    const VectorOffsetError* errorsBuf,
    const VectorOffsetString* symbolBuf,
    SymbolTable& canonicalSymbols, ErrorContainer* errorContainer,
    SymbolTable* symbols);

  std::vector<CACHE::VObject>
  cacheVObjects(FileContent* fcontent, SymbolTable& canonicalSymbols,
                SymbolTable& fileTable, SymbolId fileId);

  void restoreVObjects(
    const flatbuffers::Vector<const SURELOG::CACHE::VObject*>* objects,
    SymbolTable& canonicalSymbols,
    SymbolTable& fileTable,
    SymbolId fileId,
    FileContent* fileContent);

private:
  Cache(const Cache& orig) = delete;
};

}  // namespace SURELOG

#endif /* CACHE_H */
