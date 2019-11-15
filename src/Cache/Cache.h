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
#include "header_generated.h"
#include <cstdio>  // For printing and file access.

namespace SURELOG {

class Cache {
 public:
  Cache();
  Cache(const Cache& orig);
  virtual ~Cache();
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
  std::pair<flatbuffers::Offset<flatbuffers::Vector<
                flatbuffers::Offset<SURELOG::CACHE::Error>>>,
            flatbuffers::Offset<
                flatbuffers::Vector<flatbuffers::Offset<flatbuffers::String>>>>
  cacheErrors(flatbuffers::FlatBufferBuilder& builder,
              SymbolTable& canonicalSymbols, ErrorContainer* errorContainer,
              SymbolTable* symbols, SymbolId subjectId);
  void restoreErrors(
      const flatbuffers::Vector<flatbuffers::Offset<SURELOG::CACHE::Error>>*
          errorsBuf,
      const flatbuffers::Vector<flatbuffers::Offset<flatbuffers::String>>*
          symbolBuf,
      SymbolTable& canonicalSymbols, ErrorContainer* errorContainer,
      SymbolTable* symbols);
};

};  // namespace SURELOG

#endif /* CACHE_H */
