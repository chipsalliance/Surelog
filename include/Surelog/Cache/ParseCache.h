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
 * File:   ParseCache.h
 * Author: alain
 *
 * Created on April 29, 2017, 4:20 PM
 */

#ifndef SURELOG_PARSECACHE_H
#define SURELOG_PARSECACHE_H
#pragma once

#include <Surelog/Cache/Cache.h>
#include <Surelog/Cache/ParseCache.capnp.h>
#include <Surelog/Common/PathId.h>
#include <capnp/list.h>

namespace SURELOG {

class ParseFile;

class ParseCache final : Cache {
 public:
  explicit ParseCache(ParseFile* pp);
  ParseCache(const ParseCache& orig) = delete;

  bool restore();
  bool save();
  bool isValid();

 private:
  PathId getCacheFileId(PathId ppFileId) const;

  bool checkCacheIsValid(PathId cacheFileId,
                         const ::ParseCache::Reader& root) const;
  bool checkCacheIsValid(PathId cacheFileId) const;

  // Store symbols in cache.
  void cacheSymbols(::ParseCache::Builder builder, SymbolTable& sourceSymbols);

  // Store errors in cache. Canonicalize strings and store in "targetSymbols".
  void cacheErrors(::ParseCache::Builder builder, SymbolTable& targetSymbols,
                   const ErrorContainer* errorContainer,
                   const SymbolTable& sourceSymbols, PathId subjectId);

  // Convert vobjects from "fcontent" into cachable VObjects.
  // Uses "sourceSymbols" and "targetSymbols" to map symbols found in "fC"
  // to IDs used on the cache on disk.
  // Updates "targetSymbols" if new IDs are needed.
  void cacheVObjects(::ParseCache::Builder builder, const FileContent* fC,
                     SymbolTable& targetSymbols,
                     const SymbolTable& sourceSymbols, PathId fileId);

  void cacheDesignElements(::ParseCache::Builder builder, const FileContent* fC,
                           SymbolTable& targetSymbols,
                           const SymbolTable& sourceSymbols);

  bool restore(PathId cacheFileId);

  void restoreDesignElements(
      FileContent* fC, SymbolTable& targetSymbols,
      const ::capnp::List< ::DesignElement, ::capnp::Kind::STRUCT>::Reader&
          sourceDesignElements,
      const SymbolTable& sourceSymbols);

 private:
  ParseFile* const m_parse = nullptr;
};

}  // namespace SURELOG

#endif /* SURELOG_PARSECACHE_H */
