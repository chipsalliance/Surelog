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
 * File:   PPCache.h
 * Author: alain
 *
 * Created on April 23, 2017, 8:49 PM
 */

#ifndef SURELOG_PPCACHE_H
#define SURELOG_PPCACHE_H
#pragma once

#include <Surelog/Cache/Cache.capnp.h>
#include <Surelog/Cache/Cache.h>
#include <Surelog/Cache/PPCache.capnp.h>
#include <Surelog/Common/PathId.h>
#include <capnp/list.h>

#include <cstdint>

namespace SURELOG {

class PreprocessFile;

class PPCache : Cache {
 public:
  explicit PPCache(PreprocessFile* pp);
  PPCache(const PPCache& orig) = delete;

  bool restore(bool errorsOnly);
  bool save();
  bool isValid();

 private:
  PathId getCacheFileId(PathId sourceFileId) const;

  bool checkCacheIsValid(PathId cacheFileId,
                         const ::PPCache::Reader& root) const;
  bool checkCacheIsValid(PathId cacheFileId) const;

  // Store symbols in cache.
  void cacheSymbols(::PPCache::Builder builder, SymbolTable& sourceSymbols);

  // Store errors in cache. Canonicalize strings and store in "targetSymbols".
  void cacheErrors(::PPCache::Builder builder, SymbolTable& targetSymbols,
                   const ErrorContainer* errorContainer,
                   const SymbolTable& sourceSymbols, PathId subjectId);

  // Convert vobjects from "fcontent" into cachable VObjects.
  // Uses "sourceSymbols" and "targetSymbols" to map symbols found in "fC"
  // to IDs used on the cache on disk.
  // Updates "targetSymbols" if new IDs are needed.
  void cacheVObjects(::PPCache::Builder builder, const FileContent* fC,
                     SymbolTable& targetSymbols,
                     const SymbolTable& sourceSymbols, PathId fileId);

  // Store macros in cache. Canonicalize strings and store in "targetSymbols".
  void cacheMacros(::PPCache::Builder builder, SymbolTable& targetSymbols,
                   const SymbolTable& sourceSymbols);

  void cacheDefines(::PPCache::Builder builder, SymbolTable& targetSymbols,
                    const SymbolTable& sourceSymbols);

  void cacheTimeInfos(::PPCache::Builder builder, SymbolTable& targetSymbols,
                      const SymbolTable& sourceSymbols);

  void cacheLineTranslationInfos(::PPCache::Builder builder,
                                 SymbolTable& targetSymbols,
                                 const SymbolTable& sourceSymbols);

  void cacheIncludeFileInfos(::PPCache::Builder builder,
                             SymbolTable& targetSymbols,
                             const SymbolTable& sourceSymbols);

  bool restore(PathId cacheFileId, bool errorsOnly, int32_t recursionDepth);

  void restoreMacros(SymbolTable& targetSymbols,
                     const ::capnp::List<::Macro>::Reader& sourceMacros,
                     const SymbolTable& sourceSymbols);

  void restoreTimeInfos(
      SymbolTable& targetSymbols,
      const ::capnp::List<::TimeInfo>::Reader& sourceTimeInfos,
      const SymbolTable& sourceSymbols);

  void restoreLineTranslationInfos(
      SymbolTable& targetSymbols,
      const ::capnp::List<::LineTranslationInfo>::Reader&
          sourceLineTranslationInfos,
      const SymbolTable& sourceSymbols);

  void restoreIncludeFileInfos(
      SymbolTable& targetSymbols,
      const ::capnp::List<::IncludeFileInfo>::Reader& sourceIncludeFileInfos,
      const SymbolTable& sourceSymbols);

 private:
  PreprocessFile* const m_pp = nullptr;
};

}  // namespace SURELOG

#endif /* SURELOG_PPCACHE_H */
