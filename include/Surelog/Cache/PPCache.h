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

#include "Surelog/Cache/Cache.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/SourceCompile/PreprocessFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"

namespace SURELOG {

class PPCache : Cache {
 public:
  PPCache(PreprocessFile* pp);

  bool restore(bool errorsOnly);
  bool save();

 private:
  PPCache(const PPCache& orig) = delete;

  std::filesystem::path getCacheFileName_(
      const std::filesystem::path& fileName = "");
  bool restore_(const std::filesystem::path& cacheFileName, bool errorsOnly);
  bool checkCacheIsValid_(const std::filesystem::path& cacheFileName);

  PreprocessFile* m_pp;
  bool m_isPrecompiled;
};

}  // namespace SURELOG

#endif /* SURELOG_PPCACHE_H */
