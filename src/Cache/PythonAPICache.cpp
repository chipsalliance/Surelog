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
 * File:   PythonAPICache.cpp
 * Author: alain
 *
 * Created on May 28, 2017, 10:49 PM
 */

#include "Surelog/Cache/PythonAPICache.h"

#include <capnp/blob.h>
#include <capnp/common.h>
#include <capnp/list.h>
#include <capnp/message.h>
#include <capnp/serialize-packed.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "Surelog/API/PythonAPI.h"
#include "Surelog/Cache/Cache.capnp.h"
#include "Surelog/Cache/Cache.h"
#include "Surelog/Cache/PythonAPICache.capnp.h"
#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Library/Library.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/PreprocessFile.h"
#include "Surelog/SourceCompile/PythonListen.h"
#include "Surelog/SourceCompile/SymbolTable.h"

#if defined(_MSC_VER)
#include <io.h>
#else
#include <unistd.h>
#endif

#include <filesystem>
#include <limits>

namespace SURELOG {
static std::string_view kSchemaVersion = "1.1";

PythonAPICache::PythonAPICache(PythonListen* listener) : m_listener(listener) {}

PathId PythonAPICache::getCacheFileId(PathId sourceFileId) const {
  ParseFile* parseFile = m_listener->getParseFile();
  if (!sourceFileId) sourceFileId = parseFile->getFileId(LINE1);
  if (!sourceFileId) return BadPathId;

  FileSystem* const fileSystem = FileSystem::getInstance();
  CommandLineParser* clp =
      m_listener->getCompileSourceFile()->getCommandLineParser();
  SymbolTable* symbolTable =
      m_listener->getCompileSourceFile()->getSymbolTable();

  const std::string_view libName =
      m_listener->getCompileSourceFile()->getLibrary()->getName();
  return fileSystem->getPythonCacheFile(clp->fileunit(), sourceFileId, libName,
                                        symbolTable);
}

bool PythonAPICache::checkCacheIsValid(
    PathId cacheFileId, const ::PythonAPICache::Reader& root) const {
  FileSystem* const fileSystem = FileSystem::getInstance();
  const ::Header::Reader& sourceHeader = root.getHeader();

  SymbolTable* const targetSymbols =
      m_listener->getCompileSourceFile()->getSymbolTable();

  const std::string scriptFile(root.getScriptFile().cStr());
  const PathId scriptFileId =
      fileSystem->toPathId(fileSystem->remap(scriptFile), targetSymbols);

  std::filesystem::file_time_type ct = fileSystem->modtime(cacheFileId);
  std::filesystem::file_time_type ft = fileSystem->modtime(scriptFileId);

  if (ft == std::filesystem::file_time_type::min()) {
    return false;
  }
  if (ct == std::filesystem::file_time_type::min()) {
    return false;
  }
  if (ct < ft) {
    return false;
  }

  return checkIfCacheIsValid(sourceHeader, kSchemaVersion, cacheFileId,
                             m_listener->getParseFile()->getFileId(LINE1));
}

bool PythonAPICache::checkCacheIsValid(PathId cacheFileId) const {
  if (!cacheFileId) return false;

  FileSystem* const fileSystem = FileSystem::getInstance();
  const std::string filepath =
      fileSystem->toPlatformAbsPath(cacheFileId).string();

  const int32_t fd = ::open(filepath.c_str(), O_RDONLY | O_BINARY);
  if (fd < 0) return false;

  bool result = false;
  do {
    ::capnp::ReaderOptions options;
    options.traversalLimitInWords = std::numeric_limits<uint64_t>::max();
    options.nestingLimit = 1024;
    ::capnp::PackedFdMessageReader message(fd, options);
    const ::PythonAPICache::Reader& root = message.getRoot<::PythonAPICache>();
    result = checkCacheIsValid(cacheFileId, root);
  } while (false);

  ::close(fd);
  return result;
}

bool PythonAPICache::isValid() const {
  return checkCacheIsValid(getCacheFileId(BadPathId));
}

void PythonAPICache::cacheSymbols(::PythonAPICache::Builder builder,
                                  SymbolTable& sourceSymbols) {
  const std::vector<std::string_view> texts = sourceSymbols.getSymbols();
  ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Builder targetSymbols =
      builder.initSymbols(texts.size());
  Cache::cacheSymbols(targetSymbols, texts);
}

void PythonAPICache::cacheErrors(::PythonAPICache::Builder builder,
                                 SymbolTable& targetSymbols,
                                 const ErrorContainer* errorContainer,
                                 const SymbolTable& sourceSymbols,
                                 PathId subjectId) {
  std::vector<Error> sourceErrors;
  sourceErrors.reserve(errorContainer->getErrors().size());
  for (const Error& error : errorContainer->getErrors()) {
    for (const Location& loc : error.getLocations()) {
      if (loc.m_fileId == subjectId) {
        sourceErrors.emplace_back(error);
        break;
      }
    }
  }

  ::capnp::List<::Error, ::capnp::Kind::STRUCT>::Builder targetErrors =
      builder.initErrors(sourceErrors.size());
  Cache::cacheErrors(targetErrors, targetSymbols, sourceErrors, sourceSymbols);
}

bool PythonAPICache::restore() {
  CompileSourceFile* const csf = m_listener->getCompileSourceFile();
  CommandLineParser* const clp = csf->getCommandLineParser();
  if (!clp->cacheAllowed()) return false;

  PathId cacheFileId = getCacheFileId(BadPathId);
  if (!cacheFileId) return false;

  FileSystem* const fileSystem = FileSystem::getInstance();
  const std::string filepath =
      fileSystem->toPlatformAbsPath(cacheFileId).string();

  const int32_t fd = ::open(filepath.c_str(), O_RDONLY | O_BINARY);
  if (fd < 0) return false;

  bool result = true;
  do {
    ::capnp::ReaderOptions options;
    options.traversalLimitInWords = std::numeric_limits<uint64_t>::max();
    options.nestingLimit = 1024;
    ::capnp::PackedFdMessageReader message(fd, options);
    const ::PythonAPICache::Reader& root = message.getRoot<::PythonAPICache>();

    if (!checkCacheIsValid(cacheFileId, root)) {
      result = false;
      break;
    }

    SymbolTable sourceSymbols;
    SymbolTable* const targetSymbols =
        m_listener->getCompileSourceFile()->getSymbolTable();

    restoreSymbols(sourceSymbols, root.getSymbols());
    restoreErrors(csf->getErrorContainer(), *targetSymbols, root.getErrors(),
                  sourceSymbols);
  } while (false);

  ::close(fd);
  return result;
}

bool PythonAPICache::save() {
  CompileSourceFile* const csf = m_listener->getCompileSourceFile();
  ParseFile* const pf = m_listener->getParseFile();
  CommandLineParser* clp =
      m_listener->getCompileSourceFile()->getCommandLineParser();
  if (!clp->cacheAllowed()) return false;

  PathId cacheFileId = getCacheFileId(BadPathId);
  if (!cacheFileId) return false;

  FileSystem* const fileSystem = FileSystem::getInstance();
  ErrorContainer* const errorContainer = csf->getErrorContainer();
  SymbolTable* const sourceSymbols = csf->getSymbolTable();
  SymbolTable targetSymbols;

  ::capnp::MallocMessageBuilder message;
  ::PythonAPICache::Builder builder = message.initRoot<::PythonAPICache>();

  // Create header section
  cacheHeader(builder.getHeader(), kSchemaVersion);

  const std::string scriptFile = PythonAPI::getListenerScript();
  builder.setScriptFile(scriptFile.c_str());

  // Cache the errors and canonical symbols
  cacheErrors(builder, targetSymbols, errorContainer, *sourceSymbols,
              pf->getFileId(LINE1));

  // Cache symbols
  cacheSymbols(builder, targetSymbols);

  // Finally, save to disk
  PathId cacheDirId = fileSystem->getParent(cacheFileId, sourceSymbols);
  if (!fileSystem->mkdirs(cacheDirId)) return false;

  const std::string filepath =
      fileSystem->toPlatformAbsPath(cacheFileId).string();

  const int32_t fd = ::open(filepath.c_str(), O_RDONLY | O_BINARY);
  if (fd < 0) return false;

  writePackedMessageToFd(fd, message);
  ::close(fd);
  return true;
}
}  // namespace SURELOG
