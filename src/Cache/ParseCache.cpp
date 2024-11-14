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
 * File:   ParseCache.cpp
 * Author: alain
 *
 * Created on April 29, 2017, 4:20 PM
 */

#include "Surelog/Cache/ParseCache.h"

#include <capnp/blob.h>
#include <capnp/list.h>
#include <capnp/serialize-packed.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/SumbolId.h"
#include "Surelog/Design/Design.h"
#include "Surelog/Design/DesignElement.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/VObject.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Package/Precompiled.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Utils/StringUtils.h"
#include "Surelog/config.h"

#if defined(_MSC_VER)
#include <io.h>
#else
#include <unistd.h>
#endif

#include <filesystem>
#include <iostream>
#include <limits>

namespace SURELOG {
static constexpr char kSchemaVersion[] = "1.4";
static constexpr std::string_view UnknownRawPath = "<unknown>";

ParseCache::ParseCache(ParseFile* parser) : m_parse(parser) {}

PathId ParseCache::getCacheFileId(PathId ppFileId) const {
  if (!ppFileId) ppFileId = m_parse->getPpFileId();
  if (!ppFileId) return BadPathId;

  FileSystem* const fileSystem = FileSystem::getInstance();
  CommandLineParser* clp =
      m_parse->getCompileSourceFile()->getCommandLineParser();
  SymbolTable* const symbolTable =
      m_parse->getCompileSourceFile()->getSymbolTable();

  const std::string_view libName = m_parse->getLibrary()->getName();

  if (clp->parseOnly()) {
    // If parseOnly flag is set, the Preprocessor doesn't actually generate
    // an output file. Instead it uses the source itself i.e. from the original
    // source location. Compute the "potential" Preprocessor output file so the
    // cache file location would be correct.
    ppFileId = fileSystem->getPpOutputFile(clp->fileunit(), ppFileId, libName,
                                           symbolTable);
  }

  Precompiled* const prec = Precompiled::getSingleton();
  const bool isPrecompiled = prec->isFilePrecompiled(ppFileId, symbolTable);

  return fileSystem->getParseCacheFile(clp->fileunit(), ppFileId, libName,
                                       isPrecompiled, symbolTable);
}

bool ParseCache::checkCacheIsValid(PathId cacheFileId,
                                   const ::ParseCache::Reader& root) const {
  const ::Header::Reader& sourceHeader = root.getHeader();

  SymbolTable* const symbolTable =
      m_parse->getCompileSourceFile()->getSymbolTable();
  Precompiled* const prec = Precompiled::getSingleton();

  if (prec->isFilePrecompiled(m_parse->getPpFileId(), symbolTable)) {
    // For precompiled, check only the signature & version (so using
    // BadPathId instead of the actual arguments)
    return checkIfCacheIsValid(sourceHeader, kSchemaVersion, BadPathId,
                               BadPathId);
  } else {
    return checkIfCacheIsValid(sourceHeader, kSchemaVersion, cacheFileId,
                               m_parse->getPpFileId());
  }
}

bool ParseCache::checkCacheIsValid(PathId cacheFileId) const {
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
    const ::ParseCache::Reader& root = message.getRoot<::ParseCache>();
    result = checkCacheIsValid(cacheFileId, root);
  } while (false);

  ::close(fd);
  return result;
}

bool ParseCache::isValid() {
  return checkCacheIsValid(getCacheFileId(BadPathId));
}

void ParseCache::cacheSymbols(::ParseCache::Builder builder,
                              SymbolTable& sourceSymbols) {
  const std::vector<std::string_view> texts = sourceSymbols.getSymbols();
  ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Builder targetSymbols =
      builder.initSymbols(texts.size());
  Cache::cacheSymbols(targetSymbols, texts);
}

void ParseCache::cacheErrors(::ParseCache::Builder builder,
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

void ParseCache::cacheVObjects(::ParseCache::Builder builder,
                               const FileContent* fC,
                               SymbolTable& targetSymbols,
                               const SymbolTable& sourceSymbols,
                               PathId fileId) {
  const std::vector<VObject>& sourceVObjects = fC->getVObjects();
  ::capnp::List<::VObject, ::capnp::Kind::STRUCT>::Builder targetVObjects =
      builder.initObjects(sourceVObjects.size());
  Cache::cacheVObjects(targetVObjects, targetSymbols, sourceVObjects,
                       sourceSymbols);
}

void ParseCache::cacheDesignElements(::ParseCache::Builder builder,
                                     const FileContent* fC,
                                     SymbolTable& targetSymbols,
                                     const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  const std::vector<DesignElement*>& sourceDesignElements =
      fC->getDesignElements();
  ::capnp::List<::DesignElement, ::capnp::Kind::STRUCT>::Builder
      targetDesignElements = builder.initElements(sourceDesignElements.size());

  for (size_t i = 0, ni = sourceDesignElements.size(); i < ni; ++i) {
    const DesignElement* sourceDesignElement = sourceDesignElements[i];
    const TimeInfo& sourceTimeInfo = sourceDesignElement->m_timeInfo;

    ::DesignElement::Builder targetDesignElement = targetDesignElements[i];
    ::TimeInfo::Builder targetTimeInfo = targetDesignElement.initTimeInfo();

    targetTimeInfo.setType(static_cast<uint16_t>(sourceTimeInfo.m_type));
    targetTimeInfo.setFileId(
        (RawPathId)fileSystem->copy(sourceTimeInfo.m_fileId, &targetSymbols));
    targetTimeInfo.setLine(sourceTimeInfo.m_line);
    targetTimeInfo.setTimeUnit(
        static_cast<uint16_t>(sourceTimeInfo.m_timeUnit));
    targetTimeInfo.setTimeUnitValue(sourceTimeInfo.m_timeUnitValue);
    targetTimeInfo.setTimePrecision(
        static_cast<uint16_t>(sourceTimeInfo.m_timePrecision));
    targetTimeInfo.setTimePrecisionValue(sourceTimeInfo.m_timePrecisionValue);

    targetDesignElement.setName((RawSymbolId)targetSymbols.copyFrom(
        sourceDesignElement->m_name, &sourceSymbols));
    targetDesignElement.setFileId((RawPathId)fileSystem->copy(
        sourceDesignElement->m_fileId, &targetSymbols));
    targetDesignElement.setType(sourceDesignElement->m_type);
    targetDesignElement.setUniqueId((RawNodeId)sourceDesignElement->m_uniqueId);
    targetDesignElement.setLine(sourceDesignElement->m_line);
    targetDesignElement.setColumn(sourceDesignElement->m_column);
    targetDesignElement.setEndLine(sourceDesignElement->m_endLine);
    targetDesignElement.setEndColumn(sourceDesignElement->m_endColumn);
    targetDesignElement.setParent((RawNodeId)sourceDesignElement->m_parent);
    targetDesignElement.setNode((RawNodeId)sourceDesignElement->m_node);
    targetDesignElement.setDefaultNetType(
        static_cast<uint32_t>(sourceDesignElement->m_defaultNetType));
  }
}

void ParseCache::restoreDesignElements(
    FileContent* fC, SymbolTable& targetSymbols,
    const ::capnp::List<::DesignElement, ::capnp::Kind::STRUCT>::Reader&
        sourceDesignElements,
    const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = FileSystem::getInstance();

  for (const ::DesignElement::Reader& sourceElement : sourceDesignElements) {
    const std::string_view elemName = sourceSymbols.getSymbol(
        SymbolId(sourceElement.getName(), UnknownRawPath));
    DesignElement* targetElement = new DesignElement(
        targetSymbols.registerSymbol(elemName),
        fileSystem->toPathId(fileSystem->remap(sourceSymbols.getSymbol(SymbolId(
                                 sourceElement.getFileId(), UnknownRawPath))),
                             m_parse->getCompileSourceFile()->getSymbolTable()),
        static_cast<DesignElement::ElemType>(sourceElement.getType()),
        NodeId(sourceElement.getUniqueId()), sourceElement.getLine(),
        sourceElement.getColumn(), sourceElement.getEndLine(),
        sourceElement.getEndColumn(), NodeId(sourceElement.getParent()));
    targetElement->m_node = NodeId(sourceElement.getNode());
    targetElement->m_defaultNetType =
        static_cast<VObjectType>(sourceElement.getDefaultNetType());

    const ::TimeInfo::Reader& sourceTimeInfo = sourceElement.getTimeInfo();
    TimeInfo* const targetTimeInfo = &targetElement->m_timeInfo;

    targetTimeInfo->m_type =
        static_cast<TimeInfo::Type>(sourceTimeInfo.getType());
    targetTimeInfo->m_fileId =
        fileSystem->toPathId(fileSystem->remap(sourceSymbols.getSymbol(SymbolId(
                                 sourceTimeInfo.getFileId(), UnknownRawPath))),
                             &targetSymbols);
    targetTimeInfo->m_line = sourceTimeInfo.getLine();
    targetTimeInfo->m_timeUnit =
        static_cast<TimeInfo::Unit>(sourceTimeInfo.getTimeUnit());
    targetTimeInfo->m_timeUnitValue = sourceTimeInfo.getTimeUnitValue();
    targetTimeInfo->m_timePrecision =
        static_cast<TimeInfo::Unit>(sourceTimeInfo.getTimePrecision());
    targetTimeInfo->m_timePrecisionValue =
        sourceTimeInfo.getTimePrecisionValue();
    const std::string fullName =
        StrCat(fC->getLibrary()->getName(), "@", elemName);
    fC->addDesignElement(fullName, targetElement);
  }
}

bool ParseCache::restore(PathId cacheFileId) {
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
    const ::ParseCache::Reader& root = message.getRoot<::ParseCache>();

    if (!checkCacheIsValid(cacheFileId, root)) {
      result = false;
      break;
    }

    SymbolTable sourceSymbols;
    SymbolTable& targetSymbols =
        *m_parse->getCompileSourceFile()->getSymbolTable();
    ErrorContainer* const targetErrorContainer =
        m_parse->getCompileSourceFile()->getErrorContainer();

    restoreSymbols(sourceSymbols, root.getSymbols());
    restoreErrors(m_parse->getCompileSourceFile()->getErrorContainer(),
                  targetSymbols, root.getErrors(), sourceSymbols);

    // Restore design content (Verilog Design Elements)
    FileContent* fC = m_parse->getFileContent();
    if (fC == nullptr) {
      fC = new FileContent(m_parse->getFileId(0), m_parse->getLibrary(),
                           &targetSymbols, targetErrorContainer, nullptr,
                           BadPathId);
      m_parse->setFileContent(fC);
      m_parse->getCompileSourceFile()
          ->getCompiler()
          ->getDesign()
          ->addFileContent(m_parse->getFileId(0), fC);
    }

    // Restore design elements
    restoreDesignElements(fC, targetSymbols, root.getElements(), sourceSymbols);

    // Restore design objects
    restoreVObjects(*fC->mutableVObjects(), targetSymbols, root.getObjects(),
                    sourceSymbols);
  } while (false);

  ::close(fd);
  return result;
}

bool ParseCache::restore() {
  CommandLineParser* clp =
      m_parse->getCompileSourceFile()->getCommandLineParser();

  Precompiled* const prec = Precompiled::getSingleton();
  if (prec->isFilePrecompiled(
          m_parse->getPpFileId(),
          m_parse->getCompileSourceFile()->getSymbolTable())) {
    if (!clp->precompiledCacheAllowed()) return false;
  } else {
    if (!clp->cacheAllowed()) return false;
  }

  PathId cacheFileId = getCacheFileId(BadPathId);
  return cacheFileId && restore(cacheFileId);
}

bool ParseCache::save() {
  CommandLineParser* clp =
      m_parse->getCompileSourceFile()->getCommandLineParser();
  if (!clp->writeCache()) return true;

  FileContent* const fC = m_parse->getFileContent();
  if (fC && (fC->getVObjects().size() > Cache::Capacity)) {
    clp->setCacheAllowed(false);
    Location loc(BadSymbolId);
    Error err(ErrorDefinition::CMD_CACHE_CAPACITY_EXCEEDED, loc);
    m_parse->getCompileSourceFile()->getErrorContainer()->addError(err);
    return false;
  }

  PathId cacheFileId = getCacheFileId(BadPathId);
  if (!cacheFileId) {
    // Any fake(virtual) file like builtin.sv
    return true;
  }

  FileSystem* const fileSystem = FileSystem::getInstance();
  ErrorContainer* const errorContainer =
      m_parse->getCompileSourceFile()->getErrorContainer();
  SymbolTable* const sourceSymbols =
      m_parse->getCompileSourceFile()->getSymbolTable();
  SymbolTable targetSymbols;

  ::capnp::MallocMessageBuilder message;
  ::ParseCache::Builder builder = message.initRoot<::ParseCache>();

  // Create header section
  cacheHeader(builder.getHeader(), kSchemaVersion);

  // Cache the errors and canonical symbols
  cacheErrors(builder, targetSymbols, errorContainer, *sourceSymbols,
              m_parse->getFileId(LINE1));

  if (fC != nullptr) {
    // Cache the design content
    cacheDesignElements(builder, fC, targetSymbols, *sourceSymbols);
  }

  // Cache the design objects
  cacheVObjects(builder, fC, targetSymbols, *sourceSymbols,
                m_parse->getFileId(0));

  // Cache symbols
  cacheSymbols(builder, targetSymbols);

  // Finally, save to disk
  PathId cacheDirId = fileSystem->getParent(cacheFileId, sourceSymbols);
  if (!fileSystem->mkdirs(cacheDirId)) return false;

  const std::string filepath =
      fileSystem->toPlatformAbsPath(cacheFileId).string();
  const int32_t fd =
      ::open(filepath.c_str(), O_CREAT | O_WRONLY | O_BINARY, S_IRWXU);
  if (fd < 0) return false;

  writePackedMessageToFd(fd, message);
  ::close(fd);
  return true;
}
}  // namespace SURELOG
