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
 * File:   PPCache.cpp
 * Author: alain
 *
 * Created on April 23, 2017, 8:49 PM
 */

#include "Surelog/Cache/PPCache.h"

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
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Common/SymbolId.h"
#include "Surelog/Design/Design.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/TimeInfo.h"
#include "Surelog/Design/VObject.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Package/Precompiled.h"
#include "Surelog/SourceCompile/CompilationUnit.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/IncludeFileInfo.h"
#include "Surelog/SourceCompile/MacroInfo.h"
#include "Surelog/SourceCompile/PreprocessFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Utils/StringUtils.h"
#include "Surelog/config.h"

#if defined(_MSC_VER)
#include <io.h>
#else
#include <unistd.h>
#endif

#include <iostream>
#include <limits>

namespace SURELOG {
static constexpr std::string_view kSchemaVersion = "1.6";
static constexpr std::string_view UnknownRawPath = "<unknown>";

PPCache::PPCache(Session* session, PreprocessFile* pp)
    : Cache(session), m_pp(pp) {}

PathId PPCache::getCacheFileId(PathId sourceFileId) const {
  if (!sourceFileId) sourceFileId = m_pp->getFileId(LINE1);
  if (!sourceFileId) return BadPathId;

  FileSystem* const fileSystem = m_session->getFileSystem();
  SymbolTable* const symbols = m_session->getSymbolTable();
  CommandLineParser* const clp = m_session->getCommandLineParser();

  const std::string_view libName = m_pp->getLibrary()->getName();

  if (clp->parseOnly()) {
    // If parseOnly flag is set, the Preprocessor doesn't actually generate
    // an output file. Instead it uses the source itself i.e. from the original
    // source location. Compute the "potential" Preprocessor output file so the
    // cache file location would be correct.
    sourceFileId = fileSystem->getPpOutputFile(clp->fileUnit(), sourceFileId,
                                               libName, symbols);
  }

  Precompiled* const precompiled = m_session->getPrecompiled();
  const bool isPrecompiled = precompiled->isFilePrecompiled(sourceFileId);

  return fileSystem->getPpCacheFile(clp->fileUnit(), sourceFileId, libName,
                                    isPrecompiled, symbols);
}

void PPCache::cacheSymbols(::PPCache::Builder builder,
                           SymbolTable& sourceSymbols) {
  const std::vector<std::string_view> texts = sourceSymbols.getSymbols();
  ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Builder targetSymbols =
      builder.initSymbols(texts.size());
  Cache::cacheSymbols(targetSymbols, texts);
}

void PPCache::cacheErrors(::PPCache::Builder builder,
                          SymbolTable& targetSymbols,
                          const ErrorContainer* errorContainer,
                          const SymbolTable& sourceSymbols, PathId subjectId) {
  FileSystem* const fileSystem = m_session->getFileSystem();
  std::vector<Error> sourceErrors;
  sourceErrors.reserve(errorContainer->getErrors().size());
  for (const Error& error : errorContainer->getErrors()) {
    for (const Location& loc : error.getLocations()) {
      if (loc.m_fileId.equals(subjectId, fileSystem)) {
        sourceErrors.emplace_back(error);
        break;
      }
    }
  }

  ::capnp::List<::Error, ::capnp::Kind::STRUCT>::Builder targetErrors =
      builder.initErrors(sourceErrors.size());
  Cache::cacheErrors(targetErrors, targetSymbols, sourceErrors, sourceSymbols);
}

void PPCache::cacheVObjects(::PPCache::Builder builder, const FileContent* fC,
                            SymbolTable& targetSymbols,
                            const SymbolTable& sourceSymbols, PathId fileId) {
  const std::vector<VObject>& sourceVObjects = fC->getVObjects();
  ::capnp::List<::VObject, ::capnp::Kind::STRUCT>::Builder targetVObjects =
      builder.initObjects(sourceVObjects.size());
  Cache::cacheVObjects(targetVObjects, targetSymbols, sourceVObjects,
                       sourceSymbols);
}

template <class T>
static bool compareVectors(std::vector<T> a, std::vector<T> b) {
  std::sort(a.begin(), a.end());
  std::sort(b.begin(), b.end());
  return (a == b);
}

bool PPCache::checkCacheIsValid(PathId cacheFileId,
                                const ::PPCache::Reader& root) const {
  FileSystem* const fileSystem = m_session->getFileSystem();
  const ::Header::Reader& sourceHeader = root.getHeader();

  Precompiled* const precompiled = m_session->getPrecompiled();
  if (precompiled->isFilePrecompiled(m_pp->getFileId(LINE1))) {
    // For precompiled, check only the signature & version (so using
    // BadPathId instead of the actual arguments)
    return checkIfCacheIsValid(sourceHeader, kSchemaVersion, BadPathId,
                               BadPathId);
  }

  if (!checkIfCacheIsValid(sourceHeader, kSchemaVersion, cacheFileId,
                           m_pp->getFileId(LINE1))) {
    return false;
  }

  CommandLineParser* clp = m_session->getCommandLineParser();
  if (clp->parseOnly() || clp->lowMem()) return true;

  const ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Reader&
      sourceSymbols = root.getSymbols();

  // Check if the defines match
  const ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Reader&
      sourceDefines = root.getDefines();
  const auto& targetDefines = clp->getDefineList();
  if (sourceDefines.size() != targetDefines.size()) return false;

  std::vector<std::string> targetCmdDefineOptions;
  targetCmdDefineOptions.reserve(targetDefines.size());
  for (const auto& definePair : targetDefines) {
    std::string spath =
        StrCat(m_pp->getSymbol(definePair.first), "=", definePair.second);
    targetCmdDefineOptions.emplace_back(std::move(spath));
  }

  std::vector<std::string> sourceCmdDefineOptions;
  sourceCmdDefineOptions.reserve(sourceDefines.size());
  for (const ::capnp::Text::Reader& sourceDefine : sourceDefines) {
    sourceCmdDefineOptions.emplace_back(sourceDefine.cStr());
  }
  if (!compareVectors(sourceCmdDefineOptions, targetCmdDefineOptions)) {
    return false;
  }

  SymbolTable* const symbols = m_session->getSymbolTable();

  // Check if the includes resolve to the *same* path
  const ::capnp::List<::IncludeFileInfo, ::capnp::Kind::STRUCT>::Reader&
      sourceIncludeFileInfos = root.getIncludeFileInfos();
  PathIdSet targetIncludedFileIds;
  for (const ::IncludeFileInfo::Reader& sourceIncludeFileInfo :
       sourceIncludeFileInfos) {
    IncludeFileInfo::Context context = static_cast<IncludeFileInfo::Context>(
        sourceIncludeFileInfo.getContext());
    IncludeFileInfo::Action action =
        static_cast<IncludeFileInfo::Action>(sourceIncludeFileInfo.getAction());
    if ((context == IncludeFileInfo::Context::Include) &&
        (action == IncludeFileInfo::Action::Push)) {
      std::string cachedFile = fileSystem->remap(
          sourceSymbols[sourceIncludeFileInfo.getSectionFileId()].cStr());
      PathId cachedFileId = fileSystem->toPathId(cachedFile, symbols);
      PathId sessionFileId = fileSystem->locate(
          sourceSymbols[sourceIncludeFileInfo.getSymbolId()].cStr(),
          clp->getIncludePaths(), symbols);
      if (!cachedFileId.equals(sessionFileId, fileSystem)) {
        return false;  // Symbols don't resolve to the same file!
      }
      targetIncludedFileIds.emplace(sessionFileId);
    }
  }

  // Check all includes recursively!
  if (!std::all_of(targetIncludedFileIds.begin(), targetIncludedFileIds.end(),
                   [this](const PathId& targetIncludedFileId) {
                     return checkCacheIsValid(
                         getCacheFileId(targetIncludedFileId));
                   })) {
    return false;
  }

  return true;
}

bool PPCache::checkCacheIsValid(PathId cacheFileId) const {
  if (!cacheFileId) return false;
  if (m_pp->isMacroBody()) return false;

  CommandLineParser* const clp = m_session->getCommandLineParser();
  if (clp->parseOnly() || clp->lowMem()) return true;
  if (m_pp->isMacroBody()) return false;

  FileSystem* const fileSystem = m_session->getFileSystem();
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
    const ::PPCache::Reader& root = message.getRoot<::PPCache>();
    result = checkCacheIsValid(cacheFileId, root);
  } while (false);

  ::close(fd);
  return result;
}

bool PPCache::isValid() { return checkCacheIsValid(getCacheFileId(BadPathId)); }

void PPCache::cacheMacros(::PPCache::Builder builder,
                          SymbolTable& targetSymbols,
                          const SymbolTable& sourceSymbols,
                          const std::vector<MacroInfo*>& globalMacros) {
  FileSystem* const fileSystem = m_session->getFileSystem();
  ::capnp::List<::Macro, ::capnp::Kind::STRUCT>::Builder targetGlobalMacros =
      builder.initGlobalMacros(globalMacros.size());

  for (size_t index = 0, nindex = globalMacros.size(); index < nindex;
       ++index) {
    const MacroInfo* const info = globalMacros[index];
    ::Macro::Builder targetMacro = targetGlobalMacros[index];

    targetMacro.setNameId(
        (RawSymbolId)targetSymbols.registerSymbol(info->m_name));
    targetMacro.setDefType(static_cast<::MacroDefType>(info->m_defType));
    targetMacro.setFileId(
        (RawPathId)fileSystem->copy(info->m_fileId, &targetSymbols));
    targetMacro.setStartLine(info->m_startLine);
    targetMacro.setStartColumn(info->m_startColumn);
    targetMacro.setEndLine(info->m_endLine);
    targetMacro.setEndColumn(info->m_endColumn);
    targetMacro.setNameColumn(info->m_nameStartColumn);
    targetMacro.setBodyColumn(info->m_bodyStartColumn);

    const std::vector<std::string>& sourceArguments = info->m_arguments;
    ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Builder targetArguments =
        targetMacro.initArguments(sourceArguments.size());
    for (size_t i = 0, ni = sourceArguments.size(); i < ni; ++i) {
      targetArguments.set(i, sourceArguments[i].c_str());
    }

    const std::vector<LineColumn>& sourceArgumentPositions =
        info->m_argumentPositions;
    ::capnp::List<::LineColumn, ::capnp::Kind::STRUCT>::Builder
        targetArgumentPositions =
            targetMacro.initArgumentPositions(sourceArgumentPositions.size());
    for (size_t i = 0, ni = sourceArgumentPositions.size(); i < ni; ++i) {
      targetArgumentPositions[i].setLine(sourceArgumentPositions[i].first);
      targetArgumentPositions[i].setColumn(sourceArgumentPositions[i].second);
    }

    const std::vector<std::string>& sourceTokens = info->m_tokens;
    ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Builder targetTokens =
        targetMacro.initTokens(sourceTokens.size());
    for (size_t i = 0, ni = sourceTokens.size(); i < ni; ++i) {
      targetTokens.set(i, sourceTokens[i].c_str());
    }

    const std::vector<LineColumn>& sourceTokenPositions =
        info->m_tokenPositions;
    ::capnp::List<::LineColumn, ::capnp::Kind::STRUCT>::Builder
        targetTokenPositions =
            targetMacro.initTokenPositions(sourceTokenPositions.size());
    for (size_t i = 0, ni = sourceTokenPositions.size(); i < ni; ++i) {
      targetTokenPositions[i].setLine(sourceTokenPositions[i].first);
      targetTokenPositions[i].setColumn(sourceTokenPositions[i].second);
    }

    /*
    std::cout << "SAVING MACRO: " << macroName << std::endl;
    Debug code for a caching issue"
    std::cout << "STRING VECTOR CONTENT:\n";
    int32_t index = 0;
    std::cout << "VECTOR SIZE: " << info->m_tokens.size() << std::endl;
    for (auto st : info->m_tokens) {
      std::cout << index << " ST:" << st.size() << " >>>" << st << "<<<"
                << std::endl;
      index++;
    }
    */
  }

  const MacroStorage& localMacros = m_pp->getMacros();
  ::capnp::List<::uint16_t, ::capnp::Kind::PRIMITIVE>::Builder
      targetLocalMacros = builder.initLocalMacros(localMacros.size());

  for (size_t index = 0, nindex = localMacros.size(); index < nindex; ++index) {
    const MacroInfo* const info = localMacros[index];
    targetLocalMacros.set(
        index, std::distance(
                   globalMacros.begin(),
                   std::find(globalMacros.begin(), globalMacros.end(), info)));
  }
}

void PPCache::cacheDefines(::PPCache::Builder builder,
                           SymbolTable& targetSymbols,
                           const SymbolTable& sourceSymbols) {
  CommandLineParser* const clp = m_session->getCommandLineParser();

  const auto& sourceDefines = clp->getDefineList();
  ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Builder targetDefines =
      builder.initDefines(sourceDefines.size());

  size_t index = 0;
  for (const auto& entry : sourceDefines) {
    std::string define =
        StrCat(m_pp->getSymbol(entry.first), "=", entry.second);
    targetDefines.set(index, define.c_str());
    ++index;
  }
}

void PPCache::cacheTimeInfos(::PPCache::Builder builder,
                             SymbolTable& targetSymbols,
                             const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = m_session->getFileSystem();

  const std::vector<TimeInfo>& sourceTimeInfos =
      m_pp->getCompilationUnit()->getTimeInfo();

  size_t count = 0;
  for (const TimeInfo& sourceTimeInfo : sourceTimeInfos) {
    if (sourceTimeInfo.m_fileId == m_pp->getFileId(0)) {
      ++count;
    }
  }

  if (count == 0) return;

  ::capnp::List<::TimeInfo, ::capnp::Kind::STRUCT>::Builder targetTimeInfos =
      builder.initTimeInfos(count);

  for (size_t i = 0, j = 0, ni = sourceTimeInfos.size(); i < ni; ++i) {
    const TimeInfo& sourceTimeInfo = sourceTimeInfos[i];
    if (sourceTimeInfo.m_fileId != m_pp->getFileId(0)) continue;

    ::TimeInfo::Builder targetTimeInfo = targetTimeInfos[j++];
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
  }
}

void PPCache::cacheLineTranslationInfos(::PPCache::Builder builder,
                                        SymbolTable& targetSymbols,
                                        const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = m_session->getFileSystem();

  const std::vector<PreprocessFile::LineTranslationInfo>&
      sourceLineTranslationInfos = m_pp->getLineTranslationInfo();
  ::capnp::List<::LineTranslationInfo, ::capnp::Kind::STRUCT>::Builder
      targetLineTranslationInfos =
          builder.initLineTranslations(sourceLineTranslationInfos.size());

  for (size_t i = 0, ni = sourceLineTranslationInfos.size(); i < ni; ++i) {
    const PreprocessFile::LineTranslationInfo& sourceLineTranslationInfo =
        sourceLineTranslationInfos[i];
    ::LineTranslationInfo::Builder targetLineTranslationInfo =
        targetLineTranslationInfos[i];
    PathId pretendFileId = fileSystem->copy(
        sourceLineTranslationInfo.m_pretendFileId, &targetSymbols);

    targetLineTranslationInfo.setPretendFileId((RawPathId)pretendFileId);
    targetLineTranslationInfo.setOriginalLine(
        sourceLineTranslationInfo.m_originalLine);
    targetLineTranslationInfo.setPretendLine(
        sourceLineTranslationInfo.m_pretendLine);
  }
}

void PPCache::cacheIncludeFileInfos(
    ::PPCache::Builder builder, SymbolTable& targetSymbols,
    const SymbolTable& sourceSymbols,
    const std::vector<MacroInfo*>& globalMacros) {
  FileSystem* const fileSystem = m_session->getFileSystem();

  const std::vector<IncludeFileInfo>& sourceIncludeFileInfos =
      m_pp->getIncludeFileInfo();
  ::capnp::List<::IncludeFileInfo, ::capnp::Kind::STRUCT>::Builder
      targetIncludeFileInfos =
          builder.initIncludeFileInfos(sourceIncludeFileInfos.size());

  for (size_t i = 0, ni = sourceIncludeFileInfos.size(); i < ni; ++i) {
    const IncludeFileInfo& sourceIncludeFileInfo = sourceIncludeFileInfos[i];
    ::IncludeFileInfo::Builder targetIncludeFileInfo =
        targetIncludeFileInfos[i];

    SymbolId symbolId = targetSymbols.copyFrom(sourceIncludeFileInfo.m_symbolId,
                                               &sourceSymbols);
    PathId sectionFileId =
        fileSystem->copy(sourceIncludeFileInfo.m_sectionFileId, &targetSymbols);

    targetIncludeFileInfo.setContext(
        static_cast<uint16_t>(sourceIncludeFileInfo.m_context));
    targetIncludeFileInfo.setAction(
        static_cast<uint16_t>(sourceIncludeFileInfo.m_action));

    if (sourceIncludeFileInfo.m_macroDefinition == nullptr) {
      targetIncludeFileInfo.setDefinition(-1);
    } else {
      targetIncludeFileInfo.setDefinition(
          std::distance(globalMacros.begin(),
                        std::find(globalMacros.begin(), globalMacros.end(),
                                  sourceIncludeFileInfo.m_macroDefinition)));
    }
    targetIncludeFileInfo.setSectionFileId((RawPathId)sectionFileId);
    targetIncludeFileInfo.setSectionLine(sourceIncludeFileInfo.m_sectionLine);
    targetIncludeFileInfo.setSectionColumn(
        sourceIncludeFileInfo.m_sectionColumn);

    targetIncludeFileInfo.setSourceLine(sourceIncludeFileInfo.m_sourceLine);
    targetIncludeFileInfo.setSourceColumn(sourceIncludeFileInfo.m_sourceColumn);

    targetIncludeFileInfo.setSymbolId((RawSymbolId)symbolId);
    targetIncludeFileInfo.setSymbolLine(sourceIncludeFileInfo.m_symbolLine);
    targetIncludeFileInfo.setSymbolColumn(sourceIncludeFileInfo.m_symbolColumn);

    targetIncludeFileInfo.setIndexOpposite(
        sourceIncludeFileInfo.m_indexOpposite);

    const std::vector<MacroInfo*>& sourceDefinitions =
        sourceIncludeFileInfo.m_macroDefinitions;
    ::capnp::List<::uint16_t, ::capnp::Kind::PRIMITIVE>::Builder
        targetDefinitions =
            targetIncludeFileInfo.initDefinitions(sourceDefinitions.size());
    for (size_t j = 0, nj = sourceDefinitions.size(); j < nj; ++j) {
      targetDefinitions.set(
          j, std::distance(globalMacros.begin(),
                           std::find(globalMacros.begin(), globalMacros.end(),
                                     sourceDefinitions[j])));
    }

    const std::vector<LineColumn>& sourceTokenPositions =
        sourceIncludeFileInfo.m_tokenPositions;
    ::capnp::List<::LineColumn, ::capnp::Kind::STRUCT>::Builder
        targetTokenPositions = targetIncludeFileInfo.initTokenPositions(
            sourceTokenPositions.size());
    for (size_t j = 0, nj = sourceTokenPositions.size(); j < nj; ++j) {
      targetTokenPositions[j].setLine(sourceTokenPositions[j].first);
      targetTokenPositions[j].setColumn(sourceTokenPositions[j].second);
    }
  }
}

void PPCache::restoreMacros(
    SymbolTable& targetSymbols,
    const ::capnp::List<::Macro>::Reader& sourceGlobalMacros,
    const ::capnp::List<::uint16_t, ::capnp::Kind::PRIMITIVE>::Reader&
        sourceLocalMacros,
    const SymbolTable& sourceSymbols, std::vector<MacroInfo*>& globalMacros) {
  FileSystem* const fileSystem = m_session->getFileSystem();

  for (const ::Macro::Reader& sourceMacro : sourceGlobalMacros) {
    // std::cout << "RESTORING MACRO: " << macro->name()->str() << std::endl;
    const ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Reader&
        sourceArguments = sourceMacro.getArguments();
    const ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Reader&
        sourceTokens = sourceMacro.getTokens();
    const ::capnp::List<::LineColumn, ::capnp::Kind::STRUCT>::Reader&
        sourceArgumentPositions = sourceMacro.getArgumentPositions();
    const ::capnp::List<::LineColumn, ::capnp::Kind::STRUCT>::Reader&
        sourceTokenPositions = sourceMacro.getTokenPositions();

    std::vector<std::string> args;
    args.reserve(sourceArguments.size());
    for (const ::capnp::Text::Reader& sourceArgument : sourceArguments) {
      args.emplace_back(sourceArgument.cStr());
    }

    std::vector<LineColumn> argumentPositions;
    argumentPositions.reserve(sourceArgumentPositions.size());
    for (const ::LineColumn::Reader& sourcePosition : sourceArgumentPositions) {
      argumentPositions.emplace_back(sourcePosition.getLine(),
                                     sourcePosition.getColumn());
    }

    std::vector<std::string> tokens;
    tokens.reserve(sourceTokens.size());
    for (const ::capnp::Text::Reader& sourceToken : sourceTokens) {
      tokens.emplace_back(sourceToken.cStr());
    }

    std::vector<LineColumn> tokenPositions;
    tokenPositions.reserve(sourceTokenPositions.size());
    for (const ::LineColumn::Reader& sourcePosition : sourceTokenPositions) {
      tokenPositions.emplace_back(sourcePosition.getLine(),
                                  sourcePosition.getColumn());
    }

    globalMacros.emplace_back(new MacroInfo(
        sourceSymbols.getSymbol(
            SymbolId(sourceMacro.getNameId(), UnknownRawPath)),
        static_cast<MacroInfo::DefType>(sourceMacro.getDefType()),
        fileSystem->toPathId(fileSystem->remap(sourceSymbols.getSymbol(SymbolId(
                                 sourceMacro.getFileId(), UnknownRawPath))),
                             &targetSymbols),
        sourceMacro.getStartLine(), sourceMacro.getStartColumn(),
        sourceMacro.getEndLine(), sourceMacro.getEndColumn(),
        sourceMacro.getNameColumn(), sourceMacro.getBodyColumn(), args,
        argumentPositions, tokens, tokenPositions));
  }

  for (uint16_t index : sourceLocalMacros) {
    m_pp->addMacro(globalMacros[index]);
  }
}

void PPCache::restoreTimeInfos(
    SymbolTable& targetSymbols,
    const ::capnp::List<::TimeInfo>::Reader& sourceTimeInfos,
    const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = m_session->getFileSystem();

  for (const ::TimeInfo::Reader& sourceTimeInfo : sourceTimeInfos) {
    TimeInfo targetTimeInfo;
    targetTimeInfo.m_type =
        static_cast<TimeInfo::Type>(sourceTimeInfo.getType());
    targetTimeInfo.m_fileId =
        fileSystem->toPathId(fileSystem->remap(sourceSymbols.getSymbol(SymbolId(
                                 sourceTimeInfo.getFileId(), UnknownRawPath))),
                             &targetSymbols);
    targetTimeInfo.m_line = sourceTimeInfo.getLine();
    targetTimeInfo.m_timeUnit =
        static_cast<TimeInfo::Unit>(sourceTimeInfo.getTimeUnit());
    targetTimeInfo.m_timeUnitValue = sourceTimeInfo.getTimeUnitValue();
    targetTimeInfo.m_timePrecision =
        static_cast<TimeInfo::Unit>(sourceTimeInfo.getTimePrecision());
    targetTimeInfo.m_timePrecisionValue =
        sourceTimeInfo.getTimePrecisionValue();
    m_pp->getCompilationUnit()->recordTimeInfo(targetTimeInfo);
  }
}

void PPCache::restoreLineTranslationInfos(
    SymbolTable& targetSymbols,
    const ::capnp::List<::LineTranslationInfo>::Reader&
        sourceLineTranslationInfos,
    const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = m_session->getFileSystem();

  for (const ::LineTranslationInfo::Reader& sourceLineTranslationInfo :
       sourceLineTranslationInfos) {
    PathId pretendFileId = fileSystem->toPathId(
        fileSystem->remap(sourceSymbols.getSymbol(SymbolId(
            sourceLineTranslationInfo.getPretendFileId(), UnknownRawPath))),
        &targetSymbols);
    PreprocessFile::LineTranslationInfo lineFileInfo(
        pretendFileId, sourceLineTranslationInfo.getOriginalLine(),
        sourceLineTranslationInfo.getPretendLine());
    m_pp->addLineTranslationInfo(lineFileInfo);
  }
}

void PPCache::restoreIncludeFileInfos(
    SymbolTable& targetSymbols,
    const ::capnp::List<::IncludeFileInfo>::Reader& sourceIncludeFileInfos,
    const SymbolTable& sourceSymbols, const std::vector<MacroInfo*>& macros) {
  FileSystem* const fileSystem = m_session->getFileSystem();

  for (const ::IncludeFileInfo::Reader& sourceIncludeFileInfo :
       sourceIncludeFileInfos) {
    SymbolId sectionSymbolId = targetSymbols.copyFrom(
        SymbolId(sourceIncludeFileInfo.getSymbolId(), "<unknown"),
        &sourceSymbols);
    PathId sectionFileId = fileSystem->toPathId(
        fileSystem->remap(sourceSymbols.getSymbol(SymbolId(
            sourceIncludeFileInfo.getSectionFileId(), UnknownRawPath))),
        &targetSymbols);
    int32_t macroIndex = sourceIncludeFileInfo.getDefinition();
    MacroInfo* const macroInstance =
        (macroIndex != -1) ? macros[macroIndex] : nullptr;
    // std::cout << "read sectionFile: " << sectionFileName << " s:" <<
    // incinfo->m_sectionStartLine() << " o:" << incinfo->m_originalLine() <<
    // " t:" << incinfo->m_type() << "\n";
    int32_t index = m_pp->addIncludeFileInfo(
        static_cast<IncludeFileInfo::Context>(
            sourceIncludeFileInfo.getContext()),
        static_cast<IncludeFileInfo::Action>(sourceIncludeFileInfo.getAction()),
        macroInstance, sectionFileId, sourceIncludeFileInfo.getSectionLine(),
        sourceIncludeFileInfo.getSectionColumn(),
        sourceIncludeFileInfo.getSourceLine(),
        sourceIncludeFileInfo.getSourceColumn(), sectionSymbolId,
        sourceIncludeFileInfo.getSymbolLine(),
        sourceIncludeFileInfo.getSymbolColumn(),
        sourceIncludeFileInfo.getIndexOpposite());

    IncludeFileInfo& fi = m_pp->getIncludeFileInfo(index);

    ::capnp::List<::uint16_t, ::capnp::Kind::PRIMITIVE>::Reader
        sourceDefinitions = sourceIncludeFileInfo.getDefinitions();
    std::vector<MacroInfo*>& targetDefinitions = fi.m_macroDefinitions;
    for (uint16_t index : sourceDefinitions) {
      targetDefinitions.emplace_back(macros[index]);
    }

    ::capnp::List<::LineColumn, ::capnp::Kind::STRUCT>::Reader
        sourceTokenPositions = sourceIncludeFileInfo.getTokenPositions();
    std::vector<LineColumn>& targetTokenPositions = fi.m_tokenPositions;
    for (const ::LineColumn::Reader& lc : sourceTokenPositions) {
      targetTokenPositions.emplace_back(lc.getLine(), lc.getColumn());
    }
  }
}

bool PPCache::restore(PathId cacheFileId, bool errorsOnly,
                      int32_t recursionDepth) {
  if (!cacheFileId) return false;

  FileSystem* const fileSystem = m_session->getFileSystem();
  const std::string filepath =
      fileSystem->toPlatformAbsPath(cacheFileId).string();

  const int32_t fd = ::open(filepath.c_str(), O_RDONLY | O_BINARY);
  if (fd < 0) return false;

  SymbolTable* const targetSymbols = m_session->getSymbolTable();
  ErrorContainer* const errors = m_session->getErrorContainer();

  bool result = true;
  do {
    ::capnp::ReaderOptions options;
    options.traversalLimitInWords = std::numeric_limits<uint64_t>::max();
    options.nestingLimit = 1024;
    ::capnp::PackedFdMessageReader message(fd, options);
    const ::PPCache::Reader& root = message.getRoot<::PPCache>();

    if (!checkCacheIsValid(cacheFileId, root)) {
      result = false;
      break;
    }

    SymbolTable sourceSymbols;

    restoreSymbols(sourceSymbols, root.getSymbols());
    restoreErrors(errors, *targetSymbols, root.getErrors(), sourceSymbols);

    // Always restore the macros
    std::vector<MacroInfo*> globalMacros;
    restoreMacros(*targetSymbols, root.getGlobalMacros(), root.getLocalMacros(),
                  sourceSymbols, globalMacros);

    if (!errorsOnly) {
      // Restore `timescale directives
      restoreTimeInfos(*targetSymbols, root.getTimeInfos(), sourceSymbols);
    }

    if (recursionDepth == 0) {
      // Restore line translation info
      restoreLineTranslationInfos(*targetSymbols, root.getLineTranslations(),
                                  sourceSymbols);
    }

    // Restore include file info
    if (recursionDepth == 0) m_pp->clearIncludeFileInfo();
    restoreIncludeFileInfos(*targetSymbols, root.getIncludeFileInfos(),
                            sourceSymbols, globalMacros);

    if (!errorsOnly) {
      // Restore file body
      m_pp->append(root.getBody().cStr());
    }

    // FileContent
    FileContent* fC = m_pp->getFileContent();
    if (fC == nullptr) {
      fC = new FileContent(m_session, m_pp->getFileId(0), m_pp->getLibrary(),
                           nullptr, BadPathId);
      m_pp->setFileContent(fC);
      m_pp->getCompileSourceFile()
          ->getCompiler()
          ->getDesign()
          ->addPPFileContent(m_pp->getFileId(0), fC);
    }

    if (!errorsOnly) {
      // Restore design objects
      restoreVObjects(*fC->mutableVObjects(), *targetSymbols, root.getObjects(),
                      sourceSymbols);
    }
  } while (false);

  ::close(fd);
  return result;
}

bool PPCache::restore(bool errorsOnly) {
  if (m_pp->isMacroBody()) return false;

  CommandLineParser* const clp = m_session->getCommandLineParser();
  Precompiled* const precompiled = m_session->getPrecompiled();
  if (precompiled->isFilePrecompiled(m_pp->getFileId(LINE1))) {
    if (!clp->precompiledCacheAllowed()) return false;
  } else {
    if (!clp->cacheAllowed()) return false;
  }

  PathId cacheFileId = getCacheFileId(BadPathId);
  return cacheFileId && restore(cacheFileId, errorsOnly, 0);
}

bool PPCache::save() {
  if (m_pp->isMacroBody()) return true;

  CommandLineParser* const clp = m_session->getCommandLineParser();
  if (!clp->writeCache()) return true;

  ErrorContainer* const errors = m_session->getErrorContainer();

  FileContent* const fC = m_pp->getFileContent();
  if (fC && (fC->getVObjects().size() > Cache::Capacity)) {
    clp->setCacheAllowed(false);
    errors->addError(ErrorDefinition::CMD_CACHE_CAPACITY_EXCEEDED,
                     Location(BadSymbolId));
    return false;
  }

  const PathId cacheFileId = getCacheFileId(BadPathId);
  if (!cacheFileId) {
    // Any fake(virtual) file like builtin.sv
    return true;
  }

  // std::cout << "SAVING FILE: " << PathIdPP(cacheFileId) << std::endl;

  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errorContainer = m_session->getErrorContainer();
  SymbolTable* const sourceSymbols = m_session->getSymbolTable();
  SymbolTable targetSymbols;

  ::capnp::MallocMessageBuilder message;
  ::PPCache::Builder builder = message.initRoot<::PPCache>();

  // Create header section
  cacheHeader(builder.getHeader(), kSchemaVersion);

  std::vector<MacroInfo*> globalMacros;
  for (const IncludeFileInfo& ifi : m_pp->getIncludeFileInfo()) {
    globalMacros.insert(globalMacros.end(), ifi.m_macroDefinitions.cbegin(),
                        ifi.m_macroDefinitions.cend());
  }

  // Cache the macro definitions
  cacheMacros(builder, targetSymbols, *sourceSymbols, globalMacros);

  // Cache the body of the file
  const auto& body = m_pp->getPreProcessedFileContent();
  builder.setBody(std::get<0>(body).c_str());

  // Cache the errors and canonical symbols
  PathId subjectFileId = m_pp->getFileId(LINE1);
  cacheErrors(builder, targetSymbols, errorContainer, *sourceSymbols,
              subjectFileId);

  // Cache the defines on the command line
  cacheDefines(builder, targetSymbols, *sourceSymbols);

  // Cache the include info
  cacheTimeInfos(builder, targetSymbols, *sourceSymbols);

  // Cache the line translation
  cacheLineTranslationInfos(builder, targetSymbols, *sourceSymbols);

  // Cache the include info
  cacheIncludeFileInfos(builder, targetSymbols, *sourceSymbols, globalMacros);

  // Cache the design objects
  cacheVObjects(builder, fC, targetSymbols, *sourceSymbols, m_pp->getFileId(0));

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
