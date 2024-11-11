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

#include <capnp/serialize-packed.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Design/Design.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/TimeInfo.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Package/Precompiled.h"
#include "Surelog/SourceCompile/CompilationUnit.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/Compiler.h"
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

PPCache::PPCache(PreprocessFile* pp) : m_pp(pp) {}

PathId PPCache::getCacheFileId(PathId sourceFileId) const {
  if (!sourceFileId) sourceFileId = m_pp->getFileId(LINE1);
  if (!sourceFileId) return BadPathId;

  FileSystem* const fileSystem = FileSystem::getInstance();
  CommandLineParser* clp = m_pp->getCompileSourceFile()->getCommandLineParser();
  SymbolTable* symbolTable = m_pp->getCompileSourceFile()->getSymbolTable();

  const std::string_view libName = m_pp->getLibrary()->getName();

  if (clp->parseOnly()) {
    // If parseOnly flag is set, the Preprocessor doesn't actually generate
    // an output file. Instead it uses the source itself i.e. from the original
    // source location. Compute the "potential" Preprocessor output file so the
    // cache file location would be correct.
    sourceFileId = fileSystem->getPpOutputFile(clp->fileunit(), sourceFileId,
                                               libName, symbolTable);
  }

  Precompiled* prec = Precompiled::getSingleton();
  const bool isPrecompiled = prec->isFilePrecompiled(sourceFileId, symbolTable);

  return fileSystem->getPpCacheFile(clp->fileunit(), sourceFileId, libName,
                                    isPrecompiled, symbolTable);
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
  FileSystem* const fileSystem = FileSystem::getInstance();
  const ::Header::Reader& sourceHeader = root.getHeader();

  SymbolTable* const targetSymbols =
      m_pp->getCompileSourceFile()->getSymbolTable();

  Precompiled* prec = Precompiled::getSingleton();
  if (prec->isFilePrecompiled(m_pp->getFileId(LINE1), targetSymbols)) {
    // For precompiled, check only the signature & version (so using
    // BadPathId instead of the actual arguments)
    return checkIfCacheIsValid(sourceHeader, kSchemaVersion, BadPathId,
                               BadPathId);
  }

  if (!checkIfCacheIsValid(sourceHeader, kSchemaVersion, cacheFileId,
                           m_pp->getFileId(LINE1))) {
    return false;
  }

  CommandLineParser* clp = m_pp->getCompileSourceFile()->getCommandLineParser();
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
    if ((context == IncludeFileInfo::Context::INCLUDE) &&
        (action == IncludeFileInfo::Action::PUSH)) {
      std::string cachedFile = fileSystem->remap(
          sourceSymbols[sourceIncludeFileInfo.getSectionFileId()].cStr());
      PathId cachedFileId = fileSystem->toPathId(
          cachedFile, m_pp->getCompileSourceFile()->getSymbolTable());
      PathId sessionFileId = fileSystem->locate(
          sourceSymbols[sourceIncludeFileInfo.getSectionSymbolId()].cStr(),
          clp->getIncludePaths(),
          m_pp->getCompileSourceFile()->getSymbolTable());
      if (cachedFileId != sessionFileId) {
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

  CommandLineParser* clp = m_pp->getCompileSourceFile()->getCommandLineParser();
  if (clp->parseOnly() || clp->lowMem()) return true;
  if (m_pp->isMacroBody()) return false;

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
    const ::PPCache::Reader& root = message.getRoot<::PPCache>();
    result = checkCacheIsValid(cacheFileId, root);
  } while (false);

  ::close(fd);
  return result;
}

bool PPCache::isValid() { return checkCacheIsValid(getCacheFileId(BadPathId)); }

void PPCache::cacheMacros(::PPCache::Builder builder,
                          SymbolTable& targetSymbols,
                          const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = FileSystem::getInstance();

  const MacroStorage& sourceMacros = m_pp->getMacros();
  size_t count = 0;
  for (const auto& [macroName, infoVec] : sourceMacros) {
    count += infoVec.size();
  }

  ::capnp::List<::Macro, ::capnp::Kind::STRUCT>::Builder targetMacros =
      builder.initMacros(count);

  size_t index = 0;
  for (const auto& [macroName, infoVec] : sourceMacros) {
    for (const auto& info : infoVec) {
      ::Macro::Builder targetMacro = targetMacros[index];

      targetMacro.setNameId(
          (RawSymbolId)targetSymbols.registerSymbol(macroName));
      targetMacro.setType((info->m_type == MacroInfo::WITH_ARGS)
                              ? ::MacroType::WITH_ARGS
                              : ::MacroType::NO_ARGS);
      targetMacro.setFileId(
          (RawPathId)fileSystem->copy(info->m_fileId, &targetSymbols));
      targetMacro.setStartLine(info->m_startLine);
      targetMacro.setStartColumn(info->m_startColumn);
      targetMacro.setEndLine(info->m_endLine);
      targetMacro.setEndColumn(info->m_endColumn);

      const std::vector<std::string>& sourceArguments = info->m_arguments;
      ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Builder
          targetArguments = targetMacro.initArguments(sourceArguments.size());
      for (size_t i = 0, ni = sourceArguments.size(); i < ni; ++i) {
        targetArguments.set(i, sourceArguments[i].c_str());
      }

      const std::vector<std::string>& sourceTokens = info->m_tokens;
      ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Builder targetTokens =
          targetMacro.initTokens(sourceTokens.size());
      for (size_t i = 0, ni = sourceTokens.size(); i < ni; ++i) {
        targetTokens.set(i, sourceTokens[i].c_str());
      }

      ++index;

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
  }
}

void PPCache::cacheDefines(::PPCache::Builder builder,
                           SymbolTable& targetSymbols,
                           const SymbolTable& sourceSymbols) {
  CommandLineParser* const clp =
      m_pp->getCompileSourceFile()->getCommandLineParser();

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
  FileSystem* const fileSystem = FileSystem::getInstance();

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
  FileSystem* const fileSystem = FileSystem::getInstance();

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

void PPCache::cacheIncludeFileInfos(::PPCache::Builder builder,
                                    SymbolTable& targetSymbols,
                                    const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = FileSystem::getInstance();

  const std::vector<IncludeFileInfo>& sourceIncludeFileInfos =
      m_pp->getIncludeFileInfo();
  ::capnp::List<::IncludeFileInfo, ::capnp::Kind::STRUCT>::Builder
      targetIncludeFileInfos =
          builder.initIncludeFileInfos(sourceIncludeFileInfos.size());

  for (size_t i = 0, ni = sourceIncludeFileInfos.size(); i < ni; ++i) {
    const IncludeFileInfo& sourceIncludeFileInfo = sourceIncludeFileInfos[i];
    ::IncludeFileInfo::Builder targetIncludeFileInfo =
        targetIncludeFileInfos[i];

    SymbolId sectionSymbolId = targetSymbols.copyFrom(
        sourceIncludeFileInfo.m_sectionSymbolId, &sourceSymbols);
    PathId sectionFileId =
        fileSystem->copy(sourceIncludeFileInfo.m_sectionFileId, &targetSymbols);

    targetIncludeFileInfo.setContext(
        static_cast<uint32_t>(sourceIncludeFileInfo.m_context));
    targetIncludeFileInfo.setSectionStartLine(
        sourceIncludeFileInfo.m_sectionStartLine);
    targetIncludeFileInfo.setSectionSymbolId((RawSymbolId)sectionSymbolId);
    targetIncludeFileInfo.setSectionFileId((RawPathId)sectionFileId);
    targetIncludeFileInfo.setOriginalStartLine(
        sourceIncludeFileInfo.m_originalStartLine);
    targetIncludeFileInfo.setOriginalStartColumn(
        sourceIncludeFileInfo.m_originalStartColumn);
    targetIncludeFileInfo.setOriginalEndLine(
        sourceIncludeFileInfo.m_originalEndLine);
    targetIncludeFileInfo.setOriginalEndColumn(
        sourceIncludeFileInfo.m_originalEndColumn);
    targetIncludeFileInfo.setAction(
        static_cast<uint32_t>(sourceIncludeFileInfo.m_action));
    targetIncludeFileInfo.setIndexOpening(sourceIncludeFileInfo.m_indexOpening);
    targetIncludeFileInfo.setIndexClosing(sourceIncludeFileInfo.m_indexClosing);
  }
}

void PPCache::restoreMacros(SymbolTable& targetSymbols,
                            const ::capnp::List<::Macro>::Reader& sourceMacros,
                            const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = FileSystem::getInstance();

  for (const ::Macro::Reader& sourceMacro : sourceMacros) {
    // std::cout << "RESTORING MACRO: " << macro->name()->str() << std::endl;
    const ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Reader&
        sourceArguments = sourceMacro.getArguments();
    const ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Reader&
        sourceTokens = sourceMacro.getTokens();

    std::vector<std::string> args;
    args.reserve(sourceArguments.size());
    for (const ::capnp::Text::Reader& sourceArgument : sourceArguments) {
      args.emplace_back(sourceArgument.cStr());
    }

    std::vector<std::string> tokens;
    tokens.reserve(sourceTokens.size());
    for (const ::capnp::Text::Reader& sourceToken : sourceTokens) {
      tokens.emplace_back(sourceToken.cStr());
    }

    m_pp->recordMacro(
        sourceSymbols.getSymbol(
            SymbolId(sourceMacro.getNameId(), UnknownRawPath)),
        fileSystem->toPathId(fileSystem->remap(sourceSymbols.getSymbol(SymbolId(
                                 sourceMacro.getFileId(), UnknownRawPath))),
                             &targetSymbols),
        sourceMacro.getStartLine(), sourceMacro.getStartColumn(),
        sourceMacro.getEndLine(), sourceMacro.getEndColumn(), args, tokens);
  }
}

void PPCache::restoreTimeInfos(
    SymbolTable& targetSymbols,
    const ::capnp::List<::TimeInfo>::Reader& sourceTimeInfos,
    const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = FileSystem::getInstance();

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
  FileSystem* const fileSystem = FileSystem::getInstance();

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
    const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = FileSystem::getInstance();

  for (const ::IncludeFileInfo::Reader& sourceIncludeFileInfo :
       sourceIncludeFileInfos) {
    SymbolId sectionSymbolId = targetSymbols.copyFrom(
        SymbolId(sourceIncludeFileInfo.getSectionSymbolId(), "<unknown"),
        &sourceSymbols);
    PathId sectionFileId = fileSystem->toPathId(
        fileSystem->remap(sourceSymbols.getSymbol(SymbolId(
            sourceIncludeFileInfo.getSectionFileId(), UnknownRawPath))),
        &targetSymbols);
    // std::cout << "read sectionFile: " << sectionFileName << " s:" <<
    // incinfo->m_sectionStartLine() << " o:" << incinfo->m_originalLine() <<
    // " t:" << incinfo->m_type() << "\n";
    m_pp->addIncludeFileInfo(
        static_cast<IncludeFileInfo::Context>(
            sourceIncludeFileInfo.getContext()),
        sourceIncludeFileInfo.getSectionStartLine(), sectionSymbolId,
        sectionFileId, sourceIncludeFileInfo.getOriginalStartLine(),
        sourceIncludeFileInfo.getOriginalStartColumn(),
        sourceIncludeFileInfo.getOriginalEndLine(),
        sourceIncludeFileInfo.getOriginalEndColumn(),
        static_cast<IncludeFileInfo::Action>(sourceIncludeFileInfo.getAction()),
        sourceIncludeFileInfo.getIndexClosing(),
        sourceIncludeFileInfo.getIndexClosing());
  }
}

bool PPCache::restore(PathId cacheFileId, bool errorsOnly,
                      int32_t recursionDepth) {
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
    const ::PPCache::Reader& root = message.getRoot<::PPCache>();

    if (!checkCacheIsValid(cacheFileId, root)) {
      result = false;
      break;
    }

    SymbolTable sourceSymbols;
    SymbolTable* const targetSymbols =
        m_pp->getCompileSourceFile()->getSymbolTable();

    restoreSymbols(sourceSymbols, root.getSymbols());
    restoreErrors(m_pp->getCompileSourceFile()->getErrorContainer(),
                  *targetSymbols, root.getErrors(), sourceSymbols);

    // Always restore the macros
    restoreMacros(*targetSymbols, root.getMacros(), sourceSymbols);

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
                            sourceSymbols);

    if (!errorsOnly) {
      // Restore file body
      m_pp->append(root.getBody().cStr());
    }

    // FileContent
    FileContent* fC = m_pp->getFileContent();
    if (fC == nullptr) {
      fC = new FileContent(m_pp->getFileId(0), m_pp->getLibrary(),
                           m_pp->getCompileSourceFile()->getSymbolTable(),
                           m_pp->getCompileSourceFile()->getErrorContainer(),
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

  CommandLineParser* clp = m_pp->getCompileSourceFile()->getCommandLineParser();
  Precompiled* prec = Precompiled::getSingleton();
  if (prec->isFilePrecompiled(m_pp->getFileId(LINE1),
                              m_pp->getCompileSourceFile()->getSymbolTable())) {
    if (!clp->precompiledCacheAllowed()) return false;
  } else {
    if (!clp->cacheAllowed()) return false;
  }

  PathId cacheFileId = getCacheFileId(BadPathId);
  return cacheFileId && restore(cacheFileId, errorsOnly, 0);
}

bool PPCache::save() {
  if (m_pp->isMacroBody()) return true;

  CommandLineParser* const clp =
      m_pp->getCompileSourceFile()->getCommandLineParser();
  if (!clp->writeCache()) return true;

  FileContent* const fC = m_pp->getFileContent();
  if (fC && (fC->getVObjects().size() > Cache::Capacity)) {
    clp->setCacheAllowed(false);
    Location loc(BadSymbolId);
    Error err(ErrorDefinition::CMD_CACHE_CAPACITY_EXCEEDED, loc);
    m_pp->getCompileSourceFile()->getErrorContainer()->addError(err);
    return false;
  }

  const PathId cacheFileId = getCacheFileId(BadPathId);
  if (!cacheFileId) {
    // Any fake(virtual) file like builtin.sv
    return true;
  }

  // std::cout << "SAVING FILE: " << PathIdPP(cacheFileId) << std::endl;

  FileSystem* const fileSystem = FileSystem::getInstance();
  ErrorContainer* const errorContainer =
      m_pp->getCompileSourceFile()->getErrorContainer();
  SymbolTable* const sourceSymbols =
      m_pp->getCompileSourceFile()->getSymbolTable();
  SymbolTable targetSymbols;

  ::capnp::MallocMessageBuilder message;
  ::PPCache::Builder builder = message.initRoot<::PPCache>();

  // Create header section
  cacheHeader(builder.getHeader(), kSchemaVersion);

  // Cache the macro definitions
  cacheMacros(builder, targetSymbols, *sourceSymbols);

  // Cache the body of the file
  builder.setBody(m_pp->getPreProcessedFileContent().c_str());

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
  cacheIncludeFileInfos(builder, targetSymbols, *sourceSymbols);

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
