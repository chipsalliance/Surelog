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
#include <Surelog/Cache/PPCache.h>
#include <Surelog/Cache/preproc_generated.h>
#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/FileSystem.h>
#include <Surelog/Design/Design.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/TimeInfo.h>
#include <Surelog/Library/Library.h>
#include <Surelog/Package/Precompiled.h>
#include <Surelog/SourceCompile/CompilationUnit.h>
#include <Surelog/SourceCompile/CompileSourceFile.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/MacroInfo.h>
#include <Surelog/SourceCompile/PreprocessFile.h>
#include <Surelog/SourceCompile/SymbolTable.h>

#include <iostream>

namespace SURELOG {
static constexpr std::string_view FlbSchemaVersion = "1.5";
static constexpr std::string_view UnknownRawPath = "<unknown>";

PPCache::PPCache(PreprocessFile* pp) : m_pp(pp) {}

PathId PPCache::getCacheFileId_(PathId sourceFileId) const {
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

template <class T>
static bool compareVectors(std::vector<T> a, std::vector<T> b) {
  std::sort(a.begin(), a.end());
  std::sort(b.begin(), b.end());
  return (a == b);
}

bool PPCache::restore_(PathId cacheFileId, const std::vector<char>& content,
                       bool errorsOnly, int recursionDepth) {
  if (content.empty()) return false;
  FileSystem* const fileSystem = FileSystem::getInstance();

  const MACROCACHE::PPCache* ppcache = MACROCACHE::GetPPCache(content.data());
  // std::cout << "RESTORING FILE: " << cacheFileName << std::endl;
  SymbolTable cacheSymbols;
  restoreSymbols(ppcache->symbols(), &cacheSymbols);

  restoreErrors(ppcache->errors(), &cacheSymbols,
                m_pp->getCompileSourceFile()->getErrorContainer(),
                m_pp->getCompileSourceFile()->getSymbolTable());

  // Always restore the macros
  const flatbuffers::Vector<flatbuffers::Offset<MACROCACHE::Macro>>* macros =
      ppcache->macros();
  for (const MACROCACHE::Macro* macro : *macros) {
    // std::cout << "RESTORING MACRO: " << macro->name()->str() << std::endl;
    std::vector<std::string> args;
    for (const auto* macro_arg : *macro->arguments()) {
      args.emplace_back(macro_arg->string_view());
    }
    std::vector<std::string> tokens;
    tokens.reserve(macro->tokens()->size());
    for (const auto* macro_token : *macro->tokens()) {
      tokens.emplace_back(macro_token->string_view());
    }
    m_pp->recordMacro(
        cacheSymbols.getSymbol(SymbolId(macro->name_id(), UnknownRawPath)),
        fileSystem->toPathId(fileSystem->remap(cacheSymbols.getSymbol(
                                 SymbolId(macro->file_id(), UnknownRawPath))),
                             m_pp->getCompileSourceFile()->getSymbolTable()),
        macro->start_line(), macro->start_column(), macro->end_line(),
        macro->end_column(), args, tokens);
  }

  /* Restore `timescale directives */
  if (!errorsOnly) {
    for (const CACHE::TimeInfo* fbtimeinfo : *ppcache->time_info()) {
      TimeInfo timeInfo;
      timeInfo.m_type = (TimeInfo::Type)fbtimeinfo->type();
      timeInfo.m_fileId = fileSystem->toPathId(
          fileSystem->remap(cacheSymbols.getSymbol(
              SymbolId(fbtimeinfo->file_id(), UnknownRawPath))),
          m_pp->getCompileSourceFile()->getSymbolTable());
      timeInfo.m_line = fbtimeinfo->line();
      timeInfo.m_timeUnit = (TimeInfo::Unit)fbtimeinfo->time_unit();
      timeInfo.m_timeUnitValue = fbtimeinfo->time_unit_value();
      timeInfo.m_timePrecision = (TimeInfo::Unit)fbtimeinfo->time_precision();
      timeInfo.m_timePrecisionValue = fbtimeinfo->time_precision_value();
      m_pp->getCompilationUnit()->recordTimeInfo(timeInfo);
    }
  }

  /* Restore file line info */
  if (recursionDepth == 0) {
    const auto* lineinfos = ppcache->line_translation_vec();
    for (const MACROCACHE::LineTranslationInfo* lineinfo : *lineinfos) {
      PathId pretendFileId = fileSystem->toPathId(
          fileSystem->remap(cacheSymbols.getSymbol(
              SymbolId(lineinfo->pretend_file_id(), UnknownRawPath))),
          m_pp->getCompileSourceFile()->getSymbolTable());
      PreprocessFile::LineTranslationInfo lineFileInfo(
          pretendFileId, lineinfo->original_line(), lineinfo->pretend_line());
      m_pp->addLineTranslationInfo(lineFileInfo);
    }
  }

  /* Restore include file info */
  if (recursionDepth == 0) m_pp->clearIncludeFileInfo();
  for (const auto* incinfo : *ppcache->include_file_info()) {
    SymbolId sectionSymbolId =
        m_pp->getCompileSourceFile()->getSymbolTable()->copyFrom(
            SymbolId(incinfo->section_symbol_id(), "<unknown"), &cacheSymbols);
    PathId sectionFileId =
        fileSystem->toPathId(fileSystem->remap(cacheSymbols.getSymbol(SymbolId(
                                 incinfo->section_file_id(), UnknownRawPath))),
                             m_pp->getCompileSourceFile()->getSymbolTable());
    // std::cout << "read sectionFile: " << sectionFileName << " s:" <<
    // incinfo->m_sectionStartLine() << " o:" << incinfo->m_originalLine() <<
    // " t:" << incinfo->m_type() << "\n";
    m_pp->addIncludeFileInfo(
        static_cast<IncludeFileInfo::Context>(incinfo->context()),
        incinfo->section_start_line(), sectionSymbolId, sectionFileId,
        incinfo->original_start_line(), incinfo->original_start_column(),
        incinfo->original_end_line(), incinfo->original_end_column(),
        static_cast<IncludeFileInfo::Action>(incinfo->action()),
        incinfo->index_opening(), incinfo->index_closing());
  }

  // File Body
  if (!errorsOnly) {
    if (ppcache->body() && !ppcache->body()->string_view().empty()) {
      m_pp->append(ppcache->body()->str());
    }
  }
  // FileContent
  FileContent* fileContent = m_pp->getFileContent();
  if (fileContent == nullptr) {
    fileContent = new FileContent(
        m_pp->getFileId(0), m_pp->getLibrary(),
        m_pp->getCompileSourceFile()->getSymbolTable(),
        m_pp->getCompileSourceFile()->getErrorContainer(), nullptr, BadPathId);
    m_pp->setFileContent(fileContent);
    m_pp->getCompileSourceFile()->getCompiler()->getDesign()->addPPFileContent(
        m_pp->getFileId(0), fileContent);
  }
  if (!errorsOnly) {
    auto objects = ppcache->objects();
    restoreVObjects(objects, cacheSymbols,
                    m_pp->getCompileSourceFile()->getSymbolTable(),
                    m_pp->getFileId(0), fileContent);
  }

  return true;
}

bool PPCache::checkCacheIsValid_(PathId cacheFileId,
                                 const std::vector<char>& content) const {
  if (!cacheFileId || content.empty()) return false;

  CommandLineParser* clp = m_pp->getCompileSourceFile()->getCommandLineParser();
  if (!clp->cacheAllowed() || m_pp->isMacroBody()) return false;

  if (!MACROCACHE::PPCacheBufferHasIdentifier(content.data())) {
    return false;
  }

  FileSystem* const fileSystem = FileSystem::getInstance();
  SymbolTable* symbolTable = m_pp->getCompileSourceFile()->getSymbolTable();

  const MACROCACHE::PPCache* ppcache = MACROCACHE::GetPPCache(content.data());
  const auto header = ppcache->header();

  Precompiled* prec = Precompiled::getSingleton();
  if (prec->isFilePrecompiled(m_pp->getFileId(LINE1), symbolTable)) {
    // For precompiled, check only the signature & version (so using
    // BadPathId instead of the actual arguments)
    return checkIfCacheIsValid(header, FlbSchemaVersion, BadPathId, BadPathId);
  }

  if (!checkIfCacheIsValid(header, FlbSchemaVersion, cacheFileId,
                           m_pp->getFileId(LINE1))) {
    return false;
  }

  if (clp->parseOnly() || clp->lowMem()) return true;

  const auto cacheSymbols = ppcache->symbols();

  // Check if the defines match
  const auto& defineList = clp->getDefineList();
  std::vector<std::string> define_vec;
  define_vec.reserve(defineList.size());
  for (const auto& definePair : defineList) {
    std::string spath =
        m_pp->getSymbol(definePair.first) + "=" + definePair.second;
    define_vec.emplace_back(std::move(spath));
  }

  std::vector<std::string> cache_define_vec;
  if (const auto cached_defines = ppcache->cmd_define_options()) {
    cache_define_vec.reserve(cached_defines->size());
    for (const auto* cmd_define_option : *cached_defines) {
      cache_define_vec.emplace_back(cmd_define_option->string_view());
    }
  }
  if (!compareVectors(define_vec, cache_define_vec)) {
    return false;
  }

  // Check if the includes resolve to the *same* path
  if (const auto include_file_infos = ppcache->include_file_info()) {
    PathIdSet includedFileIds;
    for (const auto* incinfo : *include_file_infos) {
      IncludeFileInfo::Context context =
          static_cast<IncludeFileInfo::Context>(incinfo->context());
      IncludeFileInfo::Action action =
          static_cast<IncludeFileInfo::Action>(incinfo->action());
      if ((context == IncludeFileInfo::Context::INCLUDE) &&
          (action == IncludeFileInfo::Action::PUSH)) {
        std::string cachedFile = fileSystem->remap(
            cacheSymbols->Get(incinfo->section_file_id())->string_view());
        PathId cachedFileId = fileSystem->toPathId(
            cachedFile, m_pp->getCompileSourceFile()->getSymbolTable());
        PathId sessionFileId = fileSystem->locate(
            cacheSymbols->Get(incinfo->section_symbol_id())->string_view(),
            clp->getIncludePaths(),
            m_pp->getCompileSourceFile()->getSymbolTable());
        if (cachedFileId != sessionFileId) {
          return false;  // Symbols don't resolve to the same file!
        }
        includedFileIds.emplace(sessionFileId);
      }
    }

    // Check all includes recursively!
    for (const PathId& includeId : includedFileIds) {
      if (!checkCacheIsValid_(getCacheFileId_(includeId))) {
        return false;
      }
    }
  }

  return true;
}

bool PPCache::checkCacheIsValid_(PathId cacheFileId) const {
  if (!cacheFileId) return false;

  CommandLineParser* clp = m_pp->getCompileSourceFile()->getCommandLineParser();
  if (!clp->cacheAllowed() || m_pp->isMacroBody()) return false;
  if (clp->parseOnly() || clp->lowMem()) return true;

  std::vector<char> content;
  return openFlatBuffers(cacheFileId, content) &&
         checkCacheIsValid_(cacheFileId, content);
}

bool PPCache::isValid() {
  return checkCacheIsValid_(getCacheFileId_(BadPathId));
}

bool PPCache::restore(bool errorsOnly) {
  CommandLineParser* clp = m_pp->getCompileSourceFile()->getCommandLineParser();
  if (!clp->cacheAllowed() || m_pp->isMacroBody()) return false;

  PathId cacheFileId = getCacheFileId_(BadPathId);
  std::vector<char> content;

  return cacheFileId && openFlatBuffers(cacheFileId, content) &&
         checkCacheIsValid_(cacheFileId, content) &&
         restore_(cacheFileId, content, errorsOnly, 0);
}

bool PPCache::save() {
  CommandLineParser* clp = m_pp->getCompileSourceFile()->getCommandLineParser();
  if (!clp->cacheAllowed() || m_pp->isMacroBody()) return true;

  FileSystem* const fileSystem = FileSystem::getInstance();
  FileContent* fcontent = m_pp->getFileContent();
  if (fcontent && (fcontent->getVObjects().size() > Cache::Capacity)) {
    clp->setCacheAllowed(false);
    Location loc(BadSymbolId);
    Error err(ErrorDefinition::CMD_CACHE_CAPACITY_EXCEEDED, loc);
    m_pp->getCompileSourceFile()->getErrorContainer()->addError(err);
    return false;
  }

  PathId cacheFileId = getCacheFileId_(BadPathId);
  if (!cacheFileId) {
    // Any fake(virtual) file like builtin.sv
    return true;
  }

  // std::cout << "SAVING FILE: " << PathIdPP(cacheFileId) << std::endl;

  flatbuffers::FlatBufferBuilder builder(1024);
  SymbolTable cacheSymbols;
  /* Create header section */
  auto header = createHeader(builder, FlbSchemaVersion);

  /* Cache the macro definitions */
  const MacroStorage& macros = m_pp->getMacros();
  std::vector<flatbuffers::Offset<MACROCACHE::Macro>> macro_vec;
  for (const auto& [macroName, infoVec] : macros) {
    for (const auto& info : infoVec) {
      // std::cout << "SAVING MACRO: " << macroName << std::endl;
      MACROCACHE::MacroType type = (info->m_type == MacroInfo::WITH_ARGS)
                                       ? MACROCACHE::MacroType_WITH_ARGS
                                       : MACROCACHE::MacroType_NO_ARGS;
      auto args = builder.CreateVectorOfStrings(info->m_arguments);
      /*
      Debug code for a flatbuffer issue"
      std::cout << "STRING VECTOR CONTENT:\n";
      int index = 0;
      std::cout << "VECTOR SIZE: " << info->m_tokens.size() << std::endl;
      for (auto st : info->m_tokens) {
        std::cout << index << " ST:" << st.size() << " >>>" << st << "<<<"
                  << std::endl;
        index++;
      }
      */
      auto tokens = builder.CreateVectorOfStrings(info->m_tokens);
      macro_vec.emplace_back(MACROCACHE::CreateMacro(
          builder, (RawSymbolId)cacheSymbols.registerSymbol(macroName), type,
          (RawPathId)fileSystem->copy(info->m_fileId, &cacheSymbols),
          info->m_startLine, info->m_startColumn, info->m_endLine,
          info->m_endColumn, args, tokens));
    }
  }
  auto macroList = builder.CreateVector(macro_vec);

  /* Cache the body of the file */
  auto body = builder.CreateString(m_pp->getPreProcessedFileContent());

  /* Cache the errors and canonical symbols */
  ErrorContainer* errorContainer =
      m_pp->getCompileSourceFile()->getErrorContainer();
  PathId subjectFileId = m_pp->getFileId(LINE1);
  auto errorCache = cacheErrors(builder, &cacheSymbols, errorContainer,
                                *m_pp->getCompileSourceFile()->getSymbolTable(),
                                subjectFileId);

  /* Cache the defines on the command line */
  auto defineList = clp->getDefineList();
  std::vector<std::string> define_vec;
  for (auto& definePair : defineList) {
    std::string spath =
        m_pp->getSymbol(definePair.first) + "=" + definePair.second;
    define_vec.emplace_back(std::move(spath));
  }
  auto defines = builder.CreateVectorOfStrings(define_vec);

  /* Cache the `timescale directives */
  auto timeinfoList = m_pp->getCompilationUnit()->getTimeInfo();
  std::vector<flatbuffers::Offset<CACHE::TimeInfo>> timeinfo_vec;
  for (auto& info : timeinfoList) {
    if (info.m_fileId != m_pp->getFileId(0)) continue;
    timeinfo_vec.emplace_back(CACHE::CreateTimeInfo(
        builder, static_cast<uint16_t>(info.m_type),
        (RawPathId)fileSystem->copy(info.m_fileId, &cacheSymbols), info.m_line,
        static_cast<uint16_t>(info.m_timeUnit), info.m_timeUnitValue,
        static_cast<uint16_t>(info.m_timePrecision),
        info.m_timePrecisionValue));
  }
  auto timeinfoFBList = builder.CreateVector(timeinfo_vec);

  /* Cache the fileline info*/
  auto lineTranslationVec = m_pp->getLineTranslationInfo();
  std::vector<flatbuffers::Offset<MACROCACHE::LineTranslationInfo>>
      linetrans_vec;
  for (const auto& info : lineTranslationVec) {
    PathId pretendFileId =
        fileSystem->copy(info.m_pretendFileId, &cacheSymbols);
    linetrans_vec.emplace_back(MACROCACHE::CreateLineTranslationInfo(
        builder, (RawPathId)pretendFileId, info.m_originalLine,
        info.m_pretendLine));
  }
  auto lineinfoFBList = builder.CreateVector(linetrans_vec);

  /* Cache the include info */
  auto includeInfo = m_pp->getIncludeFileInfo();
  std::vector<flatbuffers::Offset<MACROCACHE::IncludeFileInfo>> lineinfo_vec;
  for (IncludeFileInfo& info : includeInfo) {
    SymbolId sectionSymbolId = cacheSymbols.copyFrom(
        info.m_sectionSymbolId, m_pp->getCompileSourceFile()->getSymbolTable());
    PathId sectionFileId =
        fileSystem->copy(info.m_sectionFileId, &cacheSymbols);
    lineinfo_vec.emplace_back(MACROCACHE::CreateIncludeFileInfo(
        builder, static_cast<uint32_t>(info.m_context), info.m_sectionStartLine,
        (RawSymbolId)sectionSymbolId, (RawPathId)sectionFileId,
        info.m_originalStartLine, info.m_originalStartColumn,
        info.m_originalEndLine, info.m_originalEndColumn,
        static_cast<uint32_t>(info.m_action), info.m_indexOpening,
        info.m_indexClosing));
    // std::cout << "save sectionFile: " << sectionFileName << " s:" <<
    // info.m_sectionStartLine << " o:" << info.m_originalLine << " t:" <<
    // info.m_type << "\n";
  }
  auto incinfoFBList = builder.CreateVector(lineinfo_vec);

  /* Cache the design objects */
  std::vector<CACHE::VObject> object_vec = cacheVObjects(
      fcontent, &cacheSymbols, *m_pp->getCompileSourceFile()->getSymbolTable(),
      m_pp->getFileId(0));
  auto objectList = builder.CreateVectorOfStructs(object_vec);

  auto symbolVec = builder.CreateVectorOfStrings(cacheSymbols.getSymbols());
  /* Create Flatbuffers */
  auto ppcache = MACROCACHE::CreatePPCache(
      builder, header, macroList, body, errorCache, symbolVec, defines,
      timeinfoFBList, lineinfoFBList, incinfoFBList, objectList);
  FinishPPCacheBuffer(builder, ppcache);

  /* Save Flatbuffer */
  bool status = saveFlatbuffers(builder, cacheFileId,
                                m_pp->getCompileSourceFile()->getSymbolTable());

  return status;
}
}  // namespace SURELOG
