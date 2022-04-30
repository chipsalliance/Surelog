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
#include <Surelog/Utils/FileUtils.h>

namespace SURELOG {
namespace fs = std::filesystem;

PPCache::PPCache(PreprocessFile* pp) : m_pp(pp), m_isPrecompiled(false) {}

static const char FlbSchemaVersion[] = "1.1";

fs::path PPCache::getCacheFileName_(const fs::path& requested_file) {
  Precompiled* prec = Precompiled::getSingleton();
  CommandLineParser* clp = m_pp->getCompileSourceFile()->getCommandLineParser();
  SymbolId cacheDirId = clp->getCacheDir();

  const fs::path svFileName =
      requested_file.empty() ? m_pp->getFileName(LINE1) : requested_file;

  const fs::path baseFileName = FileUtils::basename(svFileName);
  const fs::path filePath = FileUtils::getPathName(svFileName);
  fs::path hashedPath =
      clp->noCacheHash() ? filePath : fs::path(FileUtils::hashPath(filePath));
  fs::path fileName = hashedPath / baseFileName;
  if (clp->parseOnly()) {
    fileName = filePath / baseFileName;
  }
  if (prec->isFilePrecompiled(baseFileName)) {
    fs::path packageRepDir = m_pp->getSymbol(m_pp->getCompileSourceFile()
                                                 ->getCommandLineParser()
                                                 ->getPrecompiledDir());
    cacheDirId = m_pp->getCompileSourceFile()
                     ->getCommandLineParser()
                     ->mutableSymbolTable()
                     ->registerSymbol(packageRepDir.string());
    m_isPrecompiled = true;
    fileName = baseFileName;
    hashedPath = "";
  }

  fs::path cacheDirName = m_pp->getSymbol(cacheDirId);

  Library* lib = m_pp->getLibrary();
  std::string libName = lib->getName();
  if (clp->parseOnly()) {
    libName = "";
  }
  fs::path cacheFileName =
      cacheDirName / libName / (fileName.string() + ".slpp");
  FileUtils::mkDirs(cacheDirName / libName / hashedPath);
  return cacheFileName;
}

template <class T>
static bool compareVectors(std::vector<T> a, std::vector<T> b) {
  std::sort(a.begin(), a.end());
  std::sort(b.begin(), b.end());
  return (a == b);
}

bool PPCache::restore_(const fs::path& cacheFileName, bool errorsOnly) {
  uint8_t* const buffer_pointer = openFlatBuffers(cacheFileName);
  if (buffer_pointer == nullptr) return false;

  const MACROCACHE::PPCache* ppcache = MACROCACHE::GetPPCache(buffer_pointer);
  // Always restore the macros
  const flatbuffers::Vector<flatbuffers::Offset<MACROCACHE::Macro>>* macros =
      ppcache->macros();
  for (unsigned int i = 0; i < macros->size(); i++) {
    const MACROCACHE::Macro* macro = macros->Get(i);
    std::vector<std::string> args;
    std::vector<std::string> tokens;
    for (unsigned int j = 0; j < macro->arguments()->size(); j++) {
      args.push_back(macro->arguments()->Get(j)->str());
    }
    for (unsigned int j = 0; j < macro->tokens()->size(); j++) {
      tokens.push_back(macro->tokens()->Get(j)->str());
    }
    m_pp->recordMacro(macro->name()->str(), macro->start_line(),
                      macro->start_column(), macro->end_line(),
                      macro->end_column(), args, tokens);
  }

  SymbolTable canonicalSymbols;
  restoreErrors(ppcache->errors(), ppcache->symbols(), canonicalSymbols,
                m_pp->getCompileSourceFile()->getErrorContainer(),
                m_pp->getCompileSourceFile()->getSymbolTable());

  /* Restore `timescale directives */
  if (!errorsOnly) {
    const flatbuffers::Vector<flatbuffers::Offset<CACHE::TimeInfo>>* timeinfos =
        ppcache->time_info();
    for (unsigned int i = 0; i < timeinfos->size(); i++) {
      const CACHE::TimeInfo* fbtimeinfo = timeinfos->Get(i);
      TimeInfo timeInfo;
      timeInfo.m_type = (TimeInfo::Type)fbtimeinfo->type();
      timeInfo.m_fileId = fbtimeinfo->file_id();
      timeInfo.m_line = fbtimeinfo->line();
      timeInfo.m_timeUnit = (TimeInfo::Unit)fbtimeinfo->time_unit();
      timeInfo.m_timeUnitValue = fbtimeinfo->time_unit_value();
      timeInfo.m_timePrecision = (TimeInfo::Unit)fbtimeinfo->time_precision();
      timeInfo.m_timePrecisionValue = fbtimeinfo->time_precision_value();
      m_pp->getCompilationUnit()->recordTimeInfo(timeInfo);
    }
  }
  /* Restore file line info */
  if (!errorsOnly) {
    const flatbuffers::Vector<
        flatbuffers::Offset<MACROCACHE::LineTranslationInfo>>* lineinfos =
        ppcache->line_translation_vec();
    for (unsigned int i = 0; i < lineinfos->size(); i++) {
      const MACROCACHE::LineTranslationInfo* lineinfo = lineinfos->Get(i);
      const fs::path pretendFileName = lineinfo->pretend_file()->str();
      PreprocessFile::LineTranslationInfo lineFileInfo(
          m_pp->getCompileSourceFile()->getSymbolTable()->registerSymbol(
              pretendFileName.string()),
          lineinfo->original_line(), lineinfo->pretend_line());
      m_pp->addLineTranslationInfo(lineFileInfo);
    }
  }
  /* Restore include file info */
  if (!errorsOnly) {
    const flatbuffers::Vector<flatbuffers::Offset<MACROCACHE::IncludeFileInfo>>*
        incinfos = ppcache->include_file_info();
    for (unsigned int i = 0; i < incinfos->size(); i++) {
      const MACROCACHE::IncludeFileInfo* incinfo = incinfos->Get(i);
      const fs::path sectionFileName = incinfo->section_file()->str();
      // std::cout << "read sectionFile: " << sectionFileName << " s:" <<
      // incinfo->m_sectionStartLine() << " o:" << incinfo->m_originalLine() <<
      // " t:" << incinfo->m_type() << "\n";
      m_pp->getIncludeFileInfo().emplace_back(
          static_cast<IncludeFileInfo::Context>(incinfo->context()),
          incinfo->section_start_line(),
          m_pp->getCompileSourceFile()->getSymbolTable()->registerSymbol(
              sectionFileName.string()),
          incinfo->original_start_line(), incinfo->original_start_column(),
          incinfo->original_end_line(), incinfo->original_end_column(),
          static_cast<IncludeFileInfo::Action>(incinfo->action()),
          incinfo->index_opening(), incinfo->index_closing());
    }
  }
  // Includes
  auto includes = ppcache->includes();
  if (includes) {
    for (unsigned int i = 0; i < includes->size(); i++) {
      auto include = includes->Get(i);
      restore_(getCacheFileName_(include->str()), errorsOnly);
    }
  }
  // File Body
  if (!errorsOnly) {
    if (ppcache->body() && !ppcache->body()->string_view().empty()) {
      m_pp->append(ppcache->body()->str());
    }
  }
  // FileContent
  if (!errorsOnly) {
    FileContent* fileContent = m_pp->getFileContent();
    if (fileContent == nullptr) {
      fileContent = new FileContent(
          m_pp->getFileId(0), m_pp->getLibrary(),
          m_pp->getCompileSourceFile()->getSymbolTable(),
          m_pp->getCompileSourceFile()->getErrorContainer(), nullptr, 0);
      m_pp->setFileContent(fileContent);
      m_pp->getCompileSourceFile()
          ->getCompiler()
          ->getDesign()
          ->addPPFileContent(m_pp->getFileId(0), fileContent);
    }

    auto objects = ppcache->objects();
    restoreVObjects(objects, canonicalSymbols,
                    *m_pp->getCompileSourceFile()->getSymbolTable(),
                    m_pp->getFileId(0), fileContent);
  }

  delete[] buffer_pointer;
  return true;
}

bool PPCache::checkCacheIsValid_(const fs::path& cacheFileName) {
  CommandLineParser* clp = m_pp->getCompileSourceFile()->getCommandLineParser();
  if (clp->parseOnly()) {
    return true;
  }
  if (clp->lowMem()) {
    return true;
  }
  uint8_t* buffer_pointer = openFlatBuffers(cacheFileName);
  if (buffer_pointer == nullptr) {
    delete[] buffer_pointer;
    return false;
  }
  if (!MACROCACHE::PPCacheBufferHasIdentifier(buffer_pointer)) {
    delete[] buffer_pointer;
    return false;
  }
  if (clp->noCacheHash()) {
    return true;
  }
  const MACROCACHE::PPCache* ppcache = MACROCACHE::GetPPCache(buffer_pointer);
  auto header = ppcache->header();

  if (!m_isPrecompiled) {
    if (!checkIfCacheIsValid(header, FlbSchemaVersion, cacheFileName)) {
      delete[] buffer_pointer;
      return false;
    }

    /* Cache the include paths list */
    auto includePathList =
        m_pp->getCompileSourceFile()->getCommandLineParser()->getIncludePaths();
    std::vector<fs::path> include_path_vec;
    for (auto path : includePathList) {
      fs::path spath = m_pp->getSymbol(path);
      include_path_vec.push_back(spath);
    }

    std::vector<fs::path> cache_include_path_vec;
    for (unsigned int i = 0; i < ppcache->cmd_include_paths()->size(); i++) {
      const fs::path path = ppcache->cmd_include_paths()->Get(i)->str();
      cache_include_path_vec.push_back(path);
    }
    if (!compareVectors(include_path_vec, cache_include_path_vec)) {
      delete[] buffer_pointer;
      return false;
    }

    /* Cache the defines on the command line */
    auto defineList =
        m_pp->getCompileSourceFile()->getCommandLineParser()->getDefineList();
    std::vector<std::string> define_vec;
    for (const auto& definePair : defineList) {
      std::string spath =
          m_pp->getSymbol(definePair.first) + "=" + definePair.second;
      define_vec.push_back(spath);
    }

    std::vector<std::string> cache_define_vec;
    for (unsigned int i = 0; i < ppcache->cmd_define_options()->size(); i++) {
      const std::string path = ppcache->cmd_define_options()->Get(i)->str();
      cache_define_vec.push_back(path);
    }
    if (!compareVectors(define_vec, cache_define_vec)) {
      delete[] buffer_pointer;
      return false;
    }

    /* All includes*/
    auto includes = ppcache->includes();
    if (includes)
      for (unsigned int i = 0; i < includes->size(); i++) {
        auto include = includes->Get(i);
        if (!checkCacheIsValid_(getCacheFileName_(include->str()))) {
          delete[] buffer_pointer;
          return false;
        }
      }
  }

  delete[] buffer_pointer;
  return true;
}

bool PPCache::restore(bool errorsOnly) {
  bool cacheAllowed =
      m_pp->getCompileSourceFile()->getCommandLineParser()->cacheAllowed();
  if (!cacheAllowed) return false;
  if (m_pp->isMacroBody()) return false;
  fs::path cacheFileName = getCacheFileName_();
  if (!checkCacheIsValid_(cacheFileName)) {
    return false;
  }
  return restore_(cacheFileName, errorsOnly);
}

bool PPCache::save() {
  bool cacheAllowed =
      m_pp->getCompileSourceFile()->getCommandLineParser()->cacheAllowed();
  if (!cacheAllowed) return false;
  FileContent* fcontent = m_pp->getFileContent();
  if (fcontent) {
    if (fcontent->getVObjects().size() > Cache::Capacity) {
      m_pp->getCompileSourceFile()->getCommandLineParser()->setCacheAllowed(
          false);
      Location loc(0);
      Error err(ErrorDefinition::CMD_CACHE_CAPACITY_EXCEEDED, loc);
      m_pp->getCompileSourceFile()->getErrorContainer()->addError(err);
      return false;
    }
  }
  const fs::path& svFileName = m_pp->getFileName(LINE1);
  const fs::path& origFileName = svFileName;
  const fs::path& cacheFileName = getCacheFileName_();

  if (m_pp->isMacroBody()) return false;

  flatbuffers::FlatBufferBuilder builder(1024);
  /* Create header section */
  auto header = createHeader(builder, FlbSchemaVersion, origFileName);

  /* Cache the macro definitions */
  const MacroStorage& macros = m_pp->getMacros();
  std::vector<flatbuffers::Offset<MACROCACHE::Macro>> macro_vec;
  for (const auto& [macroName, info] : macros) {
    auto name = builder.CreateString(macroName);
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
    macro_vec.push_back(MACROCACHE::CreateMacro(
        builder, name, type, info->m_startLine, info->m_startColumn,
        info->m_endLine, info->m_endColumn, args, tokens));
  }
  auto macroList = builder.CreateVector(macro_vec);

  /* Cache Included files */
  std::vector<std::string> include_vec;
  std::set<PreprocessFile*> included;
  m_pp->collectIncludedFiles(included);
  for (PreprocessFile* pp : included) {
    fs::path svFileName = m_pp->getSymbol(pp->getRawFileId());
    include_vec.push_back(svFileName.string());
  }
  auto includeList = builder.CreateVectorOfStrings(include_vec);

  /* Cache the body of the file */
  auto body = builder.CreateString(m_pp->getPreProcessedFileContent());

  /* Cache the errors and canonical symbols */
  ErrorContainer* errorContainer =
      m_pp->getCompileSourceFile()->getErrorContainer();
  SymbolId subjectFileId = m_pp->getFileId(LINE1);
  SymbolTable canonicalSymbols;
  auto errorSymbolPair = cacheErrors(
      builder, canonicalSymbols, errorContainer,
      m_pp->getCompileSourceFile()->getSymbolTable(), subjectFileId);

  /* Cache the include paths list */
  auto includePathList =
      m_pp->getCompileSourceFile()->getCommandLineParser()->getIncludePaths();
  std::vector<std::string> include_path_vec;
  for (auto path : includePathList) {
    std::string spath = m_pp->getSymbol(path);
    include_path_vec.push_back(spath);
  }
  auto incPaths = builder.CreateVectorOfStrings(include_path_vec);

  /* Cache the defines on the command line */
  auto defineList =
      m_pp->getCompileSourceFile()->getCommandLineParser()->getDefineList();
  std::vector<std::string> define_vec;
  for (auto& definePair : defineList) {
    std::string spath =
        m_pp->getSymbol(definePair.first) + "=" + definePair.second;
    define_vec.push_back(spath);
  }
  auto defines = builder.CreateVectorOfStrings(define_vec);

  /* Cache the `timescale directives */
  auto timeinfoList = m_pp->getCompilationUnit()->getTimeInfo();
  std::vector<flatbuffers::Offset<CACHE::TimeInfo>> timeinfo_vec;
  for (auto& info : timeinfoList) {
    if (info.m_fileId != m_pp->getFileId(0)) continue;
    auto timeInfo = CACHE::CreateTimeInfo(
        builder, static_cast<uint16_t>(info.m_type),
        canonicalSymbols.getId(
            m_pp->getCompileSourceFile()->getSymbolTable()->getSymbol(
                info.m_fileId)),
        info.m_line, static_cast<uint16_t>(info.m_timeUnit),
        info.m_timeUnitValue, static_cast<uint16_t>(info.m_timePrecision),
        info.m_timePrecisionValue);
    timeinfo_vec.push_back(timeInfo);
  }
  auto timeinfoFBList = builder.CreateVector(timeinfo_vec);

  /* Cache the fileline info*/
  auto lineTranslationVec = m_pp->getLineTranslationInfo();
  std::vector<flatbuffers::Offset<MACROCACHE::LineTranslationInfo>>
      linetrans_vec;
  for (auto info : lineTranslationVec) {
    fs::path pretendFileName =
        m_pp->getCompileSourceFile()->getSymbolTable()->getSymbol(
            info.m_pretendFileId);
    auto lineInfo = MACROCACHE::CreateLineTranslationInfo(
        builder, builder.CreateString(pretendFileName.string()),
        info.m_originalLine, info.m_pretendLine);
    linetrans_vec.push_back(lineInfo);
  }
  auto lineinfoFBList = builder.CreateVector(linetrans_vec);

  /* Cache the include info */
  auto includeInfo = m_pp->getIncludeFileInfo();
  std::vector<flatbuffers::Offset<MACROCACHE::IncludeFileInfo>> lineinfo_vec;
  for (IncludeFileInfo& info : includeInfo) {
    fs::path sectionFileName =
        m_pp->getCompileSourceFile()->getSymbolTable()->getSymbol(
            info.m_sectionFile);
    auto incInfo = MACROCACHE::CreateIncludeFileInfo(
        builder, static_cast<uint32_t>(info.m_context), info.m_sectionStartLine,
        builder.CreateString(sectionFileName.string()),
        info.m_originalStartLine, info.m_originalStartColumn,
        info.m_originalEndLine, info.m_originalEndColumn,
        static_cast<uint32_t>(info.m_action), info.m_indexOpening,
        info.m_indexClosing);
    // std::cout << "save sectionFile: " << sectionFileName << " s:" <<
    // info.m_sectionStartLine << " o:" << info.m_originalLine << " t:" <<
    // info.m_type << "\n";
    lineinfo_vec.push_back(incInfo);
  }
  auto incinfoFBList = builder.CreateVector(lineinfo_vec);

  /* Cache the design objects */
  std::vector<CACHE::VObject> object_vec = cacheVObjects(
      fcontent, canonicalSymbols,
      *m_pp->getCompileSourceFile()->getSymbolTable(), m_pp->getFileId(0));
  auto objectList = builder.CreateVectorOfStructs(object_vec);

  /* Create Flatbuffers */
  auto ppcache = MACROCACHE::CreatePPCache(
      builder, header, macroList, includeList, body, errorSymbolPair.first,
      errorSymbolPair.second, incPaths, defines, timeinfoFBList, lineinfoFBList,
      incinfoFBList, objectList);
  FinishPPCacheBuffer(builder, ppcache);

  /* Save Flatbuffer */
  bool status = saveFlatbuffers(builder, cacheFileName);

  return status;
}
}  // namespace SURELOG
