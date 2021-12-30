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
#include "Cache/PPCache.h"

#include <sys/stat.h>
#include <sys/types.h>

#include <algorithm>
#include <cstdio>
#include <ctime>

#include "Cache/Cache.h"
#include "Cache/preproc_generated.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Package/Precompiled.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "Utils/FileUtils.h"
#include "Utils/StringUtils.h"
#include "flatbuffers/util.h"

namespace SURELOG {
PPCache::PPCache(PreprocessFile* pp) : m_pp(pp), m_isPrecompiled(false) {}

static const char FlbSchemaVersion[] = "1.0";

std::string PPCache::getCacheFileName_(const std::string& requested_file) {
  Precompiled* prec = Precompiled::getSingleton();
  SymbolId cacheDirId =
      m_pp->getCompileSourceFile()->getCommandLineParser()->getCacheDir();

  const std::string svFileName =
      requested_file.empty() ? m_pp->getFileName(LINE1) : requested_file;

  const std::string& baseFileName = FileUtils::basename(svFileName);
  const std::string& filePath = FileUtils::getPathName(svFileName);
  std::string hashedPath = FileUtils::hashPath(filePath);
  std::string fileName = hashedPath + baseFileName;
  if (m_pp->getCompileSourceFile()->getCommandLineParser()->parseOnly()) {
    fileName = filePath + baseFileName;
  }
  if (prec->isFilePrecompiled(baseFileName)) {
    std::string packageRepDir = m_pp->getSymbol(m_pp->getCompileSourceFile()
                                                    ->getCommandLineParser()
                                                    ->getPrecompiledDir());
    cacheDirId = m_pp->getCompileSourceFile()
                     ->getCommandLineParser()
                     ->mutableSymbolTable()
                     ->registerSymbol(packageRepDir);
    m_isPrecompiled = true;
    fileName = baseFileName;
    hashedPath = "";
  }

  std::string cacheDirName = m_pp->getSymbol(cacheDirId);

  Library* lib = m_pp->getLibrary();
  std::string libName = lib->getName() + "/";
  if (m_pp->getCompileSourceFile()->getCommandLineParser()->parseOnly()) {
    libName = "";
  }
  std::string cacheFileName = cacheDirName + libName + fileName + ".slpp";
  FileUtils::mkDir(cacheDirName + libName);
  FileUtils::mkDir(cacheDirName + libName + hashedPath);
  return cacheFileName;
}

template <class T>
static bool compareVectors(std::vector<T> a, std::vector<T> b) {
  std::sort(a.begin(), a.end());
  std::sort(b.begin(), b.end());
  return (a == b);
}

bool PPCache::restore_(const std::string& cacheFileName, bool errorsOnly) {
  uint8_t* const buffer_pointer = openFlatBuffers(cacheFileName);
  if (buffer_pointer == NULL) return false;

  const MACROCACHE::PPCache* ppcache = MACROCACHE::GetPPCache(buffer_pointer);
  if (!errorsOnly) {
    const flatbuffers::Vector<flatbuffers::Offset<MACROCACHE::Macro>>* macros =
        ppcache->m_macros();
    for (unsigned int i = 0; i < macros->size(); i++) {
      const MACROCACHE::Macro* macro = macros->Get(i);
      std::vector<std::string> args;
      std::vector<std::string> tokens;
      for (unsigned int j = 0; j < macro->m_arguments()->size(); j++) {
        args.push_back(macro->m_arguments()->Get(j)->str());
      }
      for (unsigned int j = 0; j < macro->m_tokens()->size(); j++) {
        tokens.push_back(macro->m_tokens()->Get(j)->str());
      }
      m_pp->recordMacro(macro->m_name()->str(), macro->m_line(),
                        macro->m_column(), args, tokens);
    }
  }
  SymbolTable canonicalSymbols;
  restoreErrors(ppcache->m_errors(), ppcache->m_symbols(), canonicalSymbols,
                m_pp->getCompileSourceFile()->getErrorContainer(),
                m_pp->getCompileSourceFile()->getSymbolTable());

  /* Restore `timescale directives */
  if (!errorsOnly) {
    const flatbuffers::Vector<flatbuffers::Offset<CACHE::TimeInfo>>* timeinfos =
        ppcache->m_timeInfo();
    for (unsigned int i = 0; i < timeinfos->size(); i++) {
      const CACHE::TimeInfo* fbtimeinfo = timeinfos->Get(i);
      TimeInfo timeInfo;
      timeInfo.m_type = (TimeInfo::Type)fbtimeinfo->m_type();
      timeInfo.m_fileId = fbtimeinfo->m_fileId();
      timeInfo.m_line = fbtimeinfo->m_line();
      timeInfo.m_timeUnit = (TimeInfo::Unit)fbtimeinfo->m_timeUnit();
      timeInfo.m_timeUnitValue = fbtimeinfo->m_timeUnitValue();
      timeInfo.m_timePrecision = (TimeInfo::Unit)fbtimeinfo->m_timePrecision();
      timeInfo.m_timePrecisionValue = fbtimeinfo->m_timePrecisionValue();
      m_pp->getCompilationUnit()->recordTimeInfo(timeInfo);
    }
  }
  /* Restore file line info */
  if (!errorsOnly) {
    const flatbuffers::Vector<
        flatbuffers::Offset<MACROCACHE::LineTranslationInfo>>* lineinfos =
        ppcache->m_lineTranslationVec();
    for (unsigned int i = 0; i < lineinfos->size(); i++) {
      const MACROCACHE::LineTranslationInfo* lineinfo = lineinfos->Get(i);
      const std::string pretendFileName = lineinfo->m_pretendFile()->str();
      PreprocessFile::LineTranslationInfo lineFileInfo(
          m_pp->getCompileSourceFile()->getSymbolTable()->registerSymbol(
              pretendFileName),
          lineinfo->m_originalLine(), lineinfo->m_pretendLine());
      m_pp->addLineTranslationInfo(lineFileInfo);
    }
  }
  /* Restore include file info */
  if (!errorsOnly) {
    const flatbuffers::Vector<flatbuffers::Offset<MACROCACHE::IncludeFileInfo>>*
        incinfos = ppcache->m_includeFileInfo();
    for (unsigned int i = 0; i < incinfos->size(); i++) {
      const MACROCACHE::IncludeFileInfo* incinfo = incinfos->Get(i);
      const std::string sectionFileName = incinfo->m_sectionFile()->str();
      // std::cout << "read sectionFile: " << sectionFileName << " s:" <<
      // incinfo->m_sectionStartLine() << " o:" << incinfo->m_originalLine() <<
      // " t:" << incinfo->m_type() << "\n";
      IncludeFileInfo inf(
          incinfo->m_sectionStartLine(),
          m_pp->getCompileSourceFile()->getSymbolTable()->registerSymbol(
              sectionFileName),
          incinfo->m_originalLine(), (IncludeFileInfo::Action)incinfo->m_type(),
          incinfo->m_indexOpening(), incinfo->m_indexClosing());
      m_pp->getIncludeFileInfo().push_back(inf);
    }
  }
  // Includes
  auto includes = ppcache->m_includes();
  if (includes) {
    for (unsigned int i = 0; i < includes->size(); i++) {
      auto include = includes->Get(i);
      restore_(getCacheFileName_(include->str()), errorsOnly);
    }
  }
  // File Body
  if (!errorsOnly) {
    if (ppcache->m_body() && !ppcache->m_body()->string_view().empty()) {
      m_pp->append(ppcache->m_body()->str());
    }
  }
  // FileContent
  if (!errorsOnly) {
    FileContent* fileContent = m_pp->getFileContent();
    if (fileContent == NULL) {
      fileContent = new FileContent(
          m_pp->getFileId(0), m_pp->getLibrary(),
          m_pp->getCompileSourceFile()->getSymbolTable(),
          m_pp->getCompileSourceFile()->getErrorContainer(), NULL, 0);
      m_pp->setFileContent(fileContent);
      m_pp->getCompileSourceFile()
          ->getCompiler()
          ->getDesign()
          ->addPPFileContent(m_pp->getFileId(0), fileContent);
    }

    auto objects = ppcache->m_objects();
    restoreVObjects(objects, canonicalSymbols,
                    *m_pp->getCompileSourceFile()->getSymbolTable(),
                    m_pp->getFileId(0), fileContent);
  }

  delete[] buffer_pointer;
  return true;
}

bool PPCache::checkCacheIsValid_(const std::string& cacheFileName) {
  CommandLineParser* clp = m_pp->getCompileSourceFile()->getCommandLineParser();
  if (clp->parseOnly()) {
    return true;
  }
  if (clp->lowMem()) {
    return true;
  }
  uint8_t* buffer_pointer = openFlatBuffers(cacheFileName);
  if (buffer_pointer == NULL) {
    delete[] buffer_pointer;
    return false;
  }
  if (!MACROCACHE::PPCacheBufferHasIdentifier(buffer_pointer)) {
    delete[] buffer_pointer;
    return false;
  }

  const MACROCACHE::PPCache* ppcache = MACROCACHE::GetPPCache(buffer_pointer);
  auto header = ppcache->m_header();

  if (!m_isPrecompiled) {
    if (!checkIfCacheIsValid(header, FlbSchemaVersion, cacheFileName)) {
      delete[] buffer_pointer;
      return false;
    }

    /* Cache the include paths list */
    auto includePathList =
        m_pp->getCompileSourceFile()->getCommandLineParser()->getIncludePaths();
    std::vector<std::string> include_path_vec;
    for (auto path : includePathList) {
      std::string spath = m_pp->getSymbol(path);
      include_path_vec.push_back(spath);
    }

    std::vector<std::string> cache_include_path_vec;
    for (unsigned int i = 0; i < ppcache->m_cmd_include_paths()->size(); i++) {
      const std::string path = ppcache->m_cmd_include_paths()->Get(i)->str();
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
    for (auto definePair : defineList) {
      std::string spath =
          m_pp->getSymbol(definePair.first) + "=" + definePair.second;
      define_vec.push_back(spath);
    }

    std::vector<std::string> cache_define_vec;
    for (unsigned int i = 0; i < ppcache->m_cmd_define_options()->size(); i++) {
      const std::string path = ppcache->m_cmd_define_options()->Get(i)->str();
      cache_define_vec.push_back(path);
    }
    if (!compareVectors(define_vec, cache_define_vec)) {
      delete[] buffer_pointer;
      return false;
    }

    /* All includes*/
    auto includes = ppcache->m_includes();
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
  std::string cacheFileName = getCacheFileName_();
  if (!checkCacheIsValid_(cacheFileName)) {
    return false;
  }
  return restore_(cacheFileName, errorsOnly);
}

bool PPCache::save() {
  bool cacheAllowed =
      m_pp->getCompileSourceFile()->getCommandLineParser()->cacheAllowed();
  if (!cacheAllowed) return false;
  std::string svFileName = m_pp->getFileName(LINE1);
  std::string origFileName = svFileName;
  std::string cacheFileName = getCacheFileName_();

  if (m_pp->isMacroBody()) return false;

  flatbuffers::FlatBufferBuilder builder(1024);
  /* Create header section */
  auto header = createHeader(builder, FlbSchemaVersion, origFileName);

  /* Cache the macro definitions */
  const MacroStorage& macros = m_pp->getMacros();
  std::vector<flatbuffers::Offset<MACROCACHE::Macro>> macro_vec;
  for (MacroStorage::const_iterator itr = macros.begin(); itr != macros.end();
       itr++) {
    std::string macroName = (*itr).first;
    MacroInfo* info = (*itr).second;

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
        builder, name, type, info->m_line, info->m_column, args, tokens));
  }
  auto macroList = builder.CreateVector(macro_vec);

  /* Cache Included files */
  std::vector<std::string> include_vec;
  std::set<PreprocessFile*> included;
  m_pp->collectIncludedFiles(included);
  for (std::set<PreprocessFile*>::iterator itr = included.begin();
       itr != included.end(); itr++) {
    std::string svFileName = m_pp->getSymbol((*itr)->getRawFileId());
    include_vec.push_back(svFileName);
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
    std::string pretendFileName =
        m_pp->getCompileSourceFile()->getSymbolTable()->getSymbol(
            info.m_pretendFileId);
    auto lineInfo = MACROCACHE::CreateLineTranslationInfo(
        builder, builder.CreateString(pretendFileName), info.m_originalLine,
        info.m_pretendLine);
    linetrans_vec.push_back(lineInfo);
  }
  auto lineinfoFBList = builder.CreateVector(linetrans_vec);

  /* Cache the include info */
  auto includeInfo = m_pp->getIncludeFileInfo();
  std::vector<flatbuffers::Offset<MACROCACHE::IncludeFileInfo>> lineinfo_vec;
  for (IncludeFileInfo& info : includeInfo) {
    std::string sectionFileName =
        m_pp->getCompileSourceFile()->getSymbolTable()->getSymbol(
            info.m_sectionFile);
    auto incInfo = MACROCACHE::CreateIncludeFileInfo(
        builder, info.m_sectionStartLine, builder.CreateString(sectionFileName),
        info.m_originalLine, info.m_type, info.m_indexOpening,
        info.m_indexClosing);
    // std::cout << "save sectionFile: " << sectionFileName << " s:" <<
    // info.m_sectionStartLine << " o:" << info.m_originalLine << " t:" <<
    // info.m_type << "\n";
    lineinfo_vec.push_back(incInfo);
  }
  auto incinfoFBList = builder.CreateVector(lineinfo_vec);

  /* Cache the design objects */
  FileContent* fcontent = m_pp->getFileContent();
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
