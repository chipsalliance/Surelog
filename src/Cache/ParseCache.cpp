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
#include "Cache/ParseCache.h"

#if defined(_MSC_VER)
#include <direct.h>
#include <process.h>
#else
#include <sys/param.h>
#include <unistd.h>
#endif

#include <sys/stat.h>
#include <sys/types.h>

#include <cstdint>
#include <cstdio>
#include <ctime>

#if (__cplusplus >= 201703L) && __has_include(<filesystem>)
#include <filesystem>
namespace fs = std::filesystem;
#else
#include <experimental/filesystem>
namespace fs = std::experimental::filesystem;
#endif

#include "Cache/Cache.h"
#include "Cache/parser_generated.h"
#include "CommandLine/CommandLineParser.h"
#include "Design/FileContent.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Package/Precompiled.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/SymbolTable.h"
#include "Utils/FileUtils.h"
#include "Utils/StringUtils.h"
#include "flatbuffers/util.h"

namespace SURELOG {
ParseCache::ParseCache(ParseFile* parser)
    : m_parse(parser), m_isPrecompiled(false) {}

static constexpr char FlbSchemaVersion[] = "1.0";

std::string ParseCache::getCacheFileName_(std::string svFileName) {
  Precompiled* prec = Precompiled::getSingleton();
  SymbolId cacheDirId =
      m_parse->getCompileSourceFile()->getCommandLineParser()->getCacheDir();
  if (svFileName.empty()) svFileName = m_parse->getPpFileName();
  std::string baseFileName = FileUtils::basename(svFileName);
  if (prec->isFilePrecompiled(baseFileName)) {
    std::string_view packageRepDir =
        m_parse->getSymbol(m_parse->getCompileSourceFile()
                               ->getCommandLineParser()
                               ->getPrecompiledDir());
    cacheDirId = m_parse->getCompileSourceFile()
                     ->getCommandLineParser()
                     ->mutableSymbolTable()
                     ->registerSymbol(packageRepDir);
    m_isPrecompiled = true;
    svFileName = baseFileName;
  } else {
    fs::path fs_path(svFileName);
    std::string s1 = fs_path.parent_path().string();
    fs::path p1(s1);
    std::string s2 = p1.parent_path().string();
    s1.erase(0, s2.length() + 1);
    svFileName = s1 + "/" + baseFileName;
  }

  std::string_view cacheDirName = m_parse->getSymbol(cacheDirId);
  Library* lib = m_parse->getLibrary();
  std::string libName = lib->getName() + "/";
  std::string cacheFileName(cacheDirName);
  cacheFileName.append(libName).append(svFileName).append(".slpa");
  FileUtils::mkDir(std::string(cacheDirName).append(libName));
  return cacheFileName;
}

bool ParseCache::restore_(std::string cacheFileName) {
  uint8_t* buffer_pointer = openFlatBuffers(cacheFileName);
  if (buffer_pointer == NULL) return false;

  /* Restore Errors */
  const PARSECACHE::ParseCache* ppcache =
      PARSECACHE::GetParseCache(buffer_pointer);
  SymbolTable canonicalSymbols;
  restoreErrors(ppcache->m_errors(), ppcache->m_symbols(), canonicalSymbols,
                m_parse->getCompileSourceFile()->getErrorContainer(),
                m_parse->getCompileSourceFile()->getSymbolTable());
  /* Restore design content (Verilog Design Elements) */
  FileContent* fileContent = m_parse->getFileContent();
  if (fileContent == NULL) {
    fileContent = new FileContent(
        m_parse->getFileId(0), m_parse->getLibrary(),
        m_parse->getCompileSourceFile()->getSymbolTable(),
        m_parse->getCompileSourceFile()->getErrorContainer(), NULL, 0);
    m_parse->setFileContent(fileContent);
    m_parse->getCompileSourceFile()->getCompiler()->getDesign()->addFileContent(
        m_parse->getFileId(0), fileContent);
  }
  auto content = ppcache->m_elements();
  for (unsigned int i = 0; i < content->size(); i++) {
    auto elemc = content->Get(i);
    DesignElement elem(
        m_parse->getCompileSourceFile()->getSymbolTable()->registerSymbol(
            canonicalSymbols.getSymbol(elemc->m_name())),
        m_parse->getCompileSourceFile()->getSymbolTable()->registerSymbol(
            canonicalSymbols.getSymbol(elemc->m_fileId())),
        (DesignElement::ElemType)elemc->m_type(), elemc->m_uniqueId(),
        elemc->m_line(), elemc->m_column(), elemc->m_end_line(),
        elemc->m_end_column(), elemc->m_parent());
    elem.m_node = elemc->m_node();
    elem.m_timeInfo.m_type = (TimeInfo::Type)elemc->m_timeInfo()->m_type();
    elem.m_timeInfo.m_fileId = elemc->m_timeInfo()->m_fileId();
    elem.m_timeInfo.m_line = elemc->m_timeInfo()->m_line();
    elem.m_timeInfo.m_timeUnit =
        (TimeInfo::Unit)elemc->m_timeInfo()->m_timeUnit();
    elem.m_timeInfo.m_timeUnitValue = elemc->m_timeInfo()->m_timeUnitValue();
    elem.m_timeInfo.m_timePrecision =
        (TimeInfo::Unit)elemc->m_timeInfo()->m_timePrecision();
    elem.m_timeInfo.m_timePrecisionValue =
        elemc->m_timeInfo()->m_timePrecisionValue();
    fileContent->getDesignElements().push_back(elem);
  }

  /* Restore design objects */
  auto objects = ppcache->m_objects();
  restoreVObjects(objects, canonicalSymbols,
                  *m_parse->getCompileSourceFile()->getSymbolTable(),
                  m_parse->getFileId(0), fileContent);

  delete[] buffer_pointer;
  return true;
}

bool ParseCache::checkCacheIsValid_(std::string cacheFileName) {
  uint8_t* buffer_pointer = openFlatBuffers(cacheFileName);
  if (buffer_pointer == NULL) {
    return false;
  }
  if (!PARSECACHE::ParseCacheBufferHasIdentifier(buffer_pointer)) {
    delete[] buffer_pointer;
    return false;
  }
  const PARSECACHE::ParseCache* ppcache =
      PARSECACHE::GetParseCache(buffer_pointer);
  auto header = ppcache->m_header();

  if (!m_isPrecompiled) {
    if (!checkIfCacheIsValid(header, FlbSchemaVersion, cacheFileName)) {
      delete[] buffer_pointer;
      return false;
    }
  }

  delete[] buffer_pointer;
  return true;
}

bool ParseCache::isValid() {
  std::string cacheFileName = getCacheFileName_();
  return checkCacheIsValid_(cacheFileName);
}

bool ParseCache::restore() {
  CommandLineParser* clp =
      m_parse->getCompileSourceFile()->getCommandLineParser();
  bool cacheAllowed = clp->cacheAllowed();
  if (!cacheAllowed) return false;

  std::string cacheFileName = getCacheFileName_();
  if (!checkCacheIsValid_(cacheFileName)) {
    // char path [10000];
    // char* p = getcwd(path, 9999);
    // if (!clp->parseOnly())
    //   std::cout << "Cache miss for: " << cacheFileName << " pwd: " << p <<
    //   "\n";
    return false;
  }

  return restore_(cacheFileName);
}

bool ParseCache::save() {
  CommandLineParser* clp =
      m_parse->getCompileSourceFile()->getCommandLineParser();
  bool cacheAllowed = clp->cacheAllowed();
  bool parseOnly = clp->parseOnly();

  if (!cacheAllowed) return true;
  std::string_view svFileName = m_parse->getPpFileName();
  std::string origFileName(svFileName);
  if (parseOnly) {
    SymbolId cacheDirId = clp->getCacheDir();
    std::string_view cacheDirName = m_parse->getSymbol(cacheDirId);
    origFileName = std::string(cacheDirName).append("../").append(origFileName);
  }
  std::string cacheFileName = getCacheFileName_();

  flatbuffers::FlatBufferBuilder builder(1024);
  /* Create header section */
  auto header = createHeader(builder, FlbSchemaVersion, origFileName);

  /* Cache the errors and canonical symbols */
  ErrorContainer* errorContainer =
      m_parse->getCompileSourceFile()->getErrorContainer();
  std::string_view subjectFile = m_parse->getFileName(LINE1);
  SymbolId subjectFileId =
      m_parse->getCompileSourceFile()->getSymbolTable()->registerSymbol(
          subjectFile);
  SymbolTable canonicalSymbols;
  auto errorSymbolPair = cacheErrors(
      builder, canonicalSymbols, errorContainer,
      m_parse->getCompileSourceFile()->getSymbolTable(), subjectFileId);

  /* Cache the design content */
  FileContent* fcontent = m_parse->getFileContent();
  std::vector<flatbuffers::Offset<PARSECACHE::DesignElement>> element_vec;
  if (fcontent)
    for (unsigned int i = 0; i < fcontent->getDesignElements().size(); i++) {
      DesignElement& elem = fcontent->getDesignElements()[i];
      TimeInfo& info = elem.m_timeInfo;
      auto timeInfo = CACHE::CreateTimeInfo(
          builder, static_cast<uint16_t>(info.m_type),
          canonicalSymbols.getId(
              m_parse->getCompileSourceFile()->getSymbolTable()->getSymbol(
                  info.m_fileId)),
          info.m_line, static_cast<uint16_t>(info.m_timeUnit),
          info.m_timeUnitValue, static_cast<uint16_t>(info.m_timePrecision),
          info.m_timePrecisionValue);
      element_vec.push_back(PARSECACHE::CreateDesignElement(
          builder,
          canonicalSymbols.getId(
              m_parse->getCompileSourceFile()->getSymbolTable()->getSymbol(
                  elem.m_name)),
          canonicalSymbols.getId(
              m_parse->getCompileSourceFile()->getSymbolTable()->getSymbol(
                  elem.m_fileId)),
          elem.m_type, elem.m_uniqueId, elem.m_line, elem.m_column,
          elem.m_endLine, elem.m_endColumn, timeInfo, elem.m_parent,
          elem.m_node));
    }
  auto elementList = builder.CreateVector(element_vec);

  /* Cache the design objects */
  std::vector<CACHE::VObject> object_vec =
      cacheVObjects(fcontent, canonicalSymbols,
                    *m_parse->getCompileSourceFile()->getSymbolTable(),
                    m_parse->getFileId(0));
  auto objectList = builder.CreateVectorOfStructs(object_vec);

  /* Create Flatbuffers */
  auto ppcache = PARSECACHE::CreateParseCache(
      builder, header, errorSymbolPair.first, errorSymbolPair.second,
      elementList, objectList);
  FinishParseCacheBuffer(builder, ppcache);

  /* Save Flatbuffer */
  bool status = saveFlatbuffers(builder, cacheFileName);

  return status;
}
}  // namespace SURELOG
