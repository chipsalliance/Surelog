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

#include <Surelog/API/PythonAPI.h>
#include <Surelog/Cache/Cache.h>
#include <Surelog/Cache/PythonAPICache.h>
#include <Surelog/Cache/python_api_generated.h>
#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/FileSystem.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/Library/Library.h>
#include <Surelog/SourceCompile/CompilationUnit.h>
#include <Surelog/SourceCompile/CompileSourceFile.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/ParseFile.h>
#include <Surelog/SourceCompile/PreprocessFile.h>
#include <Surelog/SourceCompile/PythonListen.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/StringUtils.h>
#include <antlr4-runtime.h>
#include <flatbuffers/util.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <cstdio>
#include <ctime>
#include <filesystem>

namespace SURELOG {
static std::string FlbSchemaVersion = "1.0";

PythonAPICache::PythonAPICache(PythonListen* listener) : m_listener(listener) {}

PathId PythonAPICache::getCacheFileId_(PathId sourceFileId) const {
  ParseFile* parseFile = m_listener->getParseFile();
  if (!sourceFileId) sourceFileId = parseFile->getFileId(LINE1);
  if (!sourceFileId) return BadPathId;

  FileSystem* const fileSystem = FileSystem::getInstance();
  CommandLineParser* clp =
      m_listener->getCompileSourceFile()->getCommandLineParser();
  SymbolTable* symbolTable =
      m_listener->getCompileSourceFile()->getSymbolTable();

  const std::string& libName =
      m_listener->getCompileSourceFile()->getLibrary()->getName();
  return fileSystem->getPythonCacheFile(clp->fileunit(), sourceFileId, libName,
                                        symbolTable);
}

bool PythonAPICache::restore_(PathId cacheFileId,
                              const std::vector<char>& content) {
  if (!cacheFileId || content.empty()) return false;

  const PYTHONAPICACHE::PythonAPICache* ppcache =
      PYTHONAPICACHE::GetPythonAPICache(content.data());
  SymbolTable canonicalSymbols;
  restoreSymbols(ppcache->m_symbols(), &canonicalSymbols);
  restoreErrors(ppcache->m_errors(), &canonicalSymbols,
                m_listener->getCompileSourceFile()->getErrorContainer(),
                m_listener->getCompileSourceFile()->getSymbolTable());

  return true;
}

bool PythonAPICache::checkCacheIsValid_(
    PathId cacheFileId, const std::vector<char>& content) const {
  if (!cacheFileId || content.empty()) return false;

  if (!PYTHONAPICACHE::PythonAPICacheBufferHasIdentifier(content.data())) {
    return false;
  }
  FileSystem* const fileSystem = FileSystem::getInstance();
  SymbolTable* symbolTable =
      m_listener->getCompileSourceFile()->getSymbolTable();

  const PYTHONAPICACHE::PythonAPICache* ppcache =
      PYTHONAPICACHE::GetPythonAPICache(content.data());
  auto header = ppcache->m_header();

  const PathId scriptFileId = fileSystem->toPathId(
      ppcache->m_python_script_file()->string_view(), symbolTable);

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

  if (!checkIfCacheIsValid(header, FlbSchemaVersion, cacheFileId,
                           m_listener->getParseFile()->getFileId(LINE1),
                           symbolTable)) {
    return false;
  }

  return true;
}

bool PythonAPICache::checkCacheIsValid_(PathId cacheFileId) const {
  std::vector<char> content;
  return cacheFileId && openFlatBuffers(cacheFileId, content) &&
         checkCacheIsValid_(cacheFileId, content);
}

bool PythonAPICache::isValid() const {
  return checkCacheIsValid_(getCacheFileId_(BadPathId));
}

bool PythonAPICache::restore() {
  bool cacheAllowed = m_listener->getCompileSourceFile()
                          ->getCommandLineParser()
                          ->cacheAllowed();
  if (!cacheAllowed) return false;

  PathId cacheFileId = getCacheFileId_(BadPathId);
  std::vector<char> content;

  return cacheFileId && openFlatBuffers(cacheFileId, content) &&
         checkCacheIsValid_(cacheFileId, content) &&
         restore_(cacheFileId, content);
}

bool PythonAPICache::save() {
  CommandLineParser* clp =
      m_listener->getCompileSourceFile()->getCommandLineParser();
  if (!clp->cacheAllowed()) return false;

  PathId cacheFileId = getCacheFileId_(BadPathId);
  if (!cacheFileId) return false;

  FileSystem* const fileSystem = FileSystem::getInstance();
  ParseFile* parseFile = m_listener->getParseFile();

  flatbuffers::FlatBufferBuilder builder(1024);
  /* Create header section */
  auto header = createHeader(builder, FlbSchemaVersion);

  std::string pythonScriptFile = PythonAPI::getListenerScript();
  auto scriptFile = builder.CreateString(pythonScriptFile);

  /* Cache the errors and canonical symbols */
  ErrorContainer* errorContainer =
      m_listener->getCompileSourceFile()->getErrorContainer();
  PathId subjectFileId = m_listener->getParseFile()->getFileId(LINE1);
  SymbolTable canonicalSymbols;
  auto errorCache = cacheErrors(
      builder, &canonicalSymbols, errorContainer,
      *m_listener->getCompileSourceFile()->getSymbolTable(), subjectFileId);

  auto symbolVec = builder.CreateVectorOfStrings(canonicalSymbols.getSymbols());

  /* Create Flatbuffers */
  auto ppcache = PYTHONAPICACHE::CreatePythonAPICache(
      builder, header, scriptFile, errorCache, symbolVec);
  FinishPythonAPICacheBuffer(builder, ppcache);

  /* Save Flatbuffer */
  return saveFlatbuffers(builder, cacheFileId,
                         m_listener->getCompileSourceFile()->getSymbolTable());
}
}  // namespace SURELOG
