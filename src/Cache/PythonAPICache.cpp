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
namespace fs = std::filesystem;

static std::string FlbSchemaVersion = "1.0";

PythonAPICache::PythonAPICache(PythonListen* listener) : m_listener(listener) {}

PathId PythonAPICache::getCacheFileId_(PathId svFileNameId) const {
  ParseFile* parseFile = m_listener->getParseFile();
  if (!svFileNameId) svFileNameId = parseFile->getFileId(LINE1);
  if (!svFileNameId) return BadPathId;
  FileSystem* const fileSystem = FileSystem::getInstance();
  PathId cacheDirId = m_listener->getCompileSourceFile()
                          ->getCommandLineParser()
                          ->getCacheDirId();

  fs::path cacheDirName = fileSystem->toPath(cacheDirId);
  std::filesystem::path svFileName = std::get<1>(
      fileSystem->getLeaf(svFileNameId, parseFile->getSymbolTable()));
  Library* lib = m_listener->getCompileSourceFile()->getLibrary();
  const std::string& libName = lib->getName();
  fs::path cacheFileName =
      cacheDirName / libName / (svFileName.string() + ".slpy");
  return fileSystem->toPathId(
      cacheFileName, m_listener->getCompileSourceFile()->getSymbolTable());
}

bool PythonAPICache::restore_(PathId cacheFileId) {
  auto buffer = openFlatBuffers(cacheFileId);
  if (buffer == nullptr) return false;

  const PYTHONAPICACHE::PythonAPICache* ppcache =
      PYTHONAPICACHE::GetPythonAPICache(buffer.get());
  SymbolTable canonicalSymbols;
  restoreSymbols(ppcache->m_symbols(), &canonicalSymbols);
  restoreErrors(ppcache->m_errors(), &canonicalSymbols,
                m_listener->getCompileSourceFile()->getErrorContainer(),
                m_listener->getCompileSourceFile()->getSymbolTable());

  return true;
}

bool PythonAPICache::checkCacheIsValid_(PathId cacheFileId) {
  auto buffer = openFlatBuffers(cacheFileId);
  if (buffer == nullptr) return false;
  if (!PYTHONAPICACHE::PythonAPICacheBufferHasIdentifier(buffer.get())) {
    return false;
  }
  FileSystem* const fileSystem = FileSystem::getInstance();
  const PYTHONAPICACHE::PythonAPICache* ppcache =
      PYTHONAPICACHE::GetPythonAPICache(buffer.get());
  auto header = ppcache->m_header();

  fs::path cacheFileName = fileSystem->toPath(cacheFileId);
  auto scriptFile = ppcache->m_python_script_file()->string_view();
  if (!scriptFile.empty()) {
    time_t ct = get_mtime(cacheFileName);
    time_t ft = get_mtime(scriptFile);
    if (ft == -1) {
      return false;
    }
    if (ct == -1) {
      return false;
    }
    if (ct < ft) {
      return false;
    }
  }

  if (!checkIfCacheIsValid(header, FlbSchemaVersion, cacheFileId)) {
    return false;
  }

  return true;
}

bool PythonAPICache::isValid() {
  return checkCacheIsValid_(getCacheFileId_(BadPathId));
}

bool PythonAPICache::restore() {
  bool cacheAllowed = m_listener->getCompileSourceFile()
                          ->getCommandLineParser()
                          ->cacheAllowed();
  if (!cacheAllowed) return false;

  PathId cacheFileId = getCacheFileId_(BadPathId);
  if (!checkCacheIsValid_(cacheFileId)) {
    return false;
  }

  return restore_(cacheFileId);
}

bool PythonAPICache::save() {
  FileSystem* const fileSystem = FileSystem::getInstance();
  bool cacheAllowed = m_listener->getCompileSourceFile()
                          ->getCommandLineParser()
                          ->cacheAllowed();
  if (!cacheAllowed) return false;
  ParseFile* parseFile = m_listener->getParseFile();
  SymbolTable* symbolTable = parseFile->getSymbolTable();
  fs::path svFileName = fileSystem->toPath(parseFile->getPpFileId());
  fs::path origFileName = svFileName;
  PathId cacheFileId = getCacheFileId_(BadPathId);

  flatbuffers::FlatBufferBuilder builder(1024);
  /* Create header section */
  auto header =
      createHeader(builder, FlbSchemaVersion, parseFile->getPpFileId());

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
  bool status = saveFlatbuffers(builder, cacheFileId);

  return status;
}
}  // namespace SURELOG
