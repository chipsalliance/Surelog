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

#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/ParseFile.h"
#include "Utils/StringUtils.h"
#include "Utils/FileUtils.h"
#include "Cache/Cache.h"
#include "flatbuffers/util.h"
#include <cstdio>
#include <ctime>
#include <sys/types.h>
#include <sys/stat.h>

#include "antlr4-runtime.h"
using namespace antlr4;

#include "API/PythonAPI.h"
#include "Cache/PythonAPICache.h"
#include "SourceCompile/PythonListen.h"

using namespace SURELOG;

static std::string FlbSchemaVersion = "1.0";

PythonAPICache::PythonAPICache(PythonListen* listener) : m_listener(listener) {}

std::string PythonAPICache::getCacheFileName_(std::string svFileName) {
  SymbolId cacheDirId =
      m_listener->getCompileSourceFile()->getCommandLineParser()->getCacheDir();
  std::string cacheDirName = m_listener->getParseFile()->getSymbol(cacheDirId);
  if (svFileName.empty())
    svFileName = m_listener->getParseFile()->getFileName(LINE1);
  svFileName = FileUtils::basename(svFileName);
  Library* lib = m_listener->getCompileSourceFile()->getLibrary();
  std::string libName = lib->getName() + "/";
  std::string cacheFileName = cacheDirName + libName + svFileName + ".slpy";
  return cacheFileName;
}

bool PythonAPICache::restore_(std::string cacheFileName) {
  uint8_t* buffer_pointer = openFlatBuffers(cacheFileName);
  if (buffer_pointer == NULL) return false;

  const PYTHONAPICACHE::PythonAPICache* ppcache =
      PYTHONAPICACHE::GetPythonAPICache(buffer_pointer);
  SymbolTable canonicalSymbols;
  restoreErrors(ppcache->m_errors(), ppcache->m_symbols(), canonicalSymbols,
                m_listener->getCompileSourceFile()->getErrorContainer(),
                m_listener->getCompileSourceFile()->getSymbolTable());

  delete[] buffer_pointer;
  return true;
}

bool PythonAPICache::checkCacheIsValid_(std::string cacheFileName) {
  uint8_t* buffer_pointer = openFlatBuffers(cacheFileName);
  if (buffer_pointer == NULL) return false;
  if (!PYTHONAPICACHE::PythonAPICacheBufferHasIdentifier(buffer_pointer)) {
    delete[] buffer_pointer;
    return false;
  }
  const PYTHONAPICACHE::PythonAPICache* ppcache =
      PYTHONAPICACHE::GetPythonAPICache(buffer_pointer);
  auto header = ppcache->m_header();

  auto scriptFile = ppcache->m_python_script_file()->c_str();
  if (scriptFile) {
    time_t ct = get_mtime(cacheFileName.c_str());
    time_t ft = get_mtime(scriptFile);
    if (ft == -1) {
      delete[] buffer_pointer;
      return false;
    }
    if (ct == -1) {
      delete[] buffer_pointer;
      return false;
    }
    if (ct < ft) {
      delete[] buffer_pointer;
      return false;
    }
  }

  if (!checkIfCacheIsValid(header, FlbSchemaVersion, cacheFileName)) {
    delete[] buffer_pointer;
    return false;
  }

  delete[] buffer_pointer;
  return true;
}

bool PythonAPICache::isValid() {
  std::string cacheFileName = getCacheFileName_();
  return checkCacheIsValid_(cacheFileName);
}

bool PythonAPICache::restore() {
  bool cacheAllowed = m_listener->getCompileSourceFile()
                          ->getCommandLineParser()
                          ->cacheAllowed();
  if (!cacheAllowed) return false;

  std::string cacheFileName = getCacheFileName_();
  if (!checkCacheIsValid_(cacheFileName)) {
    return false;
  }

  return restore_(cacheFileName);
}

bool PythonAPICache::save() {
  bool cacheAllowed = m_listener->getCompileSourceFile()
                          ->getCommandLineParser()
                          ->cacheAllowed();
  if (!cacheAllowed) return false;
  std::string svFileName = m_listener->getParseFile()->getPpFileName();
  std::string origFileName = svFileName;

  std::string cacheFileName = getCacheFileName_();

  flatbuffers::FlatBufferBuilder builder(1024);
  /* Create header section */
  auto header = createHeader(builder, FlbSchemaVersion, origFileName);

  std::string pythonScriptFile = PythonAPI::getListenerScript();
  auto scriptFile = builder.CreateString(pythonScriptFile);

  /* Cache the errors and canonical symbols */
  ErrorContainer* errorContainer =
      m_listener->getCompileSourceFile()->getErrorContainer();
  SymbolId subjectFileId = m_listener->getParseFile()->getFileId(LINE1);
  SymbolTable canonicalSymbols;
  auto errorSymbolPair = cacheErrors(
      builder, canonicalSymbols, errorContainer,
      m_listener->getCompileSourceFile()->getSymbolTable(), subjectFileId);

  /* Create Flatbuffers */
  auto ppcache = PYTHONAPICACHE::CreatePythonAPICache(
      builder, header, scriptFile, errorSymbolPair.first,
      errorSymbolPair.second);
  FinishPythonAPICacheBuffer(builder, ppcache);

  /* Save Flatbuffer */
  bool status = saveFlatbuffers(builder, cacheFileName);

  return status;
}
