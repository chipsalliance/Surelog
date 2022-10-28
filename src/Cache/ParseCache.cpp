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

#include <Surelog/Cache/ParseCache.h>
#include <Surelog/Cache/parser_generated.h>
#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/FileSystem.h>
#include <Surelog/Design/Design.h>
#include <Surelog/Design/DesignElement.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/Library/Library.h>
#include <Surelog/Package/Precompiled.h>
#include <Surelog/SourceCompile/CompileSourceFile.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/ParseFile.h>
#include <Surelog/SourceCompile/SymbolTable.h>

namespace SURELOG {
namespace fs = std::filesystem;

ParseCache::ParseCache(ParseFile* parser)
    : m_parse(parser), m_isPrecompiled(false) {}

static constexpr char FlbSchemaVersion[] = "1.3";

PathId ParseCache::getCacheFileId_(PathId ppFileId) {
  if (!ppFileId) ppFileId = m_parse->getPpFileId();
  if (!ppFileId) return BadPathId;

  FileSystem* const fileSystem = FileSystem::getInstance();
  CommandLineParser* clp =
      m_parse->getCompileSourceFile()->getCommandLineParser();
  SymbolTable* const symbolTable =
      m_parse->getCompileSourceFile()->getSymbolTable();
  Precompiled* prec = Precompiled::getSingleton();

  m_isPrecompiled = prec->isFilePrecompiled(ppFileId, symbolTable);
  const std::string& libName = m_parse->getLibrary()->getName();
  return fileSystem->getParseCacheFile(clp->fileunit(), ppFileId, libName,
                                       m_isPrecompiled, symbolTable);
}

bool ParseCache::restore_(PathId cacheFileId,
                          const std::vector<char>& content) {
  if (!cacheFileId || content.empty()) return false;

  FileSystem* const fileSystem = FileSystem::getInstance();
  /* Restore Errors */
  const PARSECACHE::ParseCache* ppcache =
      PARSECACHE::GetParseCache(content.data());

  SymbolTable cacheSymbols;
  restoreSymbols(ppcache->symbols(), &cacheSymbols);

  restoreErrors(ppcache->errors(), &cacheSymbols,
                m_parse->getCompileSourceFile()->getErrorContainer(),
                m_parse->getCompileSourceFile()->getSymbolTable());

  /* Restore design content (Verilog Design Elements) */
  FileContent* fileContent = m_parse->getFileContent();
  if (fileContent == nullptr) {
    fileContent =
        new FileContent(m_parse->getFileId(0), m_parse->getLibrary(),
                        m_parse->getCompileSourceFile()->getSymbolTable(),
                        m_parse->getCompileSourceFile()->getErrorContainer(),
                        nullptr, BadPathId);
    m_parse->setFileContent(fileContent);
    m_parse->getCompileSourceFile()->getCompiler()->getDesign()->addFileContent(
        m_parse->getFileId(0), fileContent);
  }
  for (const auto* elemc : *ppcache->elements()) {
    const std::string& elemName =
        cacheSymbols.getSymbol(SymbolId(elemc->name(), "<unknown>"));
    DesignElement* elem = new DesignElement(
        m_parse->getCompileSourceFile()->getSymbolTable()->registerSymbol(
            elemName),
        fileSystem->copy(PathId(&cacheSymbols, elemc->file_id(), BadRawPath),
                         m_parse->getCompileSourceFile()->getSymbolTable()),
        (DesignElement::ElemType)elemc->type(), NodeId(elemc->unique_id()),
        elemc->line(), elemc->column(), elemc->end_line(), elemc->end_column(),
        NodeId(elemc->parent()));
    elem->m_node = NodeId(elemc->node());
    elem->m_defaultNetType = (VObjectType)elemc->default_net_type();
    elem->m_timeInfo.m_type = (TimeInfo::Type)elemc->time_info()->type();
    elem->m_timeInfo.m_fileId = fileSystem->copy(
        PathId(&cacheSymbols, elemc->time_info()->file_id(), BadRawPath),
        m_parse->getCompileSourceFile()->getSymbolTable());
    elem->m_timeInfo.m_line = elemc->time_info()->line();
    elem->m_timeInfo.m_timeUnit =
        (TimeInfo::Unit)elemc->time_info()->time_unit();
    elem->m_timeInfo.m_timeUnitValue = elemc->time_info()->time_unit_value();
    elem->m_timeInfo.m_timePrecision =
        (TimeInfo::Unit)elemc->time_info()->time_precision();
    elem->m_timeInfo.m_timePrecisionValue =
        elemc->time_info()->time_precision_value();
    const std::string& fullName =
        fileContent->getLibrary()->getName() + "@" + elemName;
    fileContent->addDesignElement(fullName, elem);
  }

  /* Restore design objects */
  auto objects = ppcache->objects();
  restoreVObjects(objects, cacheSymbols,
                  m_parse->getCompileSourceFile()->getSymbolTable(),
                  m_parse->getFileId(0), fileContent);

  return true;
}

bool ParseCache::checkCacheIsValid_(PathId cacheFileId,
                                    const std::vector<char>& content) const {
  if (!cacheFileId || content.empty()) return false;

  if (!PARSECACHE::ParseCacheBufferHasIdentifier(content.data())) {
    return false;
  }

  CommandLineParser* clp =
      m_parse->getCompileSourceFile()->getCommandLineParser();
  if (clp->noCacheHash()) {
    return true;
  }

  const PARSECACHE::ParseCache* ppcache =
      PARSECACHE::GetParseCache(content.data());
  auto header = ppcache->header();

  if (m_isPrecompiled) {
    // For precompiled, check only the signature & version (so using
    // BadPathId instead of the actual arguments)
    return checkIfCacheIsValid(header, FlbSchemaVersion, BadPathId, BadPathId);
  } else {
    return checkIfCacheIsValid(header, FlbSchemaVersion, cacheFileId,
                               m_parse->getPpFileId());
  }
}

bool ParseCache::isValid() {
  PathId cacheFileId = getCacheFileId_(BadPathId);

  std::vector<char> content;
  return cacheFileId && openFlatBuffers(cacheFileId, content) &&
         checkCacheIsValid_(cacheFileId, content);
}

bool ParseCache::restore() {
  CommandLineParser* clp =
      m_parse->getCompileSourceFile()->getCommandLineParser();
  if (!clp->cacheAllowed()) return false;

  PathId cacheFileId = getCacheFileId_(BadPathId);

  std::vector<char> content;
  return cacheFileId && openFlatBuffers(cacheFileId, content) &&
         checkCacheIsValid_(cacheFileId, content) &&
         restore_(cacheFileId, content);
}

bool ParseCache::save() {
  CommandLineParser* clp =
      m_parse->getCompileSourceFile()->getCommandLineParser();
  if (!clp->cacheAllowed()) return true;

  FileContent* fcontent = m_parse->getFileContent();
  if (fcontent && (fcontent->getVObjects().size() > Cache::Capacity)) {
    clp->setCacheAllowed(false);
    Location loc(BadSymbolId);
    Error err(ErrorDefinition::CMD_CACHE_CAPACITY_EXCEEDED, loc);
    m_parse->getCompileSourceFile()->getErrorContainer()->addError(err);
    return false;
  }

  PathId cacheFileId = getCacheFileId_(BadPathId);
  if (!cacheFileId) {
    // Any fake(virtual) file like builtin.sv
    return true;
  }

  FileSystem* const fileSystem = FileSystem::getInstance();

  flatbuffers::FlatBufferBuilder builder(1024);
  /* Create header section */
  auto header = createHeader(builder, FlbSchemaVersion);

  /* Cache the errors and canonical symbols */
  ErrorContainer* errorContainer =
      m_parse->getCompileSourceFile()->getErrorContainer();
  SymbolTable cacheSymbols;
  auto errorCache =
      cacheErrors(builder, &cacheSymbols, errorContainer,
                  *m_parse->getCompileSourceFile()->getSymbolTable(),
                  m_parse->getFileId(LINE1));

  /* Cache the design content */
  std::vector<flatbuffers::Offset<PARSECACHE::DesignElement>> element_vec;
  if (fcontent)
    for (const DesignElement* elem : fcontent->getDesignElements()) {
      const TimeInfo& info = elem->m_timeInfo;
      auto timeInfo = CACHE::CreateTimeInfo(
          builder, static_cast<uint16_t>(info.m_type),
          (RawPathId)fileSystem->copy(info.m_fileId, &cacheSymbols),
          info.m_line, static_cast<uint16_t>(info.m_timeUnit),
          info.m_timeUnitValue, static_cast<uint16_t>(info.m_timePrecision),
          info.m_timePrecisionValue);
      element_vec.emplace_back(PARSECACHE::CreateDesignElement(
          builder,
          (RawSymbolId)cacheSymbols.copyFrom(
              elem->m_name, m_parse->getCompileSourceFile()->getSymbolTable()),
          (RawPathId)fileSystem->copy(elem->m_fileId, &cacheSymbols),
          elem->m_type, (RawNodeId)elem->m_uniqueId, elem->m_line,
          elem->m_column, elem->m_endLine, elem->m_endColumn, timeInfo,
          (RawNodeId)elem->m_parent, (RawNodeId)elem->m_node,
          elem->m_defaultNetType));
    }
  auto elementList = builder.CreateVector(element_vec);

  /* Cache the design objects */
  std::vector<CACHE::VObject> object_vec =
      cacheVObjects(fcontent, &cacheSymbols,
                    *m_parse->getCompileSourceFile()->getSymbolTable(),
                    m_parse->getFileId(0));
  auto objectList = builder.CreateVectorOfStructs(object_vec);

  auto symbolVec = builder.CreateVectorOfStrings(cacheSymbols.getSymbols());
  /* Create Flatbuffers */
  auto ppcache = PARSECACHE::CreateParseCache(
      builder, header, errorCache, symbolVec, elementList, objectList);
  FinishParseCacheBuffer(builder, ppcache);

  /* Save Flatbuffer */
  return saveFlatbuffers(builder, cacheFileId,
                         m_parse->getCompileSourceFile()->getSymbolTable());
}
}  // namespace SURELOG
