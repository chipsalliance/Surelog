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
#include "CommandLine/CommandLineParser.hpp"
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
#include "Cache/ParseCache.h"
#include "Design/FileContent.h"
#include "Package/Precompiled.h"
using namespace SURELOG;

ParseCache::ParseCache(ParseFile* parser)
    : m_parse(parser), m_isPrecompiled(false) {}

ParseCache::ParseCache(const ParseCache& orig) {}

ParseCache::~ParseCache() {}

static std::string FlbSchemaVersion = "1.0";

std::string ParseCache::getCacheFileName_(std::string svFileName) {
  Precompiled* prec = Precompiled::getSingleton();
  SymbolId cacheDirId =
      m_parse->getCompileSourceFile()->getCommandLineParser()->getCacheDir();
  if (svFileName == "") svFileName = m_parse->getPpFileName();
  std::string root = svFileName;
  root = StringUtils::getRootFileName(root);
  if (prec->isFilePrecompiled(root)) {
    std::string packageRepDir =
        m_parse->getSymbol(m_parse->getCompileSourceFile()
                               ->getCommandLineParser()
                               ->getPrecompiledDir());
    cacheDirId = m_parse->getCompileSourceFile()
                     ->getCommandLineParser()
                     ->getSymbolTable()
                     ->registerSymbol(packageRepDir);
    m_isPrecompiled = true;
  }

  std::string cacheDirName = m_parse->getSymbol(cacheDirId);
  Library* lib = m_parse->getLibrary();
  std::string libName = lib->getName() + "/";
  svFileName = StringUtils::getRootFileName(svFileName);
  std::string cacheFileName = cacheDirName + libName + svFileName + ".slpa";
  FileUtils::mkDir(std::string(cacheDirName + libName).c_str());
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
  for (unsigned int i = 0; i < content->Length(); i++) {
    auto elemc = content->Get(i);
    DesignElement elem(
        m_parse->getCompileSourceFile()->getSymbolTable()->registerSymbol(
            canonicalSymbols.getSymbol(elemc->m_name())),
        m_parse->getCompileSourceFile()->getSymbolTable()->registerSymbol(
            canonicalSymbols.getSymbol(elemc->m_fileId())),
        (DesignElement::ElemType)elemc->m_type(), elemc->m_uniqueId(),
        elemc->m_line(), elemc->m_parent());
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
  for (unsigned int i = 0; i < objects->Length(); i++) {
    auto objectc = objects->Get(i);

    // VObject object
    // (m_parse->getCompileSourceFile()->getSymbolTable()->registerSymbol(canonicalSymbols.getSymbol(objectc->m_name())),
    //                (VObjectType) objectc->m_type(), objectc->m_uniqueId(),
    //                objectc->m_line(), objectc->m_parent(),
    //                objectc->m_definition(),
    //               objectc->m_child(),  objectc->m_sibling());

    unsigned long field1 = objectc->m_field1();
    unsigned long field2 = objectc->m_field2();
    unsigned long field3 = objectc->m_field3();
    // Decode compression done when saving cache (see below)
    SymbolId name = (field1 & 0x00000000000FFFFF);
    unsigned short type = (field1 & 0x00000000FFF00000) >> (20);
    // UNUSED: unsigned int   line  = (field1 & 0x0000FFFF00000000) >> (20 +
    // 12);
    NodeId parent = (field1 & 0xFFFF000000000000) >> (20 + 12 + 16);
    parent |= (field2 & 0x000000000000000F) << (16);
    NodeId definition = (field2 & 0x0000000000FFFFF0) >> (4);
    NodeId child = (field2 & 0x00000FFFFF000000) >> (4 + 20);
    NodeId sibling = (field2 & 0xFFFFF00000000000) >> (4 + 20 + 20);
    SymbolId fileId = (field3 & 0x00000000FFFFFFFF);
    unsigned int line = (field3 & 0xFFFFFFFF00000000) >> (32);
    VObject object(
        m_parse->getCompileSourceFile()->getSymbolTable()->registerSymbol(
            canonicalSymbols.getSymbol(name)),
        m_parse->getCompileSourceFile()->getSymbolTable()->registerSymbol(
            canonicalSymbols.getSymbol(fileId)),
        (VObjectType)type, line, parent, definition, child, sibling);

    fileContent->getVObjects().push_back(object);
  }
  // std::cout << "RESTORE: " << cacheFileName << " "
  //          << m_parse->getCompileSourceFile()->getSymbolTable()->getSymbol
  //          (m_parse->getFileId(0))
  //          << " NB: " <<  objects->Length()
  //          << std::endl;

  delete[] buffer_pointer;
  return true;
}

bool ParseCache::checkCacheIsValid_(std::string cacheFileName) {
  uint8_t* buffer_pointer = openFlatBuffers(cacheFileName);
  if (buffer_pointer == NULL) return false;
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
  bool cacheAllowed =
      m_parse->getCompileSourceFile()->getCommandLineParser()->cacheAllowed();
  if (!cacheAllowed) return false;

  std::string cacheFileName = getCacheFileName_();
  if (!checkCacheIsValid_(cacheFileName)) {
    return false;
  }

  return restore_(cacheFileName);
}

bool ParseCache::save() {
  bool cacheAllowed =
      m_parse->getCompileSourceFile()->getCommandLineParser()->cacheAllowed();
  if (!cacheAllowed) return true;
  std::string svFileName = m_parse->getPpFileName();
  std::string origFileName = svFileName;

  std::string cacheFileName = getCacheFileName_();

  flatbuffers::FlatBufferBuilder builder(1024);
  /* Create header section */
  auto header = createHeader(builder, FlbSchemaVersion, origFileName);

  /* Cache the errors and canonical symbols */
  ErrorContainer* errorContainer =
      m_parse->getCompileSourceFile()->getErrorContainer();
  std::string subjectFile = m_parse->getFileName(LINE1);
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
  for (unsigned int i = 0; i < fcontent->getDesignElements().size(); i++) {
    DesignElement& elem = fcontent->getDesignElements()[i];
    TimeInfo& info = elem.m_timeInfo;
    auto timeInfo = CACHE::CreateTimeInfo(
        builder, info.m_type,
        canonicalSymbols.getId(
            m_parse->getCompileSourceFile()->getSymbolTable()->getSymbol(
                info.m_fileId)),
        info.m_line, info.m_timeUnit, info.m_timeUnitValue,
        info.m_timePrecision, info.m_timePrecisionValue);
    element_vec.push_back(PARSECACHE::CreateDesignElement(
        builder,
        canonicalSymbols.getId(
            m_parse->getCompileSourceFile()->getSymbolTable()->getSymbol(
                elem.m_name)),
        canonicalSymbols.getId(
            m_parse->getCompileSourceFile()->getSymbolTable()->getSymbol(
                elem.m_fileId)),
        elem.m_type, elem.m_uniqueId, elem.m_line, timeInfo, elem.m_parent,
        elem.m_node));
  }
  auto elementList = builder.CreateVector(element_vec);

  /* Cache the design objects */
  // std::vector<flatbuffers::Offset<PARSECACHE::VObject>> object_vec;
  std::vector<PARSECACHE::VObject> object_vec;
  for (unsigned int i = 0; i < fcontent->getVObjects().size(); i++) {
    VObject& object = fcontent->getVObjects()[i];

    // Lets compress this struct into 20 and 16 bits fields:
    //  object_vec.push_back(PARSECACHE::CreateVObject(builder,
    //                                              canonicalSymbols.getId(m_parse->getCompileSourceFile()->getSymbolTable()->getSymbol(object.m_name)),
    //                                              object.m_uniqueId,
    //                                              object.m_type,
    //                                              object.m_line,
    //                                              object.m_parent,
    //                                               object.m_definition,
    //                                               object.m_child,
    //                                               object.m_sibling));

    unsigned long field1 = 0;
    unsigned long field2 = 0;
    unsigned long field3 = 0;
    SymbolId name = canonicalSymbols.getId(
        m_parse->getCompileSourceFile()->getSymbolTable()->getSymbol(
            object.m_name));
    field1 |= (name);  // 20 Bits => Filled 20 Bits (Of 64)
    field1 |= (((unsigned long)object.m_type)
               << (20));  // 12 Bits => Filled 32 Bits (Of 64)
    // UNUSED: field1 |= (((unsigned long) object.m_line)   << (20 + 12)); // 16
    // Bits => Filled 48 Bits (Of 64)
    field1 |=
        ((unsigned long)object.m_parent
         << (20 + 12 + 16));  // 16 Bits => Filled 64 Bits (Of 64) , Word Full
    field2 |= (object.m_parent >> (16));  //  4 Bits => Filled  4 Bits (Of 64)
    field2 |=
        (object.m_definition << (4));  // 20 Bits => Filled 24 Bits (Of 64)
    field2 |= (((unsigned long)object.m_child)
               << (4 + 20));  // 20 Bits => Filled 44 Bits (Of 64)
    field2 |=
        (((unsigned long)object.m_sibling)
         << (4 + 20 + 20));  // 20 Bits => Filled 64 Bits (Of 64) , Word Full
    field3 |= object.m_fileId;
    field3 |= (((unsigned long)object.m_line) << (32));
    PARSECACHE::VObject vostruct(field1, field2, field3);
    object_vec.push_back(vostruct);
  }
  // auto objectList = builder.CreateVector(object_vec);
  auto objectList = builder.CreateVectorOfStructs(object_vec);

  // std::cout << "SAVE: " << cacheFileName << " "
  //          << m_parse->getCompileSourceFile()->getSymbolTable()->getSymbol
  //          (m_parse->getFileId(0))
  //          << " NB: " <<   fcontent->getVObjects().size()
  //         << std::endl;

  /* Create Flatbuffers */
  auto ppcache = PARSECACHE::CreateParseCache(
      builder, header, errorSymbolPair.first, errorSymbolPair.second,
      elementList, objectList);
  FinishParseCacheBuffer(builder, ppcache);

  /* Save Flatbuffer */
  bool status = saveFlatbuffers(builder, cacheFileName);

  return status;
}
