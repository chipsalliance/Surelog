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
 * File:   Cache.cpp
 * Author: alain
 *
 * Created on April 28, 2017, 9:32 PM
 */
#include "Cache/Cache.h"

#include <sys/stat.h>
#include <sys/types.h>

#include <cstdio>
#include <ctime>
#include <iostream>

#include "CommandLine/CommandLineParser.h"
#include "flatbuffers/util.h"

namespace SURELOG {
namespace fs = std::filesystem;

const std::string& Cache::getExecutableTimeStamp() {
  static const std::string sExecTstamp(__DATE__ "-" __TIME__);
  return sExecTstamp;
}

time_t Cache::get_mtime(const fs::path& path) {
  std::string cpath = path.string();
  struct stat statbuf;
  if (stat(cpath.c_str(), &statbuf) == -1) {
    return -1;
  }
  return statbuf.st_mtime;
}

uint8_t* Cache::openFlatBuffers(const fs::path& cacheFileName) {
  const std::string filename = cacheFileName.string();
  FILE* file = fopen(filename.c_str(), "rb");
  if (file == nullptr) return nullptr;
  fseek(file, 0L, SEEK_END);
  unsigned int length = ftell(file);
  fseek(file, 0L, SEEK_SET);
  char* data = new char[length];
  size_t l = fread(data, sizeof(char), length, file);
  fclose(file);
  if (length != l) {
    delete[] data;
    return nullptr;
  }
  uint8_t* buffer_pointer = (uint8_t*)data;
  return buffer_pointer;
}

bool Cache::checkIfCacheIsValid(const SURELOG::CACHE::Header* header,
                                std::string schemaVersion,
                                const fs::path& cacheFileName) {
  /* Schema version */
  if (schemaVersion != header->flb_version()->c_str()) {
    return false;
  }

  /* Tool version */
  if (CommandLineParser::getVersionNumber() != header->sl_version()->c_str()) {
    return false;
  }

  /* Timestamp Tool that created Cache vs tool date */
  std::string execDate = getExecutableTimeStamp();
  if (execDate != header->sl_date_compiled()->c_str()) {
    return false;
  }

  /* Timestamp Cache vs Orig File */
  if (!cacheFileName.empty()) {
    time_t ct = get_mtime(cacheFileName);
    std::string fileName = header->file()->c_str();
    time_t ft = get_mtime(fileName.c_str());
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
  return true;
}

const flatbuffers::Offset<SURELOG::CACHE::Header> Cache::createHeader(
    flatbuffers::FlatBufferBuilder& builder, std::string schemaVersion,
    const fs::path& origFileName) {
  auto fName = builder.CreateString(origFileName.string());
  auto sl_version = builder.CreateString(CommandLineParser::getVersionNumber());
  auto sl_build_date = builder.CreateString(getExecutableTimeStamp());
  auto sl_flb_version = builder.CreateString(schemaVersion);
  std::time_t t_result = std::time(nullptr);
  auto file_creation_date = builder.CreateString(std::to_string(t_result));
  auto header = CACHE::CreateHeader(builder, sl_version, sl_flb_version,
                                    sl_build_date, file_creation_date, fName);
  return header;
}

bool Cache::saveFlatbuffers(flatbuffers::FlatBufferBuilder& builder,
                            const fs::path& cacheFileName) {
  const std::string filename = cacheFileName.string();
  const unsigned char* buf = builder.GetBufferPointer();
  int size = builder.GetSize();
  bool status = flatbuffers::SaveFile(filename.c_str(), (char*)buf, size, true);
  return status;
}

std::pair<flatbuffers::Offset<Cache::VectorOffsetError>,
          flatbuffers::Offset<Cache::VectorOffsetString>>
Cache::cacheErrors(flatbuffers::FlatBufferBuilder& builder,
                   SymbolTable& canonicalSymbols,
                   ErrorContainer* errorContainer, SymbolTable* symbols,
                   SymbolId subjectId) {
  const std::vector<Error>& errors = errorContainer->getErrors();
  std::vector<flatbuffers::Offset<SURELOG::CACHE::Error>> error_vec;
  for (const Error& error : errors) {
    const std::vector<Location>& locs = error.getLocations();
    if (!locs.empty()) {
      bool matchSubject = false;
      for (const Location& loc : locs) {
        if (loc.m_fileId == subjectId) {
          matchSubject = true;
          break;
        }
      }
      if (matchSubject) {
        std::vector<flatbuffers::Offset<SURELOG::CACHE::Location>> location_vec;
        for (const Location& loc : locs) {
          SymbolId canonicalFileId =
              canonicalSymbols.registerSymbol(symbols->getSymbol(loc.m_fileId));
          SymbolId canonicalObjectId =
              canonicalSymbols.registerSymbol(symbols->getSymbol(loc.m_object));
          auto locflb =
              CACHE::CreateLocation(builder, canonicalFileId, loc.m_line,
                                    loc.m_column, canonicalObjectId);
          location_vec.push_back(locflb);
        }
        auto locvec = builder.CreateVector(location_vec);
        auto err = CACHE::CreateError(builder, locvec, error.getType());
        error_vec.push_back(err);
      }
    }
  }

  /* Cache all the symbols */
  for (const auto& s : symbols->getSymbols()) {
    canonicalSymbols.registerSymbol(s);
  }

  auto symbolVec = builder.CreateVectorOfStrings(canonicalSymbols.getSymbols());
  auto errvec = builder.CreateVector(error_vec);
  return std::make_pair(errvec, symbolVec);
}

void Cache::restoreErrors(const VectorOffsetError* errorsBuf,
                          const VectorOffsetString* symbolsBuf,
                          SymbolTable& canonicalSymbols,
                          ErrorContainer* errorContainer,
                          SymbolTable* symbols) {
  for (unsigned int i = 0; i < symbolsBuf->size(); i++) {
    const std::string symbol = symbolsBuf->Get(i)->c_str();
    canonicalSymbols.registerSymbol(symbol);
  }
  for (unsigned int i = 0; i < errorsBuf->size(); i++) {
    auto errorFlb = errorsBuf->Get(i);
    std::vector<Location> locs;
    for (unsigned int j = 0; j < errorFlb->locations()->size(); j++) {
      auto locFlb = errorFlb->locations()->Get(j);
      SymbolId translFileId = symbols->registerSymbol(
          canonicalSymbols.getSymbol(locFlb->file_id()));
      SymbolId translObjectId =
          symbols->registerSymbol(canonicalSymbols.getSymbol(locFlb->object()));
      Location loc(translFileId, locFlb->line(), locFlb->column(),
                   translObjectId);
      locs.push_back(loc);
    }
    Error err((ErrorDefinition::ErrorType)errorFlb->error_id(), locs);
    errorContainer->addError(err, false);
  }
}

std::vector<CACHE::VObject> Cache::cacheVObjects(FileContent* fcontent,
                                                 SymbolTable& canonicalSymbols,
                                                 SymbolTable& fileTable,
                                                 SymbolId fileId) {
  /* Cache the design objects */
  // std::vector<flatbuffers::Offset<PARSECACHE::VObject>> object_vec;
  std::vector<CACHE::VObject> object_vec;
  if (!fcontent) return object_vec;
  if (fcontent->getVObjects().size() > Capacity) {
    std::cout << "INTERNAL ERROR: Cache is saturated, Use -nocache option\n";
    return object_vec;
  }
  for (size_t i = 0; i < fcontent->getVObjects().size(); i++) {
    VObject& object = fcontent->getVObjects()[i];

    // Lets compress this struct into 20 and 16 bits fields:
    //  object_vec.push_back(PARSECACHE::CreateVObject(builder,
    //                                              canonicalSymbols.getId(m_parse->getCompileSourceFile()->getSymbolTable()->getSymbol(object.m_name)),
    //                                              object.m_uniqueId,
    //                                              object.m_type,
    //                                              object.m_column,
    //                                              object.m_line,
    //                                              object.m_parent,
    //                                               object.m_definition,
    //                                               object.m_child,
    //                                               object.m_sibling));

    uint64_t field1 = 0;
    uint64_t field2 = 0;
    uint64_t field3 = 0;
    uint64_t field4 = 0;
    SymbolId name = canonicalSymbols.getId(fileTable.getSymbol(object.m_name));
    // clang-format off
    field1 |= 0x0000000000FFFFFF & (name);
    field1 |= 0x0000000FFF000000 & (((uint64_t)object.m_type)      << (24));
    field1 |= 0x0000FFF000000000 & (((uint64_t)object.m_column)    << (24 + 12));
    field1 |= 0xFFFF000000000000 & (((uint64_t)object.m_parent     << (24 + 12 + 12)));
    field2 |= 0x0000000000000FFF & (object.m_parent                >> (16));
    field2 |= 0x000000FFFFFFF000 & (((uint64_t)object.m_definition) << (12));
    field2 |= 0xFFFFFF0000000000 & (((uint64_t)object.m_child)     << (12 + 28));
    field3 |= 0x000000000000000F & (((uint64_t)object.m_child)     >> (24));
    field3 |= 0x00000000FFFFFFF0 & (object.m_sibling               << (4));
    field3 |= 0x00FFFFFF00000000 & (((uint64_t)object.m_fileId)    << (4 + 28));
    field3 |= 0xFF00000000000000 & (((uint64_t)object.m_line)      << (4 + 28 + 24));
    field4 |= 0x000000000000FFFF & (((uint64_t)object.m_line)      >> (8));
    field4 |= 0x000000FFFFFF0000 & (((uint64_t)object.m_endLine)   << (16));
    field4 |= 0x000FFF0000000000 & (((uint64_t)object.m_endColumn) << (16 + 24));
    // clang-format on
    SURELOG::CACHE::VObject vostruct(field1, field2, field3, field4);
    object_vec.push_back(vostruct);
  }
  // std::cout << "SAVE: " << cacheFileName << " "
  //          << fileTable.getSymbol(fileId)
  //          << " NB: " <<   fcontent->getVObjects().size()
  //         << std::endl;

  return object_vec;
}

void Cache::restoreVObjects(
    const flatbuffers::Vector<const SURELOG::CACHE::VObject*>* objects,
    SymbolTable& canonicalSymbols, SymbolTable& fileTable, SymbolId fileId,
    FileContent* fileContent) {
  /* Restore design objects */
  for (unsigned int i = 0; i < objects->size(); i++) {
    auto objectc = objects->Get(i);

    // VObject object
    // (m_parse->getCompileSourceFile()->getSymbolTable()->registerSymbol(canonicalSymbols.getSymbol(objectc->m_name())),
    //                (VObjectType) objectc->m_type(), objectc->m_uniqueId(),
    //                objectc->m_column(), objectc->m_line(),
    //                objectc->m_parent(), objectc->m_definition(),
    //               objectc->m_child(),  objectc->m_sibling());

    uint64_t field1 = objectc->field1();
    uint64_t field2 = objectc->field2();
    uint64_t field3 = objectc->field3();
    uint64_t field4 = objectc->field4();
    // Decode compression done when saving cache (see below)
    // clang-format off
    SymbolId name =            (field1 & 0x0000000000FFFFFF);
    unsigned short type =      (field1 & 0x0000000FFF000000) >> (24);
    unsigned short column =    (field1 & 0x0000FFF000000000) >> (24 + 12);
    NodeId parent         =    (field1 & 0xFFFF000000000000) >> (24 + 12 + 12);
    parent |=                  (field2 & 0x0000000000000FFF) << (16);
    NodeId definition =        (field2 & 0x000000FFFFFFF000) >> (12);
    NodeId child =             (field2 & 0xFFFFFF0000000000) >> (12 + 28);
    child  |=                  (field3 & 0x000000000000000F) << (24);
    NodeId sibling =           (field3 & 0x00000000FFFFFFF0) >> (4);
    SymbolId fileId =          (field3 & 0x00FFFFFF00000000) >> (4 + 28);
    unsigned int line =        (field3 & 0xFF00000000000000) >> (4 + 28 + 24);
    line |=                    (field4 & 0x000000000000FFFF) << (8);
    unsigned int endLine =     (field4 & 0x000000FFFFFF0000) >> (16);
    unsigned short endColumn = (field4 & 0x000FFF0000000000) >> (16 + 24);
    // clang-format on
    VObject object(fileTable.registerSymbol(canonicalSymbols.getSymbol(name)),
                   fileTable.registerSymbol(canonicalSymbols.getSymbol(fileId)),
                   (VObjectType)type, line, column, endLine, endColumn, parent,
                   definition, child, sibling);

    fileContent->getVObjects().push_back(object);
  }
}
}  // namespace SURELOG
