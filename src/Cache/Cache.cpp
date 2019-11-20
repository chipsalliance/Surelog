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

#include <cstdio>
#include <ctime>
#include <sys/types.h>
#include <sys/stat.h>
#include <iostream>
#include "SourceCompile/SymbolTable.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Cache/Cache.h"
#include "CommandLine/CommandLineParser.h"
#include "flatbuffers/util.h"

using namespace SURELOG;

std::string ExecTimeStamp = std::string(__DATE__) + "-" + __TIME__;

std::string Cache::getExecutableTimeStamp() { return ExecTimeStamp; }

time_t Cache::get_mtime(const char* path) {
  struct stat statbuf;
  if (stat(path, &statbuf) == -1) {
    return -1;
  }
  return statbuf.st_mtime;
}

uint8_t* Cache::openFlatBuffers(std::string cacheFileName) {
  FILE* file = fopen(cacheFileName.c_str(), "rb");
  if (file == NULL) return NULL;
  fseek(file, 0L, SEEK_END);
  unsigned int length = ftell(file);
  fseek(file, 0L, SEEK_SET);
  char* data = new char[length];
  size_t l = fread(data, sizeof(char), length, file);
  fclose(file);
  if (length != l) {
    return NULL;
  }
  uint8_t* buffer_pointer = (uint8_t*)data;
  return buffer_pointer;
}

bool Cache::checkIfCacheIsValid(const SURELOG::CACHE::Header* header,
                                std::string schemaVersion,
                                std::string cacheFileName) {
  /* Schema version */
  if (schemaVersion != header->m_flb_version()->c_str()) {
    return false;
  }

  /* Tool version */
  if (CommandLineParser::getVersionNumber() !=
      header->m_sl_version()->c_str()) {
    return false;
  }

  /* Timestamp Tool that created Cache vs tool date */
  std::string execDate = getExecutableTimeStamp();
  if (execDate != header->m_sl_date_compiled()->c_str()) {
    return false;
  }

  /* Timestamp Cache vs Orig File */
  if (cacheFileName != "") {
    time_t ct = get_mtime(cacheFileName.c_str());
    std::string fileName = header->m_file()->c_str();
    time_t ft = get_mtime(fileName.c_str());
    if (ft == -1) return false;
    if (ct == -1) return false;
    if (ct < ft) return false;
  }

  return true;
}

const flatbuffers::Offset<SURELOG::CACHE::Header> Cache::createHeader(
    flatbuffers::FlatBufferBuilder& builder, std::string schemaVersion,
    std::string origFileName) {
  auto fName = builder.CreateString(origFileName);
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
                            std::string cacheFileName) {
  const unsigned char* buf = builder.GetBufferPointer();
  int size = builder.GetSize();
  bool status =
      flatbuffers::SaveFile(cacheFileName.c_str(), (char*)buf, size, true);
  return status;
}

std::pair<flatbuffers::Offset<
              flatbuffers::Vector<flatbuffers::Offset<SURELOG::CACHE::Error>>>,
          flatbuffers::Offset<
              flatbuffers::Vector<flatbuffers::Offset<flatbuffers::String>>>>
Cache::cacheErrors(flatbuffers::FlatBufferBuilder& builder,
                   SymbolTable& canonicalSymbols,
                   ErrorContainer* errorContainer, SymbolTable* symbols,
                   SymbolId subjectId) {
  std::vector<Error>& errors = errorContainer->getErrors();
  std::vector<flatbuffers::Offset<SURELOG::CACHE::Error>> error_vec;
  for (unsigned int i = 0; i < errors.size(); i++) {
    Error& error = errors[i];
    std::vector<Location>& locs = error.getLocations();
    if (locs.size()) {
      bool matchSubject = false;
      for (unsigned int j = 0; j < locs.size(); j++) {
        if (locs[j].m_fileId == subjectId) {
          matchSubject = true;
          break;
        }
      }
      if (matchSubject) {
        std::vector<flatbuffers::Offset<SURELOG::CACHE::Location>> location_vec;
        for (unsigned int j = 0; j < locs.size(); j++) {
          Location& loc = locs[j];
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
  for (auto itr = symbols->getSymbols().begin();
       itr != symbols->getSymbols().end(); itr++) {
    canonicalSymbols.registerSymbol(*itr);
  }

  auto symbolVec = builder.CreateVectorOfStrings(canonicalSymbols.getSymbols());
  auto errvec = builder.CreateVector(error_vec);
  return std::make_pair(errvec, symbolVec);
}

void Cache::restoreErrors(
    const flatbuffers::Vector<flatbuffers::Offset<SURELOG::CACHE::Error>>*
        errorsBuf,
    const flatbuffers::Vector<flatbuffers::Offset<flatbuffers::String>>*
        symbolsBuf,
    SymbolTable& canonicalSymbols, ErrorContainer* errorContainer,
    SymbolTable* symbols) {
  for (unsigned int i = 0; i < symbolsBuf->Length(); i++) {
    const std::string symbol = symbolsBuf->Get(i)->c_str();
    canonicalSymbols.registerSymbol(symbol);
  }
  for (unsigned int i = 0; i < errorsBuf->Length(); i++) {
    auto errorFlb = errorsBuf->Get(i);
    std::vector<Location> locs;
    for (unsigned int j = 0; j < errorFlb->m_locations()->Length(); j++) {
      auto locFlb = errorFlb->m_locations()->Get(j);
      SymbolId translFileId = symbols->registerSymbol(
          canonicalSymbols.getSymbol(locFlb->m_fileId()));
      SymbolId translObjectId = symbols->registerSymbol(
          canonicalSymbols.getSymbol(locFlb->m_object()));
      Location loc(translFileId, locFlb->m_line(), locFlb->m_column(),
                   translObjectId);
      locs.push_back(loc);
    }
    Error err((ErrorDefinition::ErrorType)errorFlb->m_errorId(), locs);
    errorContainer->addError(err, false);
  }
}

Cache::Cache() {}

Cache::Cache(const Cache& orig) {}

Cache::~Cache() {}
