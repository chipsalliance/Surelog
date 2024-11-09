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

#include "Surelog/Cache/Cache.h"

#include <capnp/serialize-packed.h>

#include <filesystem>
#include <functional>
#include <iostream>
#include <string>
#include <string_view>
#include <vector>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/SourceCompile/SymbolTable.h"

namespace SURELOG {
static constexpr std::string_view UnknownRawPath = "<unknown>";

std::string_view Cache::getExecutableTimeStamp() const {
  static constexpr std::string_view sExecTstamp(__DATE__ "-" __TIME__);
  return sExecTstamp;
}

bool Cache::checkIfCacheIsValid(const Header::Reader& header,
                                std::string_view schemaVersion,
                                PathId cacheFileId, PathId sourceFileId) const {
  // Schema version
  if (schemaVersion != header.getSchemaVersion().cStr()) {
    return false;
  }

  // Tool version
  if (CommandLineParser::getVersionNumber() != header.getSlVersion().cStr()) {
    return false;
  }

  // Timestamp Cache vs Orig File
  if (cacheFileId && sourceFileId) {
    FileSystem* const fileSystem = FileSystem::getInstance();
    std::filesystem::file_time_type ct = fileSystem->modtime(cacheFileId);
    std::filesystem::file_time_type ft = fileSystem->modtime(sourceFileId);

    if (ft == std::filesystem::file_time_type::min()) {
      return false;
    }
    if (ct == std::filesystem::file_time_type::min()) {
      return false;
    }
    if (ct < ft) {
      return false;
    }
  }
  return true;
}

void Cache::cacheHeader(Header::Builder builder,
                        std::string_view schemaVersion) {
  builder.setSchemaVersion(std::string(schemaVersion));
  builder.setSlVersion(std::string(CommandLineParser::getVersionNumber()));
}

void Cache::cacheErrors(
    ::capnp::List<::Error, ::capnp::Kind::STRUCT>::Builder targetErrors,
    SymbolTable& targetSymbols, const std::vector<Error>& sourceErrors,
    const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  for (size_t i = 0, ni = sourceErrors.size(); i < ni; ++i) {
    const Error& sourceError = sourceErrors[i];
    const auto& sourceLocations = sourceError.getLocations();

    ::Error::Builder targetError = targetErrors[i];
    targetError.setErrorId(sourceError.getType());

    ::capnp::List<::Location, ::capnp::Kind::STRUCT>::Builder targetLocations =
        targetError.initLocations(sourceLocations.size());
    for (size_t j = 0, nj = sourceLocations.size(); j < nj; ++j) {
      const Location& sourceLocation = sourceLocations[j];
      PathId fileId = fileSystem->copy(sourceLocation.m_fileId, &targetSymbols);
      SymbolId objectId =
          targetSymbols.copyFrom(sourceLocation.m_object, &sourceSymbols);

      ::Location::Builder targetLocation = targetLocations[j];
      targetLocation.setFileId((RawPathId)fileId);
      targetLocation.setLine(sourceLocation.m_line);
      targetLocation.setColumn(sourceLocation.m_column);
      targetLocation.setObject((RawSymbolId)objectId);
    }
  }
}

void Cache::cacheVObjects(
    ::capnp::List<::VObject, ::capnp::Kind::STRUCT>::Builder targetVObjects,
    SymbolTable& targetSymbols, const std::vector<VObject>& sourceVObjects,
    const SymbolTable& sourceSymbols) {
  if (sourceVObjects.size() > Capacity) {
    std::cerr << "INTERNAL ERROR: Cache is saturated, Use -nocache option\n";
    return;
  }
  // Convert a local symbol ID to a cache symbol ID to be stored.
  std::function<uint64_t(SymbolId)> toCacheSym = [&targetSymbols,
                                                  &sourceSymbols](SymbolId id) {
    return (RawSymbolId)targetSymbols.copyFrom(id, &sourceSymbols);
  };
  std::function<uint64_t(PathId)> toCachePath = [&targetSymbols](PathId id) {
    FileSystem* const fileSystem = FileSystem::getInstance();
    return (RawPathId)fileSystem->copy(id, &targetSymbols);
  };

  for (size_t i = 0, ni = sourceVObjects.size(); i < ni; ++i) {
    // Lets compress this struct into 20 and 16 bits fields:
    //  object_vec.push_back(PARSECACHE::CreateVObject(builder,
    //                                                 toCacheSym(object.m_name),
    //                                                 object.m_uniqueId,
    //                                                 object.m_type,
    //                                                 object.m_column,
    //                                                 object.m_line,
    //                                                 object.m_parent,
    //                                                 object.m_definition,
    //                                                 object.m_child,
    //                                                 object.m_sibling));

    uint64_t field1 = 0;
    uint64_t field2 = 0;
    uint64_t field3 = 0;
    uint64_t field4 = 0;
    const VObject& object = sourceVObjects[i];

    // clang-format off
    field1 |= 0x0000000000FFFFFF & toCacheSym(object.m_name);
    field1 |= 0x0000000FFF000000 & (((uint64_t)object.m_type)                  << (24));
    field1 |= 0x0000FFF000000000 & (((uint64_t)object.m_column)                << (24 + 12));
    field1 |= 0xFFFF000000000000 & (((uint64_t)(RawNodeId)object.m_parent)     << (24 + 12 + 12));
    field2 |= 0x0000000000000FFF & (((uint64_t)(RawNodeId)object.m_parent)     >> (16));
    field2 |= 0x000000FFFFFFF000 & (((uint64_t)(RawNodeId)object.m_definition) << (12));
    field2 |= 0xFFFFFF0000000000 & (((uint64_t)(RawNodeId)object.m_child)      << (12 + 28));
    field3 |= 0x000000000000000F & (((uint64_t)(RawNodeId)object.m_child)      >> (24));
    field3 |= 0x00000000FFFFFFF0 & (((uint64_t)(RawNodeId)object.m_sibling)    << (4));
    field3 |= 0x00FFFFFF00000000 & (toCachePath(object.m_fileId)               << (4 + 28));
    field3 |= 0xFF00000000000000 & (((uint64_t)object.m_line)                  << (4 + 28 + 24));
    field4 |= 0x000000000000FFFF & (((uint64_t)object.m_line)                  >> (8));
    field4 |= 0x000000FFFFFF0000 & (((uint64_t)object.m_endLine)               << (16));
    field4 |= 0x000FFF0000000000 & (((uint64_t)object.m_endColumn)             << (16 + 24));
    // clang-format on

    ::VObject::Builder targetVObject = targetVObjects[i];
    targetVObject.setField1(field1);
    targetVObject.setField2(field2);
    targetVObject.setField3(field3);
    targetVObject.setField4(field4);
  }
}

void Cache::cacheSymbols(
    ::capnp::List<::capnp::Text, ::capnp::Kind::BLOB>::Builder targetSymbols,
    const std::vector<std::string_view>& sourceSymbols) {
  for (size_t i = 0, ni = sourceSymbols.size(); i < ni; ++i) {
    const std::string symbol(sourceSymbols[i]);
    targetSymbols.set(i, symbol.c_str());
  }
}

void Cache::restoreSymbols(
    SymbolTable& targetSymbols,
    const ::capnp::List<::capnp::Text>::Reader& sourceSymbols) {
  for (const ::capnp::Text::Reader& sourceSymbol : sourceSymbols) {
    targetSymbols.registerSymbol(sourceSymbol.cStr());
  }
}

void Cache::restoreErrors(ErrorContainer* errorContainer,
                          SymbolTable& targetSymbols,
                          const ::capnp::List<::Error>::Reader& sourceErrors,
                          const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  for (const ::Error::Reader& sourceError : sourceErrors) {
    std::vector<Location> targetLocations;
    for (const ::Location::Reader& sourceLocation :
         sourceError.getLocations()) {
      PathId fileId = fileSystem->toPathId(
          fileSystem->remap(sourceSymbols.getSymbol(
              SymbolId(sourceLocation.getFileId(), UnknownRawPath))),
          &targetSymbols);
      SymbolId objectId = targetSymbols.copyFrom(
          SymbolId(sourceLocation.getObject(), UnknownRawPath), &sourceSymbols);
      targetLocations.emplace_back(fileId, sourceLocation.getLine(),
                                   sourceLocation.getColumn(), objectId);
    }

    Error error(
        static_cast<ErrorDefinition::ErrorType>(sourceError.getErrorId()),
        targetLocations);
    errorContainer->addError(error, false);
  }
}

void Cache::restoreVObjects(
    std::vector<VObject>& targetVObjects, SymbolTable& targetSymbols,
    const ::capnp::List<::VObject>::Reader& sourceVObjects,
    const SymbolTable& sourceSymbols) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  /* Restore design objects */
  targetVObjects.clear();
  targetVObjects.reserve(sourceVObjects.size());
  for (const ::VObject::Reader& sourceVObject : sourceVObjects) {
    // VObject object
    // (m_parse->getCompileSourceFile()->getSymbolTable()->registerSymbol(canonicalSymbols.getSymbol(objectc->m_name())),
    //                (VObjectType) objectc->m_type(), objectc->m_uniqueId(),
    //                objectc->m_column(), objectc->m_line(),
    //                objectc->m_parent(), objectc->m_definition(),
    //               objectc->m_child(),  objectc->m_sibling());

    uint64_t field1 = sourceVObject.getField1();
    uint64_t field2 = sourceVObject.getField2();
    uint64_t field3 = sourceVObject.getField3();
    uint64_t field4 = sourceVObject.getField4();
    // Decode compression done when saving cache (see below)
    // clang-format off
    RawSymbolId name =      (field1 & 0x0000000000FFFFFF);
    uint16_t type =         (field1 & 0x0000000FFF000000) >> (24);
    uint16_t column =       (field1 & 0x0000FFF000000000) >> (24 + 12);
    RawNodeId parent =      (field1 & 0xFFFF000000000000) >> (24 + 12 + 12);
    parent |=               (field2 & 0x0000000000000FFF) << (16);
    RawNodeId definition =  (field2 & 0x000000FFFFFFF000) >> (12);
    RawNodeId child =       (field2 & 0xFFFFFF0000000000) >> (12 + 28);
    child |=                (field3 & 0x000000000000000F) << (24);
    RawNodeId sibling =     (field3 & 0x00000000FFFFFFF0) >> (4);
    RawSymbolId fileId =    (field3 & 0x00FFFFFF00000000) >> (4 + 28);
    uint32_t line =         (field3 & 0xFF00000000000000) >> (4 + 28 + 24);
    line |=                 (field4 & 0x000000000000FFFF) << (8);
    uint32_t endLine =      (field4 & 0x000000FFFFFF0000) >> (16);
    uint16_t endColumn =    (field4 & 0x000FFF0000000000) >> (16 + 24);
    // clang-format on

    targetVObjects.emplace_back(
        targetSymbols.copyFrom(SymbolId(name, UnknownRawPath), &sourceSymbols),
        fileSystem->toPathId(fileSystem->remap(sourceSymbols.getSymbol(
                                 SymbolId(fileId, UnknownRawPath))),
                             &targetSymbols),
        (VObjectType)type, line, column, endLine, endColumn, NodeId(parent),
        NodeId(definition), NodeId(child), NodeId(sibling));
  }
}
}  // namespace SURELOG
