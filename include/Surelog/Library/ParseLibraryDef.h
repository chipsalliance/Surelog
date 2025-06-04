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
 * File:   ParseLibraryDef.h
 * Author: alain
 *
 * Created on January 27, 2018, 5:05 PM
 */

#ifndef SURELOG_PARSELIBRARYDEF_H
#define SURELOG_PARSELIBRARYDEF_H
#pragma once

#include <Surelog/Common/PathId.h>
#include <Surelog/Common/SymbolId.h>

namespace SURELOG {
class ConfigSet;
class FileContent;
class Library;
class LibrarySet;
class Session;

class ParseLibraryDef final {
 public:
  ParseLibraryDef(Session* session, LibrarySet* librarySet,
                  ConfigSet* configSet);
  ParseLibraryDef(const ParseLibraryDef& orig) = delete;

  bool parseLibrariesDefinition();
  bool parseLibraryDefinition(PathId file, Library* lib = nullptr);
  bool parseConfigDefinition();

  PathId getFileId() const { return m_fileId; }
  LibrarySet* getLibrarySet() const { return m_librarySet; }
  ConfigSet* getConfigSet() const { return m_configSet; }

 private:
  Session* const m_session = nullptr;
  PathId m_fileId;
  LibrarySet* const m_librarySet = nullptr;
  ConfigSet* const m_configSet = nullptr;
  FileContent* m_fileContent = nullptr;
};

}  // namespace SURELOG

#endif /* SURELOG_PARSELIBRARYDEF_H */
