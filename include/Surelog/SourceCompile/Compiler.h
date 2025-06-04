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
 * File:   Compiler.h
 * Author: alain
 *
 * Created on March 4, 2017, 5:16 PM
 */

#ifndef SURELOG_COMPILER_H
#define SURELOG_COMPILER_H
#pragma once

#include <Surelog/Common/PathId.h>
#include <Surelog/Common/SymbolId.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/SourceCompile/CompileSourceFile.h>
#include <Surelog/SourceCompile/PreprocessFile.h>
#include <uhdm/Serializer.h>
#include <uhdm/vpi_user.h>

#include <string_view>

#ifdef USETBB
#include <tbb/task.h>
#include <tbb/task_group.h>
#include <tbb/task_scheduler_init.h>
#endif

#include <map>
#include <mutex>
#include <set>
#include <string>
#include <vector>

namespace SURELOG {
class CompileDesign;
class ConfigSet;
class Design;
class FileContent;
class LibrarySet;
class PreprocessFile;
class Session;

class Compiler {
 public:
  using PPFileMap =
      std::map<PathId, std::vector<PathId>, PathIdLessThanComparer>;
  explicit Compiler(Session* session);
  Compiler(Session* session, std::string_view text);
  Compiler(const Compiler& orig) = delete;
  virtual ~Compiler();

  bool compile();
  void purgeParsers();

  Session* getSession() { return m_session; }
  const Session* getSession() const { return m_session; }

  uhdm::Serializer& getSerializer() { return m_serializer; }
  void lockSerializer() { m_serializerMutex.lock(); }
  void unlockSerializer() { m_serializerMutex.unlock(); }

  std::vector<CompileSourceFile*>& getCompileSourceFiles() {
    return m_compilers;
  }
  const std::map<SymbolId, PreprocessFile::AntlrParserHandler*,
                 SymbolIdLessThanComparer>&
  getPpAntlrHandlerMap() const {
    return m_antlrPpMap;
  }
  void registerAntlrPpHandlerForId(SymbolId id,
                                   PreprocessFile::AntlrParserHandler* pp);
  PreprocessFile::AntlrParserHandler* getAntlrPpHandlerForId(SymbolId);

  // TODO: this should return a const Design, but can't be because
  // of Design having a bunch of non-const accessors. Address
  // these first.
  // All _modifying_ operations should be calls on the Compiler,
  // not on the handed out Design object, as the Compiler is owner
  // of the design.
  Design* getDesign() const { return m_design; }

  uhdm::Design* getUhdmDesign() const;
  vpiHandle getVpiDesign() const;
  CompileDesign* getCompileDesign() const { return m_compileDesign; }
  ErrorContainer::Stats getErrorStats() const;
  bool isLibraryFile(PathId id) const;
  const PPFileMap& getPPFileMap() { return m_ppFileMap; }

#ifdef USETBB
  tbb::task_group& getTaskGroup() { return m_taskGroup; }
#endif

 private:
  bool parseLibrariesDef_();

  bool ppinit_();
  bool createFileList_();
  bool createMultiProcessPreProcessor_();
  bool createMultiProcessParser_();
  bool parseinit_();
  bool pythoninit_();
  bool compileFileSet_(CompileSourceFile::Action action, bool allowMultithread,
                       std::vector<CompileSourceFile*>& container);
  bool compileOneFile_(CompileSourceFile* compileSource,
                       CompileSourceFile::Action action);
  bool cleanup_();

  void writeUhdmSourceFiles();
  void writePreprocMacroInstances();

 private:
  uhdm::Serializer m_serializer;
  Session* const m_session = nullptr;
  CompilationUnit* m_commonCompilationUnit;
  std::map<SymbolId, PreprocessFile::AntlrParserHandler*,
           SymbolIdLessThanComparer>
      m_antlrPpMap;
  std::vector<CompileSourceFile*> m_compilers;
  std::vector<CompileSourceFile*> m_compilersChunkFiles;
  std::vector<CompileSourceFile*> m_compilersParentFiles;
  std::vector<CompilationUnit*> m_compilationUnits;
  std::vector<Session*> m_sessions;
  LibrarySet* const m_librarySet = nullptr;
  ConfigSet* const m_configSet = nullptr;
  Design* const m_design = nullptr;
  PathIdSet m_libraryFiles;  // -v <file>
  std::string m_text;        // unit tests
  CompileDesign* m_compileDesign;
  PPFileMap m_ppFileMap;
  std::mutex m_serializerMutex;
#ifdef USETBB
  tbb::task_group m_taskGroup;
#endif
};

};  // namespace SURELOG

#endif /* SURELOG_COMPILER_H */
