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

#ifndef COMPILER_H
#define COMPILER_H

#include <string>
#include <set>
#include <map>
#include <thread>

#include "Config/ConfigSet.h"
#include "Design/Design.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Library/LibrarySet.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/SymbolTable.h"
#include "sv_vpi_user.h"

#ifdef USETBB
#  include <tbb/task.h>
#  include <tbb/task_group.h>
#  include "tbb/task_scheduler_init.h"
#endif

namespace SURELOG {

class PreprocessFile;
class FileContent;

class Compiler {
 public:
  Compiler(CommandLineParser* commandLineParser, ErrorContainer* errors,
           SymbolTable* symbolTable);
  virtual ~Compiler();

  bool compile();
  CommandLineParser* getCommandLineParser() { return m_commandLineParser; }
  SymbolTable* getSymbolTable() { return m_symbolTable; }
  ErrorContainer* getErrorContainer() { return m_errors; }

  const std::map<SymbolId, PreprocessFile::AntlrParserHandler*>&
  getPpAntlrHandlerMap() {
    return m_antlrPpMap;
  }
  void registerAntlrPpHandlerForId(SymbolId id,
                                   PreprocessFile::AntlrParserHandler* pp);
  PreprocessFile::AntlrParserHandler* getAntlrPpHandlerForId(SymbolId);

  LibrarySet* getLibrarySet() { return m_librarySet; }
  Design* getDesign() { return m_design; }
  vpiHandle getUhdmDesign() { return m_uhdmDesign; }

  ErrorContainer::Stats getErrorStats() const;
  bool isLibraryFile(SymbolId id) const;

#ifdef USETBB
  tbb::task_group& getTaskGroup() { return m_taskGroup; }
#endif

 private:
  Compiler(const Compiler& orig) = delete;
  bool parseLibrariesDef_();

  bool ppinit_();
  bool createFileList_();
  bool createMultiProcess_();
  bool parseinit_();
  bool pythoninit_();
  bool compileFileSet_(CompileSourceFile::Action action, bool allowMultithread,
                       std::vector<CompileSourceFile*>& container);
  bool compileOneFile_(CompileSourceFile* compileSource,
                       CompileSourceFile::Action action);
  bool cleanup_();

  CommandLineParser* m_commandLineParser;
  ErrorContainer* m_errors;
  SymbolTable* m_symbolTable;
  CompilationUnit* m_commonCompilationUnit;
  std::map<SymbolId, PreprocessFile::AntlrParserHandler*> m_antlrPpMap;
  std::vector<CompileSourceFile*> m_compilers;
  std::vector<CompileSourceFile*> m_compilersChunkFiles;
  std::vector<CompileSourceFile*> m_compilersParentFiles;
  std::vector<CompilationUnit*> m_compilationUnits;
  std::vector<SymbolTable*> m_symbolTables;
  std::vector<ErrorContainer*> m_errorContainers;
  LibrarySet* m_librarySet;
  ConfigSet* m_configSet;
  Design* m_design;
  vpiHandle m_uhdmDesign;
  std::set<SymbolId> m_libraryFiles;  // -v <file>

#ifdef USETBB
  tbb::task_group m_taskGroup;
#endif
};

};  // namespace SURELOG

#endif /* COMPILER_H */
