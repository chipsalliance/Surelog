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
 * File:   CompileSourceFile.h
 * Author: alain
 *
 * Created on February 20, 2017, 9:54 PM
 */

#ifndef SURELOG_COMPILESOURCEFILE_H
#define SURELOG_COMPILESOURCEFILE_H
#pragma once

#include <Surelog/Common/PathId.h>
#include <Surelog/Common/SymbolId.h>
#include <Surelog/SourceCompile/PreprocessFile.h>
#include <uhdm/containers.h>

#include <cstdint>
#include <map>
#include <string>
#include <string_view>
#include <vector>

#ifdef SURELOG_WITH_PYTHON
struct _ts;
using PyThreadState = struct _ts;
#endif

namespace SURELOG {
class AnalyzeFile;
class CompilationUnit;
class Compiler;
class Library;
class ParseFile;
class PreprocessFile;
class PythonListen;
class Session;

class CompileSourceFile final {
 public:
  friend class Compiler;
  friend class PreprocessFile;

  enum class Action { Preprocess, PostPreprocess, Parse, PythonAPI };

  CompileSourceFile(Session* session, PathId fileId, Compiler* compiler,
                    CompilationUnit* comp_unit, Library* library,
                    std::string_view = "");

  // Chunk File:
  CompileSourceFile(Session* session, CompileSourceFile* parent,
                    PathId ppResultFileId, uint32_t lineOffset);
  CompileSourceFile(const CompileSourceFile& orig);
  ~CompileSourceFile();

  bool compile(Action action);

  Compiler* getCompiler() const { return m_compiler; }
  Library* getLibrary() const { return m_library; }

  Session* getSession() { return m_session; }
  const Session* getSession() const { return m_session; }
  void setSession(Session* session) { m_session = session; }

  void registerPP(PreprocessFile* pp) { m_ppIncludeVec.push_back(pp); }
  bool initParser();
  void setParser(ParseFile* pf) { m_parser = pf; }

  const std::map<SymbolId, PreprocessFile::AntlrParserHandler*,
                 SymbolIdLessThanComparer>&
  getPpAntlrHandlerMap() const {
    return m_antlrPpMacroMap;
  }
  void registerAntlrPpHandlerForId(SymbolId id,
                                   PreprocessFile::AntlrParserHandler* pp);
  void registerAntlrPpHandlerForId(PathId id,
                                   PreprocessFile::AntlrParserHandler* pp);
  PreprocessFile::AntlrParserHandler* getAntlrPpHandlerForId(SymbolId);
  PreprocessFile::AntlrParserHandler* getAntlrPpHandlerForId(PathId);

#ifdef SURELOG_WITH_PYTHON
  void setPythonInterp(PyThreadState* interpState);
  void shutdownPythonInterp();
  PyThreadState* getPythonInterp() { return m_interpState; }
#endif

  // Get size of job approximated by size of file to process.
  uint64_t getJobSize(Action action) const;

  PathId getFileId() const { return m_fileId; }
  PathId getPpOutputFileId() const { return m_ppResultFileId; }

  void setFileAnalyzer(AnalyzeFile* analyzer) { m_fileAnalyzer = analyzer; }
  AnalyzeFile* getFileAnalyzer() const { return m_fileAnalyzer; }

  ParseFile* getParser() const { return m_parser; }
  PreprocessFile* getPreprocessor() const { return m_pp; }

  const uhdm::PreprocMacroInstanceCollection& getPreprocMacroInstances() const {
    return m_preprocMacroInstances;
  }

 private:
  bool preprocess_();
  bool postPreprocess_();

  bool parse_();
  bool pythonAPI_();

  uhdm::PreprocMacroInstanceCollection& getPreprocMacroInstances() {
    return m_preprocMacroInstances;
  }

  Session* m_session = nullptr;
  PathId m_fileId;
  Compiler* m_compiler = nullptr;
  PreprocessFile* m_pp = nullptr;
  std::vector<PreprocessFile*> m_ppIncludeVec;
  ParseFile* m_parser = nullptr;
  CompilationUnit* m_compilationUnit = nullptr;
  Action m_action = Action::Preprocess;
  PathId m_ppResultFileId;
  std::map<SymbolId, PreprocessFile::AntlrParserHandler*,
           SymbolIdLessThanComparer>
      m_antlrPpMacroMap;  // Preprocessor Antlr Handlers (One per macro)
  std::map<PathId, PreprocessFile::AntlrParserHandler*, PathIdLessThanComparer>
      m_antlrPpFileMap;  // Preprocessor Antlr Handlers (One per included file)
  uhdm::PreprocMacroInstanceCollection m_preprocMacroInstances;
#ifdef SURELOG_WITH_PYTHON
  PyThreadState* m_interpState = nullptr;
  PythonListen* m_pythonListener = nullptr;
#endif
  AnalyzeFile* m_fileAnalyzer = nullptr;
  Library* m_library = nullptr;
  std::string m_text;  // unit test
};

};  // namespace SURELOG

#endif /* SURELOG_COMPILESOURCEFILE_H */
