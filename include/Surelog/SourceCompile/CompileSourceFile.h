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

#include <Surelog/Common/SymbolId.h>
#include <Surelog/SourceCompile/PreprocessFile.h>

#include <map>
#include <string>
#include <vector>

#ifdef SURELOG_WITH_PYTHON
struct _ts;
typedef struct _ts PyThreadState;
#endif

namespace SURELOG {

class AnalyzeFile;
class CommandLineParser;
class CompilationUnit;
class Compiler;
class ErrorContainer;
class Library;
class ParseFile;
class PreprocessFile;
class PythonListen;
class SymbolTable;

class CompileSourceFile {
 public:
  friend PreprocessFile;
  enum Action { Preprocess, PostPreprocess, Parse, PythonAPI };

  CompileSourceFile(SymbolId fileId, CommandLineParser* clp,
                    ErrorContainer* errors, Compiler* compiler,
                    SymbolTable* symbols, CompilationUnit* comp_unit,
                    Library* library, const std::string& = "");

  // Chunk File:
  CompileSourceFile(CompileSourceFile* parent, SymbolId ppResultFileId,
                    unsigned int lineOffset);

  bool compile(Action action);
  CompileSourceFile(const CompileSourceFile& orig);
  virtual ~CompileSourceFile();
  Compiler* getCompiler() { return m_compiler; }
  ErrorContainer* getErrorContainer() { return m_errors; }
  CommandLineParser* getCommandLineParser() { return m_commandLineParser; }
  SymbolTable* getSymbolTable() { return m_symbolTable; }
  Library* getLibrary() { return m_library; }
  void registerPP(PreprocessFile* pp) { m_ppIncludeVec.push_back(pp); }
  bool initParser();

  const std::map<SymbolId, PreprocessFile::AntlrParserHandler*>&
  getPpAntlrHandlerMap() {
    return m_antlrPpMap;
  }
  void registerAntlrPpHandlerForId(SymbolId id,
                                   PreprocessFile::AntlrParserHandler* pp);
  PreprocessFile::AntlrParserHandler* getAntlrPpHandlerForId(SymbolId);

#ifdef SURELOG_WITH_PYTHON
  void setPythonInterp(PyThreadState* interpState);
  void shutdownPythonInterp();
  PyThreadState* getPythonInterp() { return m_interpState; }
#endif

  void setSymbolTable(SymbolTable* symbols);
  void setErrorContainer(ErrorContainer* errors) { m_errors = errors; }

  unsigned int getJobSize(Action action);

  SymbolId getFileId() { return m_fileId; }
  SymbolId getPpOutputFileId() { return m_ppResultFileId; }

  void setFileAnalyzer(AnalyzeFile* analyzer) { m_fileAnalyzer = analyzer; }
  AnalyzeFile* getFileAnalyzer() { return m_fileAnalyzer; }

  ParseFile* getParser() { return m_parser; }
  PreprocessFile* getPreprocessor() { return m_pp; }

 private:
  bool preprocess_();
  bool postPreprocess_();

  bool parse_();

  bool pythonAPI_();

  SymbolId m_fileId;
  CommandLineParser* m_commandLineParser = nullptr;
  ErrorContainer* m_errors = nullptr;
  Compiler* m_compiler = nullptr;
  PreprocessFile* m_pp = nullptr;
  SymbolTable* m_symbolTable = nullptr;
  std::vector<PreprocessFile*> m_ppIncludeVec;
  ParseFile* m_parser = nullptr;
  CompilationUnit* m_compilationUnit;
  Action m_action;
  SymbolId m_ppResultFileId;
  std::map<SymbolId, PreprocessFile::AntlrParserHandler*>
      m_antlrPpMap;  // Preprocessor Antlr Handlers (One per included file)
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
