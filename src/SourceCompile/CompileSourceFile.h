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

#ifndef COMPILESOURCEFILE_H
#define COMPILESOURCEFILE_H
#include "Python.h"
#include <string>
#include <vector>

#include "SourceCompile/ParseFile.h"
#include "SourceCompile/AnalyzeFile.h"
#include "SourceCompile/PreprocessFile.h"

namespace SURELOG {

class ParseFile;
class Compiler;
class PythonListen;

class CompileSourceFile {
 public:
  friend PreprocessFile;
  enum Action { Preprocess, PostPreprocess, Parse, PythonAPI };

  CompileSourceFile(SymbolId fileId, CommandLineParser* clp,
                    ErrorContainer* errors, Compiler* compiler,
                    SymbolTable* symbols, CompilationUnit* comp_unit,
                    Library* library);

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

  void setPythonInterp(PyThreadState* interpState);
  void shutdownPythonInterp();
  PyThreadState* getPythonInterp() { return m_interpState; }

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
  CommandLineParser* m_commandLineParser;
  ErrorContainer* m_errors;
  Compiler* m_compiler;
  PreprocessFile* m_pp;
  SymbolTable* m_symbolTable;
  std::vector<PreprocessFile*> m_ppIncludeVec;
  ParseFile* m_parser;
  CompilationUnit* m_compilationUnit;
  Action m_action;
  SymbolId m_ppResultFileId;
  std::map<SymbolId, PreprocessFile::AntlrParserHandler*>
      m_antlrPpMap;  // Preprocessor Antlr Handlers (One per included file)
  PyThreadState* m_interpState;
  PythonListen* m_pythonListener;
  AnalyzeFile* m_fileAnalyzer;
  Library* m_library;
};

};  // namespace SURELOG

#endif /* COMPILESOURCEFILE_H */
