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
 * File:   ParseFile.h
 * Author: alain
 *
 * Created on February 24, 2017, 10:03 PM
 */

#ifndef PARSEFILE_H
#define PARSEFILE_H

#include <string>

#include "Design/FileContent.h"
#include "SourceCompile/AntlrParserHandler.h"
#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"
#include "SourceCompile/CompilationUnit.h"

namespace SURELOG {

class SV3_1aTreeShapeListener;
class SV3_1aPythonListener;
class AntlrParserErrorListener;
class CompileSourceFile;

class ParseFile {
 public:
  friend class PythonListen;

  // Helper constructor used by SVLibShapeListener
  ParseFile(SymbolId fileId, SymbolTable* symbolTable, ErrorContainer* errors);

  // Regular file
  ParseFile(SymbolId fileId, CompileSourceFile* csf,
            CompilationUnit* compilationUnit, Library* library,
            SymbolId ppFileId, bool keepParserHandler);

  // File chunk
  ParseFile(CompileSourceFile* compileSourceFile, ParseFile* parent,
            SymbolId chunkFileId, unsigned int offsetLine);

  bool parse();

  virtual ~ParseFile();
  bool needToParse();
  CompileSourceFile* getCompileSourceFile() { return m_compileSourceFile; }
  CompilationUnit* getCompilationUnit() { return m_compilationUnit; }
  Library* getLibrary() { return m_library; }
  const std::string getFileName(unsigned int line);
  const std::string getPpFileName() { return getSymbol(m_ppFileId); }
  SymbolTable* getSymbolTable();
  ErrorContainer* getErrorContainer();
  SymbolId getFileId(unsigned int line);
  SymbolId getRawFileId() { return m_fileId; }
  SymbolId getPpFileId() { return m_ppFileId; }
  unsigned int getLineNb(unsigned int line);

  class LineTranslationInfo {
   public:
    LineTranslationInfo(SymbolId pretendFileId, unsigned int originalLine,
                        unsigned int pretendLine)
        : m_pretendFileId(pretendFileId),
          m_originalLine(originalLine),
          m_pretendLine(pretendLine) {}
    SymbolId m_pretendFileId;
    unsigned int m_originalLine;
    unsigned int m_pretendLine;
  };

  AntlrParserHandler* getAntlrParserHandler() { return m_antlrParserHandler; }

  void addLineTranslationInfo(LineTranslationInfo& info) {
    m_lineTranslationVec.push_back(info);
  }

  void addError(Error& error);
  SymbolId registerSymbol(const std::string symbol);
  SymbolId getId(const std::string symbol);
  const std::string getSymbol(SymbolId id);
  bool usingCachedVersion() { return m_usingCachedVersion; }
  FileContent* getFileContent() { return m_fileContent; }
  void setFileContent(FileContent* content) { m_fileContent = content; }
  void setDebugAstModel() { debug_AstModel = true; }
  std::string getProfileInfo();

 private:
  SymbolId m_fileId;
  SymbolId m_ppFileId;
  CompileSourceFile* m_compileSourceFile;
  CompilationUnit* m_compilationUnit;
  Library* m_library;
  AntlrParserHandler* m_antlrParserHandler;
  SV3_1aTreeShapeListener* m_listener;
  std::vector<LineTranslationInfo> m_lineTranslationVec;
  bool m_usingCachedVersion;
  bool m_keepParserHandler;
  FileContent* m_fileContent;
  bool debug_AstModel;

  bool parseOneFile_(std::string fileName, unsigned int lineOffset);

  // For file chunk:
  std::vector<ParseFile*> m_children;
  ParseFile* m_parent;
  unsigned int m_offsetLine;
  SymbolTable* m_symbolTable;
  ErrorContainer* m_errors;
  std::string m_profileInfo;
};

};  // namespace SURELOG

#endif /* PARSEFILE_H */
