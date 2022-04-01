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

#ifndef SURELOG_PARSEFILE_H
#define SURELOG_PARSEFILE_H
#pragma once

#include <Surelog/ErrorReporting/Error.h>

#include <filesystem>
#include <string>

namespace SURELOG {

class AntlrParserErrorListener;
class AntlrParserHandler;
class CompileSourceFile;
class CompilationUnit;
class ErrorContainer;
class FileContent;
class Library;
class SV3_1aPythonListener;
class SV3_1aTreeShapeListener;
class SymbolTable;

class ParseFile final {
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

  // Unit test constructor
  ParseFile(const std::string& text, CompileSourceFile* csf,
            CompilationUnit* compilationUnit, Library* library);

  bool parse();

  virtual ~ParseFile();
  bool needToParse();
  CompileSourceFile* getCompileSourceFile() const {
    return m_compileSourceFile;
  }
  CompilationUnit* getCompilationUnit() const { return m_compilationUnit; }
  Library* getLibrary() const { return m_library; }
  std::filesystem::path getFileName(unsigned int line);
  std::filesystem::path getPpFileName() const { return getSymbol(m_ppFileId); }
  SymbolTable* getSymbolTable();
  ErrorContainer* getErrorContainer();
  SymbolId getFileId(unsigned int line);
  SymbolId getRawFileId() const { return m_fileId; }
  SymbolId getPpFileId() const { return m_ppFileId; }
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

  AntlrParserHandler* getAntlrParserHandler() const {
    return m_antlrParserHandler;
  }

  void addLineTranslationInfo(LineTranslationInfo& info) {
    m_lineTranslationVec.push_back(info);
  }

  void addError(Error& error);
  SymbolId registerSymbol(std::string_view symbol);
  SymbolId getId(std::string_view symbol);
  std::string getSymbol(SymbolId id) const;
  bool usingCachedVersion() { return m_usingCachedVersion; }
  FileContent* getFileContent() { return m_fileContent; }
  void setFileContent(FileContent* content) { m_fileContent = content; }
  void setDebugAstModel() { debug_AstModel = true; }
  std::string getProfileInfo();
  void profileParser();

 private:
  SymbolId m_fileId;
  SymbolId m_ppFileId;
  CompileSourceFile* const m_compileSourceFile;
  CompilationUnit* const m_compilationUnit;
  Library* m_library = nullptr;
  AntlrParserHandler* m_antlrParserHandler = nullptr;
  SV3_1aTreeShapeListener* m_listener = nullptr;
  std::vector<LineTranslationInfo> m_lineTranslationVec;
  bool m_usingCachedVersion;
  bool m_keepParserHandler;
  FileContent* m_fileContent = nullptr;
  bool debug_AstModel;

  bool parseOneFile_(const std::string& fileName, unsigned int lineOffset);
  void buildLineInfoCache_();
  // For file chunk:
  std::vector<ParseFile*> m_children;
  ParseFile* const m_parent;
  unsigned int m_offsetLine;
  SymbolTable* const m_symbolTable;
  ErrorContainer* const m_errors;
  std::string m_profileInfo;
  std::string m_sourceText;  // For Unit tests
  std::vector<unsigned int> lineInfoCache;
  std::vector<SymbolId> fileInfoCache;
};

};  // namespace SURELOG

#endif /* SURELOG_PARSEFILE_H */
