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
 * File:   PreprocessFile.h
 * Author: alain
 *
 * Created on February 24, 2017, 9:37 PM
 */

#ifndef SURELOG_PREPROCESSFILE_H
#define SURELOG_PREPROCESSFILE_H
#pragma once

#include <Surelog/Common/Containers.h>
#include <Surelog/Common/PathId.h>
#include <Surelog/Common/SymbolId.h>
#include <Surelog/SourceCompile/IncludeFileInfo.h>
#include <Surelog/SourceCompile/LoopCheck.h>
#include <Surelog/SourceCompile/MacroInfo.h>

#include <cstddef>
#include <cstdint>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace antlr4 {
class ANTLRInputStream;
class CommonTokenStream;
namespace tree {
class ParseTree;
}
}  // namespace antlr4

namespace SURELOG {
class CompilationUnit;
class CompileSourceFile;
class Error;
class FileContent;
class Library;
class MacroInfo;
class Session;
class SV3_1aPpLexer;
class SV3_1aPpParser;
class SV3_1aPpParserBaseListener;

#define LINE1 1

enum VerilogVersion {
  NoVersion,
  Verilog1995,
  Verilog2001,
  Verilog2005,
  SVerilog2005,
  Verilog2009,
  SystemVerilog
};

/* Can be either an include file or a macro definition being evaluated */
class PreprocessFile final {
 public:
  class SpecialInstructions;
  class DescriptiveErrorListener;

  /* Constructors */
  PreprocessFile(Session* session, PathId fileId, CompileSourceFile* csf,
                 SpecialInstructions& instructions,
                 CompilationUnit* compilationUnit, Library* library,
                 PreprocessFile* includer = nullptr, uint32_t includerLine = 0);
  PreprocessFile(Session* session, SymbolId macroId, CompileSourceFile* csf,
                 SpecialInstructions& instructions,
                 CompilationUnit* compilationUnit, Library* library,
                 PreprocessFile* includer, uint32_t includerLine,
                 std::string_view macroBody = "", MacroInfo* = nullptr,
                 PathId fileId = BadPathId,
                 PathId embeddedMacroCallFile = BadPathId,
                 uint32_t embeddedMacroCallLine = 0,
                 uint16_t embeddedMacroCallColumn = 0);
  ~PreprocessFile();

  /* Main function */
  bool preprocess();
  std::tuple<const std::string&, LineColumn> getPreProcessedFileContent() const;

  /* Macro manipulations */
  MacroInfo* defineMacro(std::string_view name, MacroInfo::DefType defType,
                         uint32_t startLine, uint16_t startColumn,
                         uint32_t endLine, uint16_t endColumn,
                         uint16_t nameStartColumn, uint16_t bodyStartColumn,
                         std::string_view arguments,
                         const std::vector<LineColumn>& argumentPositions,
                         const std::vector<std::string>& tokens,
                         const std::vector<LineColumn>& tokenPositions);
  void addMacro(MacroInfo* info);  // Used by PPCache
  std::tuple<bool, std::string, std::vector<LineColumn>, LineColumn> getMacro(
      std::string_view name, std::vector<std::string>& actual_arguments,
      PreprocessFile* callingFile, uint32_t callingLine, LoopCheck& loopChecker,
      SpecialInstructions& instructions,
      PathId embeddedMacroCallFile = BadPathId,
      uint32_t embeddedMacroCallLine = 0, uint16_t embeddedMacroCallColumn = 0);
  MacroInfo* undefineMacro(std::string_view name, uint32_t startLine,
                           uint16_t startColumn, uint32_t endLine,
                           uint16_t endColumn, uint16_t nameStartColumn);
  MacroInfo* undefineAllMacros(uint32_t startLine, uint16_t startColumn,
                               uint32_t endLine, uint16_t endColumn);
  bool isMacroBody() const { return !m_macroBody.empty(); }
  std::string_view getMacroBody() const { return m_macroBody; }
  MacroInfo* getMacroInfo() { return m_macroInfo; }
  SymbolId getMacroSignature();
  const MacroStorage& getMacros() const { return m_macros; }
  MacroInfo* getMacro(std::string_view name);

  CompileSourceFile* getCompileSourceFile() const {
    return m_compileSourceFile;
  }
  CompilationUnit* getCompilationUnit() const { return m_compilationUnit; }
  Library* getLibrary() const { return m_library; }
  antlr4::CommonTokenStream* getTokenStream() const {
    return m_antlrParserHandler ? m_antlrParserHandler->m_pptokens : nullptr;
  }

  PathId getFileId(uint32_t line) const;
  PathId getIncluderFileId(uint32_t line) const;
  PathId getRawFileId() const { return m_fileId; }
  uint32_t getLineNb(uint32_t line);
  PreprocessFile* getIncluder() const { return m_includer; }
  uint32_t getIncluderLine() const { return m_includerLine; }
  size_t getLineCount() const { return m_lineCount; }
  void setLineCount(size_t count) { m_lineCount = count; }
  LineColumn getCurrentPosition() const;
  const std::vector<IncludeFileInfo>& getIncludeFileInfo() const {
    return m_includeFileInfo;
  }
  int32_t addIncludeFileInfo(IncludeFileInfo::Context context,
                             IncludeFileInfo::Action action,
                             const MacroInfo* macroDefinition,
                             PathId sectionFileId, uint32_t sectionLine,
                             uint16_t sectionColumn, uint32_t sourceLine,
                             uint16_t sourceColumn, SymbolId symbolId,
                             uint32_t symbolLine, uint16_t symbolColumn,
                             int32_t indexOpposite = -1);
  void clearIncludeFileInfo();
  void reportIncludeInfo(std::ostream& strm) const;

  IncludeFileInfo& getIncludeFileInfo(int32_t index) {
    if (index >= 0 && index < ((int32_t)m_includeFileInfo.size()))
      return m_includeFileInfo[index];
    else
      return s_badIncludeFileInfo;
  }

  PathId getEmbeddedMacroCallFile() const { return m_embeddedMacroCallFile; }
  uint32_t getEmbeddedMacroCallLine() const { return m_embeddedMacroCallLine; }
  uint16_t getEmbeddedMacroCallColumn() const {
    return m_embeddedMacroCallColumn;
  }

  /* Markings */
  static const char* const MacroNotDefined;
  static const char* const PP__Line__Marking;
  static const char* const PP__File__Marking;

 public:
  /* Instructions passed from calling scope */
  class SpecialInstructions final {
   public:
    enum TraceInstr : bool { Mute = true, DontMute = false };
    enum EmptyMacroInstr : bool { Mark = true, DontMark = false };
    enum FileLineInfoInstr : bool { Filter = true, DontFilter = false };
    enum CheckLoopInstr : bool { CheckLoop = true, DontCheckLoop = false };
    enum AsIsUndefinedMacroInstr : bool {
      AsIsUndefinedMacro = true,
      ComplainUndefinedMacro = false
    };
    enum PersistMacroInstr : bool { Persist = true, DontPersist = false };
    enum EvaluateInstr : bool { Evaluate = true, DontEvaluate = false };
    SpecialInstructions()
        : m_mute(DontMute),
          m_mark_empty_macro(DontMark),
          m_filterFileLine(DontFilter),
          m_check_macro_loop(DontCheckLoop),
          m_as_is_undefined_macro(ComplainUndefinedMacro),
          m_evaluate(Evaluate),
          m_persist(DontPersist) {}
    SpecialInstructions(SpecialInstructions& rhs)

        = default;
    SpecialInstructions(TraceInstr mute, EmptyMacroInstr mark_empty_macro,
                        FileLineInfoInstr filterFileLine,
                        CheckLoopInstr check_macro_loop,
                        AsIsUndefinedMacroInstr as_is_undefined_macro,
                        EvaluateInstr evaluate = Evaluate,
                        PersistMacroInstr persist = DontPersist)
        : m_mute(mute),
          m_mark_empty_macro(mark_empty_macro),
          m_filterFileLine(filterFileLine),
          m_check_macro_loop(check_macro_loop),
          m_as_is_undefined_macro(as_is_undefined_macro),
          m_evaluate(evaluate),
          m_persist(persist) {}
    void print();
    TraceInstr m_mute;
    EmptyMacroInstr m_mark_empty_macro;
    FileLineInfoInstr m_filterFileLine;
    CheckLoopInstr m_check_macro_loop;
    AsIsUndefinedMacroInstr m_as_is_undefined_macro;
    EvaluateInstr m_evaluate;
    PersistMacroInstr m_persist;
  };

  std::string evaluateMacroInstance(
      std::string_view macro_instance, PreprocessFile* callingFile,
      uint32_t callingLine, uint16_t callingColumn,
      SpecialInstructions::CheckLoopInstr checkMacroLoop,
      SpecialInstructions::AsIsUndefinedMacroInstr);

  /* Incoming `line handling */
  struct LineTranslationInfo final {
    LineTranslationInfo(PathId pretendFileId, uint32_t originalLine,
                        uint32_t pretendLine)
        : m_pretendFileId(pretendFileId),
          m_originalLine(originalLine),
          m_pretendLine(pretendLine) {}
    const PathId m_pretendFileId;
    const uint32_t m_originalLine = 0;
    const uint32_t m_pretendLine = 0;
  };

  /* `ifdef, `ifndef, `elsif, `else Stack */
  struct IfElseItem final {
    enum Type { IFDEF, IFNDEF, ELSIF, ELSE };
    std::string m_macroName;
    bool m_defined = false;
    Type m_type = Type::IFDEF;
    bool m_previousActiveState = false;
  };
  using IfElseStack = std::vector<IfElseItem>;
  IfElseStack m_ifStack;
  IfElseStack& getStack();

  /* Antlr parser container */
  struct AntlrParserHandler final {
    AntlrParserHandler() = default;
    ~AntlrParserHandler();
    bool m_clearAntlrCache = false;
    antlr4::ANTLRInputStream* m_inputStream = nullptr;
    SV3_1aPpLexer* m_pplexer = nullptr;
    antlr4::CommonTokenStream* m_pptokens = nullptr;
    SV3_1aPpParser* m_ppparser = nullptr;
    antlr4::tree::ParseTree* m_pptree = nullptr;
    DescriptiveErrorListener* m_errorListener = nullptr;
  };

 public:
  /* Options */
  void setDebug(int32_t level);
  bool m_debugPP = false;
  bool m_debugPPResult = false;
  bool m_debugPPTokens = false;
  bool m_debugPPTree = false;
  bool m_debugMacro = false;
  bool m_debugAstModel = false;

  /* To create the preprocessed content */
  void append(std::string_view s);
  void pauseAppend() { m_pauseAppend = true; }
  void resumeAppend() { m_pauseAppend = false; }
  bool isPaused() const { return m_pauseAppend; }

  void addLineTranslationInfo(LineTranslationInfo& info) {
    m_lineTranslationVec.push_back(info);
  }

  /* Shorthand for logging an error */
  void addError(Error& error);

  /* Shorthands for symbol manipulations */
  SymbolId registerSymbol(std::string_view symbol) const;
  SymbolId getId(std::string_view symbol) const;
  std::string_view getSymbol(SymbolId id) const;

  // For recursive macro definition detection
  PreprocessFile* getSourceFile();
  LoopCheck m_loopChecker;

  void setFileContent(FileContent* content) { m_fileContent = content; }
  FileContent* getFileContent() const { return m_fileContent; }

  void setVerilogVersion(VerilogVersion version) { m_verilogVersion = version; }
  VerilogVersion getVerilogVersion() const { return m_verilogVersion; }

  // For cache processing
  void saveCache();
  void collectIncludedFiles(std::set<PreprocessFile*>& included);
  bool usingCachedVersion() const { return m_usingCachedVersion; }
  std::string getProfileInfo() const { return m_profileInfo; }
  std::vector<LineTranslationInfo>& getLineTranslationInfo() {
    return m_lineTranslationVec;
  }
  const std::vector<LineTranslationInfo>& getLineTranslationInfo() const {
    return m_lineTranslationVec;
  }

 private:
  std::tuple<bool, std::string, std::vector<LineColumn>, LineColumn>
  evaluateMacro_(std::string_view name, std::vector<std::string>& arguments,
                 PreprocessFile* callingFile, uint32_t callingLine,
                 LoopCheck& loopChecker, MacroInfo* macroInfo,
                 SpecialInstructions& instructions,
                 PathId embeddedMacroCallFile, uint32_t embeddedMacroCallLine,
                 uint16_t embeddedMacroCallColumn);

  void checkMacroArguments_(std::string_view name, uint32_t line,
                            uint16_t column,
                            const std::vector<std::string>& arguments,
                            const std::vector<std::string>& tokens);
  void forgetPreprocessor_(PreprocessFile*, PreprocessFile* pp);

  Session* const m_session = nullptr;
  PathId m_fileId;
  SymbolId m_macroId;
  Library* m_library = nullptr;
  std::string m_result;
  std::string m_macroBody;
  PreprocessFile* m_includer = nullptr;
  uint32_t m_includerLine = 0;
  std::vector<PreprocessFile*> m_includes;
  CompileSourceFile* m_compileSourceFile = nullptr;
  size_t m_lineCount = 0;
  AntlrParserHandler* m_antlrParserHandler = nullptr;

 public:
  SpecialInstructions m_instructions;
  SV3_1aPpParserBaseListener* m_listener = nullptr;

 private:
  static IncludeFileInfo s_badIncludeFileInfo;

  /* Only used when preprocessing a macro content */
  MacroInfo* m_macroInfo = nullptr;
  MacroStorage m_macros;
  CompilationUnit* m_compilationUnit = nullptr;
  std::vector<LineTranslationInfo> m_lineTranslationVec;
  bool m_pauseAppend = false;
  bool m_usingCachedVersion = false;
  std::vector<IncludeFileInfo> m_includeFileInfo;
  PathId m_embeddedMacroCallFile;
  uint32_t m_embeddedMacroCallLine = 0;
  uint16_t m_embeddedMacroCallColumn = 0;
  std::string m_profileInfo;
  FileContent* m_fileContent = nullptr;
  VerilogVersion m_verilogVersion = VerilogVersion::NoVersion;
};

};  // namespace SURELOG

#endif /* SURELOG_PREPROCESSFILE_H */
