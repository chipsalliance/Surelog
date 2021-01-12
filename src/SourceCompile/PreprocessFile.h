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

#ifndef PREPROCESSFILE_H
#define PREPROCESSFILE_H
#include <string>
#include <vector>
#include <map>
#include <set>
#include <stack>

#include "parser/SV3_1aPpLexer.h"
#include "parser/SV3_1aPpParser.h"
#include "SourceCompile/CompilationUnit.h"
#include "Library/Library.h"
#include "SourceCompile/LoopCheck.h"
#include "SourceCompile/IncludeFileInfo.h"

namespace SURELOG {

class SV3_1aPpTreeShapeListener;
class CompileSourceFile;
class FileContent;

#define LINE1 1

enum VerilogVersion {
    NoVersion,
    Verilog1995,
    Verilog2001,
    Verilog2005,
    Verilog2009,
    SystemVerilog
};


/* Can be either an include file or a macro definition being evaluated */
class PreprocessFile {
 public:
  class SpecialInstructions;
  class DescriptiveErrorListener;

  /* Constructors */
  PreprocessFile(SymbolId fileId, CompileSourceFile* csf,
                 SpecialInstructions& instructions,
                 CompilationUnit* compilationUnit, Library* library);
  PreprocessFile(SymbolId fileId, PreprocessFile* includedIn,
                 unsigned int includerLine, CompileSourceFile* csf,
                 SpecialInstructions& instructions,
                 CompilationUnit* compilationUnit, Library* library,
                 std::string macroBody = "", MacroInfo* = NULL,
                 unsigned int embeddedMacroCallLine = 0,
                 SymbolId embeddedMacroCallFile = 0);
  PreprocessFile(const PreprocessFile& orig);
  virtual ~PreprocessFile();

  /* Main function */
  bool preprocess();
  std::string getPreProcessedFileContent();

  /* Macro manipulations */
  void recordMacro(const std::string name, unsigned int line,
                   unsigned short int column,
                   const std::string formal_arguments,
                   const std::vector<std::string> body);
  void recordMacro(const std::string name, unsigned int line,
                   unsigned short int column,
                   const std::vector<std::string> formal_arguments,
                   const std::vector<std::string> body);
  std::string getMacro(const std::string name,
                       std::vector<std::string>& actual_arguments,
                       PreprocessFile* callingFile, unsigned int callingLine,
                       LoopCheck& loopChecker,
                       SpecialInstructions& instructions,
                       unsigned int embeddedMacroCallLine = 0,
                       SymbolId embeddedMacroCallFile = 0);
  bool deleteMacro(const std::string name, std::set<PreprocessFile*>& visited);
  void undefineAllMacros(std::set<PreprocessFile*>& visited);
  bool isMacroBody() { return !m_macroBody.empty(); }
  std::string getMacroBody() { return m_macroBody; }
  MacroInfo* getMacroInfo() { return m_macroInfo; }
  SymbolId getMacroSignature();
  const MacroStorage& getMacros() { return m_macros; }
  MacroInfo* getMacro(const std::string name);

  const std::string getFileName(unsigned int line);

  std::string reportIncludeInfo();

  CompileSourceFile* getCompileSourceFile() { return m_compileSourceFile; }
  CompilationUnit* getCompilationUnit() { return m_compilationUnit; }
  Library* getLibrary() { return m_library; }
  antlr4::CommonTokenStream* getTokenStream() {
    return m_antlrParserHandler ? m_antlrParserHandler->m_pptokens : NULL;
  }

  SymbolId getFileId(unsigned int line);
  SymbolId getIncluderFileId(unsigned int line);
  SymbolId getRawFileId() { return m_fileId; }
  unsigned int getLineNb(unsigned int line);
  PreprocessFile* getIncluder() { return m_includer; }
  unsigned int getIncluderLine() { return m_includerLine; }
  unsigned int getLineCount() { return m_lineCount; }
  void setLineCount(unsigned int count) { m_lineCount = count; }
  unsigned int getSumLineCount();
  std::vector<IncludeFileInfo>& getIncludeFileInfo() {
    return m_includeFileInfo;
  }
  IncludeFileInfo& getIncludeFileInfo(int index) {
    if (index >= 0 && index < ((int)m_includeFileInfo.size()))
      return m_includeFileInfo[index];
    else
      return m_badIncludeFileInfo;
  }
  unsigned int getEmbeddedMacroCallLine() { return m_embeddedMacroCallLine; }
  SymbolId getEmbeddedMacroCallFile() { return m_embeddedMacroCallFile; }

  /* Markings */
  static std::string MacroNotDefined;
  static std::string PP__Line__Marking;
  static std::string PP__File__Marking;

 private:
  SymbolId m_fileId;
  Library* m_library;
  std::string m_result;
  std::string m_macroBody;
  PreprocessFile* m_includer;
  unsigned int m_includerLine;
  std::vector<PreprocessFile*> m_includes;
  CompileSourceFile* m_compileSourceFile;
  unsigned int m_lineCount;
  IncludeFileInfo m_badIncludeFileInfo;

 public:
  /* Instructions passed from calling scope */
  class SpecialInstructions {
   public:
    enum TraceInstr : bool { Mute = true, DontMute = false };
    enum EmptyMacroInstr : bool { Mark = true, DontMark = false };
    enum FileLineInfoInstr : bool { Filter = true, DontFilter = false };
    enum CheckLoopInstr : bool { CheckLoop = true, DontCheckLoop = false };
    enum AsIsUndefinedMacroInstr : bool {
      AsIsUndefinedMacro = true,
      ComplainUndefinedMacro = false
    };
    enum EvaluateInstr : bool { Evaluate = true, DontEvaluate = false };
    SpecialInstructions()
        : m_mute(DontMute),
          m_mark_empty_macro(DontMark),
          m_filterFileLine(DontFilter),
          m_check_macro_loop(DontCheckLoop),
          m_as_is_undefined_macro(ComplainUndefinedMacro),
          m_evaluate(Evaluate){}
    SpecialInstructions(SpecialInstructions& rhs)
        : m_mute(rhs.m_mute),
          m_mark_empty_macro(rhs.m_mark_empty_macro),
          m_filterFileLine(rhs.m_filterFileLine),
          m_check_macro_loop(rhs.m_check_macro_loop),
          m_as_is_undefined_macro(rhs.m_as_is_undefined_macro),
          m_evaluate(rhs.m_evaluate) {}
    SpecialInstructions(TraceInstr mute, EmptyMacroInstr mark_empty_macro,
                        FileLineInfoInstr filterFileLine,
                        CheckLoopInstr check_macro_loop,
                        AsIsUndefinedMacroInstr as_is_undefined_macro,
                        EvaluateInstr evalaute = Evaluate)
        : m_mute(mute),
          m_mark_empty_macro(mark_empty_macro),
          m_filterFileLine(filterFileLine),
          m_check_macro_loop(check_macro_loop),
          m_as_is_undefined_macro(as_is_undefined_macro),
          m_evaluate(evalaute) {}
    void print() {
      std::cout << "Trace:" << (m_mute ? "Mute" : "DontMute")
                << ", EmptyMacro:" << (m_mark_empty_macro ? "Mark" : "DontMark")
                << ", FileLineInfo:"
                << (m_filterFileLine ? "Filter " : "DontFilter")
                << ", CheckLoop:"
                << (m_check_macro_loop ? "CheckLoop" : "DontCheckLoop")
                << ", AsIsUndefMacro:"
                << (m_as_is_undefined_macro ? "AsIsUndefinedMacro"
                                            : "ComplainUndefinedMacro")
                << ", Evaluate:"
                << (m_evaluate ? "Evaluate" : "DontEvaluate")
                << std::endl;
    };
    TraceInstr        m_mute;
    EmptyMacroInstr   m_mark_empty_macro;
    FileLineInfoInstr m_filterFileLine;
    CheckLoopInstr    m_check_macro_loop;
    AsIsUndefinedMacroInstr m_as_is_undefined_macro;
    EvaluateInstr     m_evaluate;
  };

  std::string evaluateMacroInstance(
      const std::string macro_instance, PreprocessFile* callingFile,
      unsigned int callingLine,
      SpecialInstructions::CheckLoopInstr checkMacroLoop,
      SpecialInstructions::AsIsUndefinedMacroInstr);

  /* Incoming `line handling */
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

  /* `ifdef, `ifndef, `elsif, `else Stack */
  class IfElseItem {
   public:
    enum Type { IFDEF, IFNDEF, ELSIF, ELSE };
    std::string m_macroName;
    bool m_defined;
    Type m_type;
    bool m_previousActiveState;
  };
  typedef std::vector<IfElseItem> IfElseStack;
  IfElseStack m_ifStack;
  IfElseStack& getStack();

  /* Antlr parser container */
  class AntlrParserHandler {
   public:
    AntlrParserHandler()
        : m_inputStream(NULL),
          m_pplexer(NULL),
          m_pptokens(NULL),
          m_ppparser(NULL),
          m_pptree(NULL) {}
    ~AntlrParserHandler();
    antlr4::ANTLRInputStream* m_inputStream;
    SV3_1aPpLexer* m_pplexer;
    antlr4::CommonTokenStream* m_pptokens;
    SV3_1aPpParser* m_ppparser;
    antlr4::tree::ParseTree* m_pptree;
    DescriptiveErrorListener* m_errorListener;
  };
  SV3_1aPpTreeShapeListener* m_listener;

 public:
  /* Options */
  void setDebug(int level);
  bool m_debugPP;
  bool m_debugPPResult;
  bool m_debugPPTokens;
  bool m_debugPPTree;
  bool m_debugMacro;
  bool m_debugAstModel;

  SpecialInstructions m_instructions;

  /* To create the preprocessed content */
  void append(const std::string& s);
  void pauseAppend() { m_pauseAppend = true; }
  void resumeAppend() { m_pauseAppend = false; }

  void addLineTranslationInfo(LineTranslationInfo& info) {
    m_lineTranslationVec.push_back(info);
  }

  /* Shorthand for logging an error */
  void addError(Error& error);

  /* Shorthands for symbol manipulations */
  SymbolId registerSymbol(const std::string symbol);
  SymbolId getId(const std::string symbol);
  const std::string getSymbol(SymbolId id);

  // For recursive macro definition detection
  PreprocessFile* getSourceFile();
  LoopCheck m_loopChecker;

  void setFileContent(FileContent* content) { m_fileContent = content; }
  FileContent* getFileContent() { return m_fileContent; }

  void setVerilogVersion(VerilogVersion version) { m_verilogVersion = version; }
  VerilogVersion getVerilogVersion() { return m_verilogVersion; }

  // For cache processing
  void saveCache();
  void collectIncludedFiles(std::set<PreprocessFile*>& included);
  bool usingCachedVersion() { return m_usingCachedVersion; }
  std::string getProfileInfo() { return m_profileInfo; }
  std::vector<LineTranslationInfo>& getLineTranslationInfo() { return m_lineTranslationVec; }
 private:
  std::pair<bool, std::string> evaluateMacro_(
      const std::string name, std::vector<std::string>& arguments,
      PreprocessFile* callingFile, unsigned int callingLine,
      LoopCheck& loopChecker, MacroInfo* macroInfo,
      SpecialInstructions& instructions, unsigned int embeddedMacroCallLine,
      SymbolId embeddedMacroCallFile);

  void checkMacroArguments_(const std::string& name, unsigned int line,
                            unsigned short column,
                            const std::vector<std::string>& arguments,
                            const std::vector<std::string>& tokens);
  void forgetPreprocessor_(PreprocessFile*, PreprocessFile* pp);
  AntlrParserHandler* m_antlrParserHandler;

  MacroInfo* m_macroInfo; /* Only used when preprocessing a macro content */
  MacroStorage m_macros;

  CompilationUnit* m_compilationUnit;
  std::vector<LineTranslationInfo> m_lineTranslationVec;
  bool m_pauseAppend;
  bool m_usingCachedVersion;
  std::vector<IncludeFileInfo> m_includeFileInfo;
  unsigned int m_embeddedMacroCallLine;
  SymbolId m_embeddedMacroCallFile;
  std::string m_profileInfo;
  FileContent* m_fileContent;
  VerilogVersion m_verilogVersion;
};

};  // namespace SURELOG

#endif /* PREPROCESSFILE_H */
