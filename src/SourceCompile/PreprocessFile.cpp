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
 * File:   PreprocessFile.cpp
 * Author: alain
 *
 * Created on February 24, 2017, 9:38 PM
 */
#include "SourceCompile/SymbolTable.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "Utils/StringUtils.h"
#include "Cache/PPCache.h"
#include "ErrorReporting/Waiver.h"
#include <cstdlib>
#include <iostream>
#include <regex>
#include <algorithm>
#include <cctype>

using namespace std;
using namespace SURELOG;

#include "parser/SV3_1aPpLexer.h"
#include "parser/SV3_1aPpParser.h"
#include "parser/SV3_1aPpParserBaseListener.h"
using namespace antlr4;
#include "Utils/ParseUtils.h"
#include "Utils/FileUtils.h"
#include "antlr4-runtime.h"
#include "atn/ParserATNSimulator.h"
#include "Parser.h"
#include "SourceCompile/SV3_1aPpTreeShapeListener.h"
#include "Utils/Timer.h"
#include "Package/Precompiled.h"

std::string PreprocessFile::MacroNotDefined = "SURELOG_MACRO_NOT_DEFINED";
std::string PreprocessFile::PP__Line__Marking = "SURELOG__LINE__MARKING";
std::string PreprocessFile::PP__File__Marking = "SURELOG__FILE__MARKING";

void PreprocessFile::setDebug(int level) {
  switch (level) {
    case 0:
      m_debugPP = false;
      m_debugPPResult = false;
      m_debugPPTokens = false;
      m_debugPPTree = false;
      m_debugMacro = false;
      m_debugAstModel = false;
      break;
    case 1:
      m_debugPP = false;
      m_debugPPResult = false;
      m_debugPPTokens = false;
      m_debugPPTree = false;
      m_debugMacro = false;
      m_debugAstModel = true;
      break;
    case 2:
      m_debugPP = true;
      m_debugPPResult = false;
      m_debugPPTokens = false;
      m_debugPPTree = false;
      m_debugMacro = true;
      break;
    case 3:
      m_debugPP = true;
      m_debugPPResult = false;
      m_debugPPTokens = true;
      m_debugPPTree = true;
      m_debugMacro = false;
      break;
    case 4:
      m_debugPP = true;
      m_debugPPResult = true;
      m_debugPPTokens = false;
      m_debugPPTree = false;
      m_debugMacro = true;
      break;
    case 5:
      m_debugPP = true;
      m_debugPPResult = true;
      m_debugPPTokens = true;
      m_debugPPTree = true;
      m_debugMacro = true;
      break;
    default:
      break;
  }
}
class PreprocessFile::DescriptiveErrorListener : public ANTLRErrorListener {
 public:
  DescriptiveErrorListener(PreprocessFile* pp, std::string filename)
      : m_pp(pp), m_fileName(filename) {}

  void syntaxError(Recognizer* recognizer, Token* offendingSymbol, size_t line,
                   size_t charPositionInLine, const std::string& msg,
                   std::exception_ptr e) override;

  void reportAmbiguity(Parser* recognizer, const dfa::DFA& dfa,
                       size_t startIndex, size_t stopIndex, bool exact,
                       const antlrcpp::BitSet& ambigAlts,
                       atn::ATNConfigSet* configs) override;

  void reportAttemptingFullContext(Parser* recognizer, const dfa::DFA& dfa,
                                   size_t startIndex, size_t stopIndex,
                                   const antlrcpp::BitSet& conflictingAlts,
                                   atn::ATNConfigSet* configs) override;

  void reportContextSensitivity(Parser* recognizer, const dfa::DFA& dfa,
                                size_t startIndex, size_t stopIndex,
                                size_t prediction, atn::ATNConfigSet* configs) override;

  PreprocessFile* m_pp;
  std::string m_fileName;
  std::string m_fileContent;
};

void PreprocessFile::DescriptiveErrorListener::syntaxError(
    Recognizer* recognizer, Token* offendingSymbol, size_t line,
    size_t charPositionInLine, const std::string& msg, std::exception_ptr e) {
  SymbolId msgId = m_pp->registerSymbol(msg);

  if (m_pp->m_macroInfo) {
    std::string lineText = m_pp->getMacroBody();
    for (unsigned int i = 0; i < charPositionInLine; i++) lineText += " ";
    lineText += "^-- " + m_fileName + ":" + std::to_string(line) +
                ":" + std::to_string(charPositionInLine) + ":";
    msgId = m_pp->registerSymbol(msg + "," + lineText);
    Location loc(m_pp->getMacroInfo()->m_file,
                 m_pp->getMacroInfo()->m_line + line - 1, charPositionInLine,
                 msgId);
    Location extraLoc(m_pp->getIncluderFileId(m_pp->getIncluderLine()),
                      m_pp->getIncluderLine(), 0, 0);
    Error err(ErrorDefinition::PP_MACRO_SYNTAX_ERROR, loc, extraLoc);
    m_pp->addError(err);
  } else {
    if (m_fileContent.empty()) {
      m_fileContent = FileUtils::getFileContent(m_fileName);
    }

    std::string lineText;
    if (!m_fileContent.empty()) {
      lineText = StringUtils::getLineInString(m_fileContent, line);
      if (!lineText.empty()) {
        if (!strstr(lineText.c_str(), "\n")) {
          lineText += "\n";
        }
        for (unsigned int i = 0; i < charPositionInLine; i++) lineText += " ";
        lineText += "^-- " + m_fileName + ":" + std::to_string(line) +
                    ":" + std::to_string(charPositionInLine) + ":";
      }
    }

    Location loc2(0, 0, 0, m_pp->registerSymbol(lineText));

    Location loc(m_pp->getFileId(line), line, charPositionInLine, msgId);
    Error err(ErrorDefinition::PP_SYNTAX_ERROR, loc, loc2);
    m_pp->addError(err);
  }
}

void PreprocessFile::DescriptiveErrorListener::reportAmbiguity(
    Parser* recognizer, const dfa::DFA& dfa, size_t startIndex,
    size_t stopIndex, bool exact, const antlrcpp::BitSet& ambigAlts,
    atn::ATNConfigSet* configs) {}

void PreprocessFile::DescriptiveErrorListener::reportAttemptingFullContext(
    Parser* recognizer, const dfa::DFA& dfa, size_t startIndex,
    size_t stopIndex, const antlrcpp::BitSet& conflictingAlts,
    atn::ATNConfigSet* configs) {}

void PreprocessFile::DescriptiveErrorListener::reportContextSensitivity(
    Parser* recognizer, const dfa::DFA& dfa, size_t startIndex,
    size_t stopIndex, size_t prediction, atn::ATNConfigSet* configs) {}

PreprocessFile::PreprocessFile(SymbolId fileId, CompileSourceFile* csf,
                               SpecialInstructions& instructions,
                               CompilationUnit* comp_unit, Library* library)
    : m_fileId(fileId),
      m_library(library),
      m_result(""),
      m_macroBody(""),
      m_includer(NULL),
      m_includerLine(0),
      m_compileSourceFile(csf),
      m_lineCount(0),
      m_listener(NULL),
      m_instructions(instructions),
      m_antlrParserHandler(NULL),
      m_macroInfo(NULL),
      m_compilationUnit(comp_unit),
      m_pauseAppend(false),
      m_usingCachedVersion(false),
      m_embeddedMacroCallLine(0),
      m_embeddedMacroCallFile(0),
      m_fileContent(NULL),
      m_verilogVersion(VerilogVersion::NoVersion) {
  setDebug(m_compileSourceFile->m_commandLineParser->getDebugLevel());
  IncludeFileInfo info(0, m_fileId, 0, 2);
  info.m_indexClosing = 0;
  info.m_indexOpening = 0;
  getIncludeFileInfo().push_back(info);
}

PreprocessFile::PreprocessFile(SymbolId fileId, PreprocessFile* includedIn,
                               unsigned int includerLine,
                               CompileSourceFile* csf,
                               SpecialInstructions& instructions,
                               CompilationUnit* comp_unit, Library* library,
                               std::string macroBody, MacroInfo* macroInfo,
                               unsigned int embeddedMacroCallLine,
                               SymbolId embeddedMacroCallFile)
    : m_fileId(fileId),
      m_library(library),
      m_result(""),
      m_macroBody(macroBody),
      m_compileSourceFile(csf),
      m_lineCount(0),
      m_listener(NULL),
      m_instructions(instructions),
      m_antlrParserHandler(NULL),
      m_macroInfo(macroInfo),
      m_compilationUnit(comp_unit),
      m_pauseAppend(false),
      m_usingCachedVersion(false),
      m_embeddedMacroCallLine(embeddedMacroCallLine),
      m_embeddedMacroCallFile(embeddedMacroCallFile),
      m_fileContent(NULL),
      m_verilogVersion(VerilogVersion::NoVersion){
  setDebug(m_compileSourceFile->m_commandLineParser->getDebugLevel());
  m_includer = includedIn;
  m_includerLine = includerLine;
  if (includedIn) {
    includedIn->m_includes.push_back(this);
  }
}

void PreprocessFile::addError(Error& error) {
  if (!m_instructions.m_mute)
    getCompileSourceFile()->getErrorContainer()->addError(error);
}

const std::string PreprocessFile::getSymbol(SymbolId id) {
  return getCompileSourceFile()->getSymbolTable()->getSymbol(id);
}

const std::string PreprocessFile::getFileName(unsigned int line) {
  return getSymbol(getFileId(line));
}

SymbolId PreprocessFile::getMacroSignature() {
  std::string macroSignature = getSymbol(m_fileId);
  if (m_macroInfo) {
    macroSignature += "|" + getSymbol(m_macroInfo->m_file);
    macroSignature += "|" + std::to_string(m_macroInfo->m_line);
  }
  macroSignature += "|" + m_macroBody;
  SymbolId sigId = registerSymbol(macroSignature);
  return sigId;
}

PreprocessFile::PreprocessFile(const PreprocessFile& orig) {}

PreprocessFile::~PreprocessFile() {
  if (m_listener) delete m_listener;
}

PreprocessFile::AntlrParserHandler::~AntlrParserHandler() {
  delete m_errorListener;
  // delete m_pptree;  // INVALID MEMORY READ can be seen in AdvancedDebug
  delete m_ppparser;
  delete m_pptokens;
  delete m_pplexer;
  delete m_inputStream;
}

bool PreprocessFile::preprocess() {
  m_result = "";
  std::string fileName = getSymbol(m_fileId);
  Precompiled* prec = Precompiled::getSingleton();
  std::string root = FileUtils::basename(fileName);
  bool precompiled = false;
  if (prec->isFilePrecompiled(root)) precompiled = true;

  Timer tmr;
  PPCache cache(this);
  if (cache.restore()) {
    m_usingCachedVersion = true;
    getCompilationUnit()->setCurrentTimeInfo(getFileId(0));
    if (m_debugAstModel && !precompiled)
      std::cout << m_fileContent->printObjects();
    if (precompiled)
      return true;
  }
  if (getCompileSourceFile()->getCommandLineParser()->parseOnly())
    return true;

  m_antlrParserHandler = getCompileSourceFile()->getAntlrPpHandlerForId(
    (m_macroBody.empty()) ? m_fileId : getMacroSignature());

  if (m_antlrParserHandler == NULL) {
    m_antlrParserHandler = new AntlrParserHandler();
    if (!m_macroBody.empty()) {
      if (m_debugPP) {
        std::cout << "PP PREPROCESS MACRO: " << m_macroBody << endl;
      }
      m_antlrParserHandler->m_inputStream = new ANTLRInputStream(m_macroBody);
    } else {
      if (m_debugPP) std::cout << "PP PREPROCESS FILE: " << fileName << endl;
      std::ifstream stream;
      stream.open(fileName);
      if (!stream.good()) {
        if (m_includer == NULL) {
          Location loc(m_fileId);
          Error err(ErrorDefinition::PP_CANNOT_OPEN_FILE, loc);
          addError(err);
        } else {
          Location includeFile(m_includer->m_fileId, m_includerLine, 0,
                               m_fileId);
          Error err(ErrorDefinition::PP_CANNOT_OPEN_INCLUDE_FILE, includeFile);
          addError(err);
        }
        return false;
      }
      // Remove ^M (DOS) from text file
      std::string text;
      char c = stream.get();
      while (stream.good()) {
        if (c != 0x0D)
          text+=c;
        c = stream.get();
      }
      stream.close();

      try {
        m_antlrParserHandler->m_inputStream = new ANTLRInputStream(text);
      } catch (...) {
        Location loc(0);
        if (m_includer == NULL) {
          Location file(m_fileId);
          loc = file;
        } else {
          Location includeFile(m_includer->m_fileId, m_includerLine, 0,
                               m_fileId);
          loc = includeFile;
        }
        Error err(ErrorDefinition::PP_CANNOT_READ_FILE_CONTENT, loc);
        addError(err);
        return false;
      }
    }
    m_antlrParserHandler->m_errorListener =
        new PreprocessFile::DescriptiveErrorListener(
          this, (m_macroBody.empty()) ? fileName : "in macro " + fileName);
    m_antlrParserHandler->m_pplexer =
        new SV3_1aPpLexer(m_antlrParserHandler->m_inputStream);
    m_antlrParserHandler->m_pplexer->removeErrorListeners();
    m_antlrParserHandler->m_pplexer->addErrorListener(
        m_antlrParserHandler->m_errorListener);
    m_antlrParserHandler->m_pptokens =
        new CommonTokenStream(m_antlrParserHandler->m_pplexer);
    m_antlrParserHandler->m_pptokens->fill();

    if (getCompileSourceFile()->getCommandLineParser()->profile()) {
      // m_profileInfo += "Tokenizer: " + std::to_string (tmr.elapsed_rounded ())
      // + " " + fileName + "\n";
      tmr.reset();
    }

    if (m_debugPPTokens) {
      std::cout << "PP TOKENS: " << std::endl;
      for (auto token : m_antlrParserHandler->m_pptokens->getTokens()) {
        std::cout << token->toString() << std::endl;
      }
    }

    m_antlrParserHandler->m_ppparser =
        new SV3_1aPpParser(m_antlrParserHandler->m_pptokens);
    m_antlrParserHandler->m_ppparser->getInterpreter<atn::ParserATNSimulator>()
        ->setPredictionMode(atn::PredictionMode::SLL);
    m_antlrParserHandler->m_ppparser->removeErrorListeners();
    m_antlrParserHandler->m_ppparser->setErrorHandler(
        std::make_shared<BailErrorStrategy>());
    try {
      m_antlrParserHandler->m_pptree =
          m_antlrParserHandler->m_ppparser->top_level_rule();

      if (getCompileSourceFile()->getCommandLineParser()->profile()) {
        m_profileInfo +=
                "PP SSL Parsing: " + StringUtils::to_string(tmr.elapsed_rounded()) +
                "s " + fileName + "\n";
        tmr.reset();
      }

    } catch (ParseCancellationException& pex) {
      m_antlrParserHandler->m_pptokens->reset();
      m_antlrParserHandler->m_ppparser->reset();
      m_antlrParserHandler->m_ppparser->addErrorListener(
          m_antlrParserHandler->m_errorListener);
      m_antlrParserHandler->m_ppparser->setErrorHandler(
          std::make_shared<DefaultErrorStrategy>());
      m_antlrParserHandler->m_ppparser
          ->getInterpreter<atn::ParserATNSimulator>()
          ->setPredictionMode(atn::PredictionMode::LL);
      m_antlrParserHandler->m_pptree =
          m_antlrParserHandler->m_ppparser->top_level_rule();

      if (getCompileSourceFile()->getCommandLineParser()->profile()) {
        m_profileInfo +=
                "PP LL  Parsing: " + StringUtils::to_string(tmr.elapsed_rounded()) +
                " " + fileName + "\n";
        tmr.reset();
      }
    }

  if (m_debugPPTree)
      std::cout << "PP TREE: "
                << m_antlrParserHandler->m_pptree->toStringTree(
                       m_antlrParserHandler->m_ppparser)
                << std::endl
                << std::endl;

    getCompileSourceFile()->registerAntlrPpHandlerForId(
      (m_macroBody.empty()) ? m_fileId : getMacroSignature(),
      m_antlrParserHandler);
  }
  m_result = "";
  if (m_listener != NULL)
    delete m_listener;
  m_listener = new SV3_1aPpTreeShapeListener(this,
            m_antlrParserHandler->m_pptokens,
            m_instructions);
  tree::ParseTreeWalker::DEFAULT.walk(m_listener,
                                      m_antlrParserHandler->m_pptree);
  if (m_debugAstModel && !precompiled)
     std::cout << m_fileContent->printObjects();

  return true;
}

static unsigned int LinesCount(const std::string& s) {
  return std::count(s.begin(), s.end(), '\n');
}

unsigned int PreprocessFile::getSumLineCount() {
  unsigned int total = LinesCount(m_result);
  if (m_includer) 
    total += m_includer->getSumLineCount();
  return total;
}

void PreprocessFile::append(const std::string& s) {
  if (!m_pauseAppend) {
    m_lineCount += LinesCount(s);
    m_result += s;
  }
}

void PreprocessFile::recordMacro(const std::string name, unsigned int line,
                                 unsigned short int column,
                                 const std::string arguments,
                                 const std::vector<std::string> tokens) {
  // *** Argument processing
  std::string arguments_short = arguments;
  // Remove (
  size_t p = arguments_short.find('(');
  if (p != string::npos) {
    arguments_short.erase(p, 1);
  }
  // Remove )
  p = arguments_short.find(')');
  if (p != string::npos) {
    arguments_short.erase(p, 1);
  }
  // Tokenize args
  std::vector<std::string> args;
  StringUtils::tokenize(arguments_short, ",", args);

  if (m_debugMacro) {
    std::string body;
    for (auto token : tokens) {
      body += token;
    }
    std::cout << "PP RECORDING MACRO: " << name << ": | " << body << " | "
              << endl;
  }

  // std::cout << "PP RECORDING MACRO: " << name  << ", FILE: " <<
  // getSymbol(getFileId(line)) << "" << endl;

  MacroInfo* macroInfo = new MacroInfo(
      name, arguments.size() ? MacroInfo::WITH_ARGS : MacroInfo::NO_ARGS,
      getFileId(line), line, column, args, tokens);
  m_macros.insert(std::make_pair(name, macroInfo));
  m_compilationUnit->registerMacroInfo(name, macroInfo);
  checkMacroArguments_(name, line, column, args, tokens);
}

std::string PreprocessFile::reportIncludeInfo() {
  std::string report;
  for (auto info : m_includeFileInfo) {
    std::string type = (info.m_type == 1) ? "in" : "out";
    report += std::to_string(info.m_originalLine) + " " +
              getSymbol(info.m_sectionFile) + " " +
              std::to_string(info.m_sectionStartLine) + " " + type + "\n";
  }

  return report;
}

void PreprocessFile::recordMacro(const std::string name, unsigned int line,
                                 unsigned short int column,
                                 const std::vector<std::string> arguments,
                                 const std::vector<std::string> tokens) {
  MacroInfo* macroInfo = new MacroInfo(
      name, arguments.size() ? MacroInfo::WITH_ARGS : MacroInfo::NO_ARGS,
      getFileId(line), line, column, arguments, tokens);
  m_macros.insert(std::make_pair(name, macroInfo));
  m_compilationUnit->registerMacroInfo(name, macroInfo);
}

void PreprocessFile::checkMacroArguments_(
    const std::string& name, unsigned int line, unsigned short column,
    const std::vector<std::string>& arguments,
    const std::vector<std::string>& tokens) {
  std::set<std::string> argSet;
  std::set<std::string> tokenSet;
  for (auto s : arguments) {
    argSet.insert(
        StringUtils::trim(StringUtils::rtrimEqual(StringUtils::trim(s))));
  }
  for (auto s : tokens) {
    tokenSet.insert(StringUtils::trim(s));
  }
  for (auto s : argSet) {
    if (tokenSet.find(s) == tokenSet.end() &&
        tokenSet.find("``" + s + "``") == tokenSet.end() &&
        tokenSet.find(s + "``") == tokenSet.end()) {
      Location loc(m_fileId, line, column, registerSymbol(s));
      Error err(ErrorDefinition::PP_MACRO_UNUSED_ARGUMENT, loc);
      addError(err);
    }
  }
  for (unsigned int i = 0; i < tokens.size(); i++) {
    std::string s1 = tokens[i];
    std::string s2 = tokens[i];
    bool check = false;
    if ((s1.find("``") != std::string::npos) && (s1 != "``"))  // ``a``
    {
      s1 = std::regex_replace(s1, std::regex("``"), "");
      s2 = s1;
      check = true;
    } else if (s1 == "``") {
      if (i > 0) s1 = tokens[i - 1];
      s1 = StringUtils::trim(s1);
      s2 = tokens[i + 1];
      s2 = StringUtils::trim(s2);
      check = true;
    }
    if (check) {
      if ((argSet.find(s1) == argSet.end()) &&
          (argSet.find(s2) == argSet.end())) {
        for (auto s : {s1, s2}) {
          if (argSet.find(s) == argSet.end()) {
            if (s.find("`") != std::string::npos) continue;
            if (s.find("//") != std::string::npos) continue;
            if (!std::isalpha(s[0])) continue;
            Location loc(m_fileId, line, column, registerSymbol(s));
            Error err(ErrorDefinition::PP_MACRO_UNDEFINED_ARGUMENT, loc);
            addError(err);
          }
        }
      }
    }
  }
}

SymbolId PreprocessFile::getIncluderFileId(unsigned int line) {
  PreprocessFile* tmp = this;
  while (tmp->m_includer != NULL) {
    tmp = tmp->m_includer;
  }
  return tmp->getFileId(line);
}

PreprocessFile* PreprocessFile::getSourceFile() {
  PreprocessFile* tmp = this;
  while (tmp->m_includer != NULL) {
    tmp = tmp->m_includer;
  }
  return tmp;
}

void PreprocessFile::forgetPreprocessor_(PreprocessFile* inc,
                                         PreprocessFile* pp) {
  for (std::vector<PreprocessFile*>::iterator itr = inc->m_includes.begin();
       itr != inc->m_includes.end(); itr++) {
    if ((*itr) == pp) {
      inc->m_includes.erase(itr);
      break;
    }
  }
}

SymbolId PreprocessFile::registerSymbol(const std::string symbol) {
  return getCompileSourceFile()->getSymbolTable()->registerSymbol(symbol);
}

SymbolId PreprocessFile::getId(const std::string symbol) {
  return getCompileSourceFile()->getSymbolTable()->getId(symbol);
}

std::string PreprocessFile::evaluateMacroInstance(
    const std::string macro_instance, PreprocessFile* callingFile,
    unsigned int callingLine,
    SpecialInstructions::CheckLoopInstr checkMacroLoop,
    SpecialInstructions::AsIsUndefinedMacroInstr asisUndefMacro) {
  std::string result;
  // SymbolId macroArgs = registerSymbol (macro_instance);
  SpecialInstructions instructions(
      SpecialInstructions::Mute, SpecialInstructions::Mark,
      SpecialInstructions::Filter, checkMacroLoop, asisUndefMacro);
  PreprocessFile* pp = new PreprocessFile(
      0, /*macroArgs,*/ NULL,
      0 /*m_includer ? m_includer : callingFile, callingLine*/,
      m_compileSourceFile, instructions,
      m_includer ? m_includer->m_compilationUnit
                 : callingFile->m_compilationUnit,
      callingFile->m_library, macro_instance);
  if (!pp->preprocess()) {
    result = MacroNotDefined;
  } else {
    result = pp->getPreProcessedFileContent();
  }
  forgetPreprocessor_(m_includer ? m_includer : callingFile, pp);
  delete pp;
  return result;
}

std::pair<bool, std::string> PreprocessFile::evaluateMacro_(
    const std::string name, std::vector<std::string>& actual_args,
    PreprocessFile* callingFile, unsigned int callingLine,
    LoopCheck& loopChecker, MacroInfo* macroInfo,
    SpecialInstructions& instructions, unsigned int embeddedMacroCallLine,
    SymbolId embeddedMacroCallFile) {
  std::string result;
  bool found = false;
  std::vector<std::string>& formal_args = macroInfo->m_arguments;
  // Don't modify the actual tokens of the macro, make a copy...
  std::vector<std::string> body_tokens = macroInfo->m_tokens;

  if (instructions.m_check_macro_loop) {
    bool loop = loopChecker.addEdge(callingFile->m_fileId, getId(name));
    if (loop) {
      std::vector<SymbolId> loop = loopChecker.reportLoop();
      for (auto id : loop) {
        MacroInfo* macroInfo2 = m_compilationUnit->getMacroInfo(getSymbol(id));
        if (macroInfo2) {
          Location loc(macroInfo2->m_file, macroInfo2->m_line, 0, id);
          Location exloc(macroInfo->m_file, macroInfo->m_line, 0, getId(name));
          Error err(ErrorDefinition::PP_RECURSIVE_MACRO_DEFINITION, loc, exloc);
          addError(err);
          return std::make_pair(false, getCompileSourceFile()
                                           ->getCompiler()
                                           ->getSymbolTable()
                                           ->getBadSymbol());
        }
      }
    }
  }

  StringUtils::replaceInTokenVector(body_tokens, "`\"", "\"");
  StringUtils::replaceInTokenVector(body_tokens, "`\\`\"", "\\\"");

  // argument substitution
  for (unsigned int i = 0; i < actual_args.size(); i++) {
    if (actual_args[i].find('`') != std::string::npos) {
      actual_args[i] = evaluateMacroInstance(
          actual_args[i], callingFile, callingLine,
          SpecialInstructions::CheckLoop,
          SpecialInstructions::AsIsUndefinedMacroInstr::ComplainUndefinedMacro);
    }
  }

  if ((actual_args.size() > formal_args.size() && (!m_instructions.m_mute))) {
    if (formal_args.size() == 0 &&
        (StringUtils::getFirstNonEmptyToken(body_tokens) == "(")) {
      Location loc(macroInfo->m_file, macroInfo->m_line,
                   macroInfo->m_column + name.size() + 1, getId(name));
      Error err(ErrorDefinition::PP_MACRO_HAS_SPACE_BEFORE_ARGS, loc);
      addError(err);
    } else {
      if ((!Waiver::macroArgCheck(name)) && (formal_args.size() > 0)) {
        Location loc(callingFile->getFileId(callingLine),
                     callingFile->getLineNb(callingLine), 0, getId(name));
        Location arg(0, 0, 0,
                     registerSymbol(std::to_string(actual_args.size())));
        Location def(macroInfo->m_file, macroInfo->m_line, 0,
                     registerSymbol(std::to_string(formal_args.size())));
        std::vector<Location> locs = {arg, def};
        Error err(ErrorDefinition::PP_TOO_MANY_ARGS_MACRO, loc, &locs);
        addError(err);
      }
    }
  }

  for (unsigned int i = 0; i < formal_args.size(); i++) {
    std::vector<std::string> formal_arg_default;
    StringUtils::tokenize(formal_args[i], "=", formal_arg_default);
    std::string formal =
        std::regex_replace(formal_arg_default[0], std::regex("[ \t]*"), "");
    bool empty_actual = true;
    if (i < actual_args.size()) {
      for (unsigned int ii = 0; ii < actual_args[i].size(); ii++) {
        if (actual_args[i][ii] != ' ') {
          empty_actual = false;
          break;
        }
      }
    }
    if (!empty_actual) {
      if (actual_args[i] == SymbolTable::getEmptyMacroMarker()) {
        actual_args[i] = "";
      }

      StringUtils::replaceInTokenVector(body_tokens, {"``", formal, "``"},
                                        actual_args[i]);
      StringUtils::replaceInTokenVector(body_tokens, "``" + formal + "``",
                                        actual_args[i]);
      StringUtils::replaceInTokenVector(body_tokens, {formal, "``"},
                                        actual_args[i]);
      StringUtils::replaceInTokenVector(body_tokens, {"``", formal},
                                        actual_args[i]);
      StringUtils::replaceInTokenVector(body_tokens, {formal, " ", "``"},
                                        actual_args[i]);
      StringUtils::replaceInTokenVector(body_tokens, formal + "``",
                                        actual_args[i]);
      StringUtils::replaceInTokenVector(body_tokens, formal, actual_args[i]);
    } else {
      if (formal_arg_default.size() == 2) {
        std::string default_val =
            std::regex_replace(formal_arg_default[1], std::regex("[ \t]*"), "");
        StringUtils::replaceInTokenVector(body_tokens, {"``", formal, "``"},
                                          default_val);
        StringUtils::replaceInTokenVector(body_tokens, "``" + formal + "``",
                                          default_val);
        StringUtils::replaceInTokenVector(body_tokens, {formal, "``"},
                                          default_val);
        StringUtils::replaceInTokenVector(body_tokens, {"``", formal},
                                          default_val);
        StringUtils::replaceInTokenVector(body_tokens, {formal, " ", "``"},
                                          default_val);
        StringUtils::replaceInTokenVector(body_tokens, formal + "``",
                                          default_val);
        StringUtils::replaceInTokenVector(body_tokens, formal, default_val);
      } else {
        StringUtils::replaceInTokenVector(body_tokens, {"``", formal, "``"},
                                          "");
        StringUtils::replaceInTokenVector(body_tokens, "``" + formal + "``",
                                          "");
        StringUtils::replaceInTokenVector(body_tokens, {formal, "``"}, "");
        StringUtils::replaceInTokenVector(body_tokens, {"``", formal}, "");
        StringUtils::replaceInTokenVector(body_tokens, {formal, " ", "``"}, "");
        StringUtils::replaceInTokenVector(body_tokens, formal + "``", "");
        StringUtils::replaceInTokenVector(body_tokens, formal, "");

        if ((int)i > (int)(((int)actual_args.size()) - 1)) {
          if (!instructions.m_mute) {
            Location loc(callingFile->getFileId(callingLine),
                         callingFile->getLineNb(callingLine), 0, getId(name));
            SymbolId id =
                registerSymbol(std::to_string(i + 1) + " (" + formal + ")");
            Location arg(0, 0, 0, id);
            Location def(macroInfo->m_file, macroInfo->m_line, 0, id);
            std::vector<Location> locs = {arg, def};
            Error err(ErrorDefinition::PP_MACRO_NO_DEFAULT_VALUE, loc, &locs);
            addError(err);
          }
        }
      }
    }
  }

  std::string body;
  for (auto token : body_tokens) {
    body += token;
  }
  if (actual_args.size() && (formal_args.size() == 0)) {
    body += "(";
    body += actual_args[0];
    body += ")";
  }
  // *** Body processing
  std::string body_short;
  // Replace \\n by \n
  bool inString = false;
  char c1 = '\0';
  char c2 = '\0';
  for (unsigned int i = 0; i < body.size(); i++) {
    c2 = body[i];
    if (c2 == '"') {
      inString = !inString;
    }
    if ((c1 == '\\') && (c2 == '\n') && (!inString)) {
      body_short.erase(body_short.end()-1);
      body_short.push_back(c2);
    } else {
      body_short.push_back(c2);
    }
    c1 = c2;
  }
  // Truncate trailing carriage returns (up to 2)

  for (int i = 0; i < 2; i++) {
    if (body_short.size()) {
      if (body_short.at(body_short.size() - 1) == '\n') {
        body_short.erase(body_short.size() - 1);
      } else {
        break;
      }
    }
  }

  // If it is a Multiline macro, insert a \n at the end

  if (body_short.find('\n') != string::npos) {
    body_short.push_back('\n');
  }

  if (body_short.find('`') != std::string::npos) {
    // Recursively resolve macro instantiation within the macro
    if (m_debugMacro) {
      const std::string fileName = getSymbol(m_fileId);
      std::cout << "PP BODY EXPANSION FOR " << name << " in : " << fileName
                << std::endl;
      for (auto arg : actual_args) {
        std::cout << "PP ARG: " << arg << "\n";
      }
    }
    SymbolId macroId = registerSymbol(name);
    SpecialInstructions instructions(
        m_instructions.m_mute, SpecialInstructions::DontMark,
        SpecialInstructions::Filter, m_instructions.m_check_macro_loop,
        m_instructions.m_as_is_undefined_macro);
    PreprocessFile* pp = new PreprocessFile(
        macroId, callingFile ? callingFile : m_includer, callingLine,
        m_compileSourceFile, instructions,
        callingFile ? callingFile->m_compilationUnit
                    : m_includer->m_compilationUnit,
        callingFile ? callingFile->m_library : m_includer->m_library,
        body_short, macroInfo, embeddedMacroCallLine, embeddedMacroCallFile);
    getCompileSourceFile()->registerPP(pp);
    if (!pp->preprocess()) {
      result = MacroNotDefined;
    } else {
      std::string pp_result = pp->getPreProcessedFileContent();

      if (callingLine && callingFile && !callingFile->isMacroBody()) {
        pp_result = std::regex_replace(
            pp_result, std::regex(PP__File__Marking),
            "\"" +
                FileUtils::getFullPath(callingFile->getFileName(callingLine)) +
                "\"");
        pp_result = std::regex_replace(pp_result, std::regex(PP__Line__Marking),
                                       std::to_string(callingLine));
      }
      result = pp_result;
      found = true;
    }
  } else {
    result = body_short;
    found = true;
  }
  return std::make_pair(found, result);
}

MacroInfo* PreprocessFile::getMacro(const std::string name) {
  registerSymbol(name);
  return m_compilationUnit->getMacroInfo(name);
}

bool PreprocessFile::deleteMacro(const std::string name,
                                 std::set<PreprocessFile*>& visited) {
  /*SymbolId macroId = */ registerSymbol(name);
  if (m_debugMacro)
    std::cout << "PP CALL TO deleteMacro for " << name << std::endl;
  bool found = false;
  // Try CommandLine overrides
  // const std::map<SymbolId,std::string>& defines =
  // m_compileSourceFile->m_commandLineParser->getDefineList();
  // std::map<SymbolId,std::string>::const_iterator itMap =
  // defines.find(macroId);
  // if (itMap != defines.end())
  //  {
  //    result = (*itMap).second;
  //    found = true;
  //  }

  // Try local file scope
  if (found == false) {
    MacroStorage::iterator itr = m_macros.find(name);
    if (itr != m_macros.end()) {
      m_macros.erase(itr);
      m_compilationUnit->deleteMacro(name);
      found = true;
    }
  }
  // Try in included files
  if (found == false) {
    for (std::vector<PreprocessFile*>::iterator iitr = m_includes.begin();
         iitr != m_includes.end(); iitr++) {
      PreprocessFile* pFile = *iitr;
      if (visited.find(pFile) == visited.end()) {
        visited.insert(pFile);
        bool tmp = pFile->deleteMacro(name, visited);
        if (tmp == true) {
          found = true;
          break;
        }
      }
    }
  }
  // Try in file that included this file
  if (found == false) {
    if (m_includer) {
      if (visited.find(m_includer) == visited.end()) {
        visited.insert(m_includer);
        bool tmp = m_includer->deleteMacro(name, visited);
        if (tmp == true) {
          found = true;
        }
      }
    }
  }
  return found;
}

void PreprocessFile::undefineAllMacros(std::set<PreprocessFile*>& visited) {
  if (m_debugMacro) std::cout << "PP CALL TO undefineAllMacros" << std::endl;
  m_macros.clear();
  m_compilationUnit->deleteAllMacros();

  for (std::vector<PreprocessFile*>::iterator iitr = m_includes.begin();
       iitr != m_includes.end(); iitr++) {
    PreprocessFile* pFile = *iitr;
    if (visited.find(pFile) == visited.end()) {
      visited.insert(pFile);
      pFile->undefineAllMacros(visited);
    }
  }

  if (m_includer) {
    if (visited.find(m_includer) == visited.end()) {
      visited.insert(m_includer);
      m_includer->undefineAllMacros(visited);
    }
  }
}

std::string PreprocessFile::getMacro(
    const std::string name, std::vector<std::string>& arguments,
    PreprocessFile* callingFile, unsigned int callingLine,
    LoopCheck& loopChecker, SpecialInstructions& instructions,
    unsigned int embeddedMacroCallLine, SymbolId embeddedMacroCallFile) {
  SymbolId macroId = registerSymbol(name);
  if (m_debugMacro) {
    std::cout << "PP CALL TO getMacro for " << name << "\n";
    for (auto arg : arguments) {
      std::cout << "PP ARG: " << arg << "\n";
    }
    instructions.print();
  }
  std::string result;
  bool found = false;
  // Try CommandLine overrides
  const std::map<SymbolId, std::string>& defines =
      m_compileSourceFile->m_commandLineParser->getDefineList();
  std::map<SymbolId, std::string>::const_iterator itMap = defines.find(macroId);
  if (itMap != defines.end()) {
    result = (*itMap).second;
    found = true;
  }

  // Try local file scope
  if (found == false) {
    MacroInfo* info = m_compilationUnit->getMacroInfo(name);
    if (instructions.m_evaluate == SpecialInstructions::Evaluate) {
      if (info) {
        std::pair<bool, std::string> evalResult = evaluateMacro_(
                name, arguments, callingFile, callingLine, loopChecker, info,
                instructions, embeddedMacroCallLine, embeddedMacroCallFile);
        found = evalResult.first;
        result = evalResult.second;
        result = std::regex_replace(result, std::regex("``"), "");
      }
    } else {
      if (info) {
        found = true;
        result = "";
      }
    }
  }
  if (found == false) {
    if (instructions.m_as_is_undefined_macro ==
        SpecialInstructions::AsIsUndefinedMacro) {
      return "`" + name;
    } else {
      return MacroNotDefined;
    }
  } else {
    return result;
  }
}

SymbolId PreprocessFile::getFileId(unsigned int line) {
  const unsigned int size = m_lineTranslationVec.size();
  if (isMacroBody() && m_macroInfo) {
    return m_macroInfo->m_file;
  } else {
    if (size) {
      if (size == 1) {
        if (line >= m_lineTranslationVec[0].m_originalLine) {
          return (m_lineTranslationVec[0].m_pretendFileId);
        }
      } else {
        unsigned int index = size - 1;
        while (1) {
          if (line >= m_lineTranslationVec[index].m_originalLine) {
            return (m_lineTranslationVec[index].m_pretendFileId);
          }
          if (index == 0) break;
          index--;
        }
      }
      return m_fileId;
    } else {
      return m_fileId;
    }
  }
}

unsigned int PreprocessFile::getLineNb(unsigned int line) {
  if (isMacroBody() && m_macroInfo) {
    return (m_macroInfo->m_line + line - 1);
  } else {
    if (m_lineTranslationVec.size()) {
      unsigned int index = m_lineTranslationVec.size() - 1;
      while (1) {
        if (line >= m_lineTranslationVec[index].m_originalLine) {
          return (m_lineTranslationVec[index].m_pretendLine +
                  (line - m_lineTranslationVec[index].m_originalLine));
        }
        if (index == 0) break;
        index --;
      }
      return line;
    } else {
      return line;
    }
  }
}

std::string PreprocessFile::getPreProcessedFileContent() {
  // If File is empty (Only CR) return an empty string
  bool nonEmpty = false;
  unsigned int pp_result_size = m_result.size();
  for (unsigned int i = 0; i < pp_result_size; i++) {
    if ((m_result[i] != '\n') && (m_result[i] != ' ')) {
      nonEmpty = true;
      break;
    }
  }
  if (!nonEmpty) m_result = "";
  if (m_debugPPResult) {
    const std::string fileName = getSymbol(m_fileId);
    std::string objName =
      (!m_macroBody.empty()) ? "macro " + m_macroBody : "file " + fileName;
    std::cout << "PP RESULT for " << objName
              << " : \nvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv\n"
              << m_result << "\n^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
              << std::endl;
  }
  return m_result;
}

PreprocessFile::IfElseStack& PreprocessFile::getStack() {
  PreprocessFile* tmp = this;
  while (tmp->m_includer != NULL) {
    tmp = tmp->m_includer;
  }
  // std::cout << "STACK FOR: " << tmp->m_fileName << std::endl;
  return tmp->m_ifStack;
}

void PreprocessFile::collectIncludedFiles(std::set<PreprocessFile*>& included) {
  for (std::vector<PreprocessFile*>::iterator itr = m_includes.begin();
       itr != m_includes.end(); itr++) {
    if (!(*itr)->isMacroBody()) {
      included.insert(*itr);
    }
    (*itr)->collectIncludedFiles(included);
  }
}

void PreprocessFile::saveCache() {
   if (getCompileSourceFile()->getCommandLineParser()->parseOnly())
    return;
   if (m_macroBody.empty()) {
     if (!m_usingCachedVersion) {
       PPCache cache(this);
       cache.save();
     }
   }
   for (std::vector<PreprocessFile*>::iterator itr = m_includes.begin();
        itr != m_includes.end(); itr++) {
     (*itr)->saveCache();
   }
}
