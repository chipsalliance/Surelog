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
 * File:   ParseFile.cpp
 * Author: alain
 *
 * Created on February 24, 2017, 10:03 PM
 */

#include <Surelog/Cache/ParseCache.h>
#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/Package/Precompiled.h>
#include <Surelog/SourceCompile/AntlrParserErrorListener.h>
#include <Surelog/SourceCompile/AntlrParserHandler.h>
#include <Surelog/SourceCompile/CompileSourceFile.h>
#include <Surelog/SourceCompile/ParseFile.h>
#include <Surelog/SourceCompile/SV3_1aTreeShapeListener.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/FileUtils.h>
#include <Surelog/Utils/StringUtils.h>
#include <Surelog/Utils/Timer.h>
#include <antlr4-runtime.h>
#include <parser/SV3_1aLexer.h>
#include <parser/SV3_1aParser.h>

#include <fstream>
#include <sstream>

namespace SURELOG {

namespace fs = std::filesystem;

ParseFile::ParseFile(SymbolId fileId, SymbolTable* symbolTable,
                     ErrorContainer* errors)
    : m_fileId(fileId),
      m_ppFileId(0),
      m_compileSourceFile(nullptr),
      m_compilationUnit(nullptr),
      m_library(nullptr),
      m_antlrParserHandler(nullptr),
      m_listener(nullptr),
      m_usingCachedVersion(false),
      m_keepParserHandler(false),
      m_fileContent(nullptr),
      debug_AstModel(false),
      m_parent(nullptr),
      m_offsetLine(0),
      m_symbolTable(symbolTable),
      m_errors(errors) {
  debug_AstModel = false;
}

ParseFile::ParseFile(SymbolId fileId, CompileSourceFile* csf,
                     CompilationUnit* compilationUnit, Library* library,
                     SymbolId ppFileId, bool keepParserHandler)
    : m_fileId(fileId),
      m_ppFileId(ppFileId),
      m_compileSourceFile(csf),
      m_compilationUnit(compilationUnit),
      m_library(library),
      m_antlrParserHandler(nullptr),
      m_listener(nullptr),
      m_usingCachedVersion(false),
      m_keepParserHandler(keepParserHandler),
      m_fileContent(nullptr),
      debug_AstModel(false),
      m_parent(nullptr),
      m_offsetLine(0),
      m_symbolTable(nullptr),
      m_errors(nullptr) {
  debug_AstModel =
      m_compileSourceFile->getCommandLineParser()->getDebugAstModel();
}

ParseFile::ParseFile(CompileSourceFile* compileSourceFile, ParseFile* parent,
                     SymbolId chunkFileId, unsigned int offsetLine)
    : m_fileId(parent->m_fileId),
      m_ppFileId(chunkFileId),
      m_compileSourceFile(compileSourceFile),
      m_compilationUnit(parent->m_compilationUnit),
      m_library(parent->m_library),
      m_antlrParserHandler(nullptr),
      m_listener(nullptr),
      m_usingCachedVersion(false),
      m_keepParserHandler(parent->m_keepParserHandler),
      m_fileContent(parent->m_fileContent),
      debug_AstModel(false),
      m_parent(parent),
      m_offsetLine(offsetLine),
      m_symbolTable(nullptr),
      m_errors(nullptr) {
  parent->m_children.push_back(this);
}

ParseFile::ParseFile(const std::string& text, CompileSourceFile* csf,
                     CompilationUnit* compilationUnit, Library* library)
    : m_fileId(0),
      m_ppFileId(0),
      m_compileSourceFile(csf),
      m_compilationUnit(compilationUnit),
      m_library(library),
      m_antlrParserHandler(nullptr),
      m_listener(nullptr),
      m_usingCachedVersion(false),
      m_keepParserHandler(false),
      m_fileContent(nullptr),
      debug_AstModel(false),
      m_parent(nullptr),
      m_offsetLine(0),
      m_symbolTable(csf->getSymbolTable()),
      m_errors(csf->getErrorContainer()),
      m_sourceText(text) {
  debug_AstModel =
      m_compileSourceFile->getCommandLineParser()->getDebugAstModel();
}

ParseFile::~ParseFile() {
  if (!m_keepParserHandler) delete m_antlrParserHandler;
  delete m_listener;
}

SymbolTable* ParseFile::getSymbolTable() {
  return m_symbolTable ? m_symbolTable : m_compileSourceFile->getSymbolTable();
}

ErrorContainer* ParseFile::getErrorContainer() {
  return m_errors ? m_errors : m_compileSourceFile->getErrorContainer();
}

SymbolId ParseFile::registerSymbol(std::string_view symbol) {
  return getCompileSourceFile()->getSymbolTable()->registerSymbol(symbol);
}

SymbolId ParseFile::getId(std::string_view symbol) {
  return getCompileSourceFile()->getSymbolTable()->getId(symbol);
}

std::string ParseFile::getSymbol(SymbolId id) const {
  return getCompileSourceFile()->getSymbolTable()->getSymbol(id);
}

fs::path ParseFile::getFileName(unsigned int line) {
  return getSymbol(getFileId(line));
}

void ParseFile::addError(Error& error) {
  getCompileSourceFile()->getErrorContainer()->addError(error);
}

void ParseFile::buildLineInfoCache_() {
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  if (!pp) return;
  auto const& infos = pp->getIncludeFileInfo();
  if (!infos.empty()) {
    fileInfoCache.resize(pp->getSumLineCount() + 10);
    lineInfoCache.resize(pp->getSumLineCount() + 10);
    lineInfoCache[0] = 1;
    fileInfoCache[0] = m_fileId;
    for (unsigned int lineItr = 1; lineItr < pp->getSumLineCount() + 10;
         lineItr++) {
      fileInfoCache[lineItr] = m_fileId;
      lineInfoCache[lineItr] = lineItr;
      bool inRange = false;
      unsigned int indexOpeningRange = 0;
      unsigned int index = infos.size() - 1;
      while (1) {
        if ((lineItr >= infos[index].m_originalStartLine) &&
            (infos[index].m_type == IncludeFileInfo::POP)) {
          SymbolId fileId = infos[index].m_sectionFile;
          fileInfoCache[lineItr] = fileId;
          unsigned int l = infos[index].m_sectionStartLine +
                           (lineItr - infos[index].m_originalStartLine);
          lineInfoCache[lineItr] = l;
          break;
        }
        if (infos[index].m_type == IncludeFileInfo::POP) {
          if (!inRange) {
            inRange = true;
            indexOpeningRange = infos[index].m_indexOpening;
          }
        } else {
          if (inRange) {
            if (index == indexOpeningRange) inRange = false;
          }
        }
        if ((lineItr >= infos[index].m_originalStartLine) &&
            (infos[index].m_type == IncludeFileInfo::PUSH) &&
            (infos[index].m_indexClosing > -1) &&
            (lineItr <
             infos[infos[index].m_indexClosing].m_originalStartLine)) {
          SymbolId fileId = infos[index].m_sectionFile;
          fileInfoCache[lineItr] = fileId;
          unsigned int l = infos[index].m_sectionStartLine +
                           (lineItr - infos[index].m_originalStartLine);
          lineInfoCache[lineItr] = l;
          break;
        }
        if (index == 0) break;
        index--;
      }
    }
  }
}

SymbolId ParseFile::getFileId(unsigned int line) {
  if (!getCompileSourceFile()) {
    return m_fileId;
  }
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  if (!pp) return 0;
  auto& infos = pp->getIncludeFileInfo();
  if (!infos.empty()) {
    if (!fileInfoCache.empty()) {
      if (line > fileInfoCache.size()) {
        SymbolId fileId = registerSymbol("CACHE OUT OF BOUND");
        Location ppfile(fileId);
        Error err(ErrorDefinition::PA_INTERNAL_ERROR, ppfile);
        addError(err);
      }
      return fileInfoCache[line];
    }
    buildLineInfoCache_();
    if (line > fileInfoCache.size()) {
      SymbolId fileId = registerSymbol("CACHE OUT OF BOUND");
      Location ppfile(fileId);
      Error err(ErrorDefinition::PA_INTERNAL_ERROR, ppfile);
      addError(err);
    }
    return fileInfoCache[line];
  } else {
    return m_fileId;
  }
}

unsigned int ParseFile::getLineNb(unsigned int line) {
  if (!getCompileSourceFile()) return line;
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  if (!pp) return 0;
  auto& infos = pp->getIncludeFileInfo();
  if (!infos.empty()) {
    if (!lineInfoCache.empty()) {
      if (line > lineInfoCache.size()) {
        SymbolId fileId = registerSymbol("CACHE OUT OF BOUND");
        Location ppfile(fileId);
        Error err(ErrorDefinition::PA_INTERNAL_ERROR, ppfile);
        addError(err);
      }
      return lineInfoCache[line];
    }
    buildLineInfoCache_();
    if (line > lineInfoCache.size()) {
      SymbolId fileId = registerSymbol("CACHE OUT OF BOUND");
      Location ppfile(fileId);
      Error err(ErrorDefinition::PA_INTERNAL_ERROR, ppfile);
      addError(err);
    }
    return lineInfoCache[line];
  } else {
    return line;
  }
}

bool ParseFile::parseOneFile_(const std::string& fileName,
                              unsigned int lineOffset) {
  CommandLineParser* clp = getCompileSourceFile()->getCommandLineParser();
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  Timer tmr;
  AntlrParserHandler* antlrParserHandler = new AntlrParserHandler();
  m_antlrParserHandler = antlrParserHandler;
  std::ifstream stream;
  std::stringstream ss(m_sourceText);
  if (m_sourceText.empty()) {
    stream.open(fileName);
    if (!stream.good()) {
      SymbolId fileId = registerSymbol(fileName);
      Location ppfile(fileId);
      Error err(ErrorDefinition::PA_CANNOT_OPEN_FILE, ppfile);
      addError(err);
      return false;
    }
    antlrParserHandler->m_inputStream = new antlr4::ANTLRInputStream(stream);
    stream.close();
  } else {
    antlrParserHandler->m_inputStream = new antlr4::ANTLRInputStream(ss);
  }

  antlrParserHandler->m_errorListener =
      new AntlrParserErrorListener(this, false, lineOffset, fileName);
  antlrParserHandler->m_lexer =
      new SV3_1aLexer(antlrParserHandler->m_inputStream);
  const auto suffix = StringUtils::leaf(fileName);
  VerilogVersion version = VerilogVersion::SystemVerilog;
  if (pp) version = pp->getVerilogVersion();
  if (version != VerilogVersion::NoVersion) {
    switch (version) {
      case VerilogVersion::NoVersion:
        break;
      case VerilogVersion::Verilog1995:
        antlrParserHandler->m_lexer->sverilog = false;
        break;
      case VerilogVersion::Verilog2001:
        antlrParserHandler->m_lexer->sverilog = false;
        break;
      case VerilogVersion::Verilog2005:
        antlrParserHandler->m_lexer->sverilog = false;
        break;
      case VerilogVersion::SVerilog2005:
        antlrParserHandler->m_lexer->sverilog = true;
        break;
      case VerilogVersion::Verilog2009:
        antlrParserHandler->m_lexer->sverilog = true;
        break;
      case VerilogVersion::SystemVerilog:
        antlrParserHandler->m_lexer->sverilog = true;
        break;
    }
  } else {
    fs::path baseFileName = FileUtils::basename(fileName);
    if ((suffix == "sv") || (clp->fullSVMode()) ||
        (clp->isSVFile(baseFileName))) {
      antlrParserHandler->m_lexer->sverilog = true;
    } else {
      antlrParserHandler->m_lexer->sverilog = false;
    }
  }

  antlrParserHandler->m_lexer->removeErrorListeners();
  antlrParserHandler->m_lexer->addErrorListener(
      antlrParserHandler->m_errorListener);
  antlrParserHandler->m_tokens =
      new antlr4::CommonTokenStream(antlrParserHandler->m_lexer);
  antlrParserHandler->m_tokens->fill();

  if (getCompileSourceFile()->getCommandLineParser()->profile()) {
    // m_profileInfo += "Tokenizer: " + std::to_string (tmr.elapsed_rounded
    // ())
    // + " " + fileName + "\n";
    tmr.reset();
  }

  antlrParserHandler->m_parser = new SV3_1aParser(antlrParserHandler->m_tokens);
  if (getCompileSourceFile()->getCommandLineParser()->profile()) {
    m_antlrParserHandler->m_parser->setProfile(true);
  }
  m_antlrParserHandler->m_parser
      ->getInterpreter<antlr4::atn::ParserATNSimulator>()
      ->setPredictionMode(antlr4::atn::PredictionMode::SLL);
  m_antlrParserHandler->m_parser->removeErrorListeners();
  m_antlrParserHandler->m_parser->setErrorHandler(
      std::make_shared<antlr4::BailErrorStrategy>());

  try {
    m_antlrParserHandler->m_tree =
        m_antlrParserHandler->m_parser->top_level_rule();

    if (getCompileSourceFile()->getCommandLineParser()->profile()) {
      m_profileInfo +=
          "SLL Parsing: " + StringUtils::to_string(tmr.elapsed_rounded()) +
          "s " + fileName + "\n";
      tmr.reset();
      profileParser();
    }
  } catch (antlr4::ParseCancellationException& pex) {
    m_antlrParserHandler->m_tokens->reset();
    m_antlrParserHandler->m_parser->reset();
    m_antlrParserHandler->m_parser->removeErrorListeners();
    if (getCompileSourceFile()->getCommandLineParser()->profile()) {
      m_antlrParserHandler->m_parser->setProfile(true);
    }
    m_antlrParserHandler->m_parser->setErrorHandler(
        std::make_shared<antlr4::DefaultErrorStrategy>());
    antlrParserHandler->m_parser->addErrorListener(
        antlrParserHandler->m_errorListener);
    antlrParserHandler->m_parser
        ->getInterpreter<antlr4::atn::ParserATNSimulator>()
        ->setPredictionMode(antlr4::atn::PredictionMode::LL);
    antlrParserHandler->m_tree = antlrParserHandler->m_parser->top_level_rule();

    if (getCompileSourceFile()->getCommandLineParser()->profile()) {
      m_profileInfo +=
          "LL  Parsing: " + StringUtils::to_string(tmr.elapsed_rounded()) +
          " " + fileName + "\n";
      tmr.reset();
      profileParser();
    }
  }
  /* Failed attempt to minimize memory usage:
     m_antlrParserHandler->m_parser->getInterpreter<antlr4::atn::ParserATNSimulator>()->clearDFA();
     SV3_1aParser::_sharedContextCache.clear();
  */
  if (m_sourceText.empty()) {
    stream.close();
  }
  return true;
}

void ParseFile::profileParser() {
  // Core dumps
  /*
  for (auto iterator =
  m_antlrParserHandler->m_parser->getParseInfo().getDecisionInfo().begin();
       iterator !=
  m_antlrParserHandler->m_parser->getParseInfo().getDecisionInfo().end();
  iterator++) { antlr4::atn::DecisionInfo& decisionInfo = *iterator;
    antlr4::atn::DecisionState* ds =
        m_antlrParserHandler->m_parser->getATN().getDecisionState(decisionInfo.decision);
    std::string rule =
  m_antlrParserHandler->m_parser->getRuleNames()[ds->ruleIndex]; if
  (decisionInfo.timeInPrediction > 0) { std::cout << std::left << std::setw(35)
  << std::setfill(' ') << rule; std::cout << std::left << std::setw(15) <<
  std::setfill(' ')
                << decisionInfo.timeInPrediction;
      std::cout << std::left << std::setw(15) << std::setfill(' ')
                << decisionInfo.invocations;
      std::cout << std::left << std::setw(15) << std::setfill(' ')
                << decisionInfo.SLL_TotalLook;
      std::cout << std::left << std::setw(15) << std::setfill(' ')
                << decisionInfo.SLL_MaxLook;
      std::cout << std::left << std::setw(15) << std::setfill(' ')
                << decisionInfo.ambiguities.size();
      std::cout << std::left << std::setw(15) << std::setfill(' ')
                << decisionInfo.errors.size();
      std::cout << std::endl;
    }
  }
  */
}

std::string ParseFile::getProfileInfo() {
  std::string profile;
  profile = m_profileInfo;
  for (const ParseFile* child : m_children) {
    profile += child->m_profileInfo;
  }
  return profile;
}

bool ParseFile::parse() {
  Precompiled* prec = Precompiled::getSingleton();
  fs::path root = FileUtils::basename(this->getPpFileName());
  bool precompiled = false;
  if (prec->isFilePrecompiled(root)) precompiled = true;

  if (m_children.empty()) {
    ParseCache cache(this);

    if (cache.restore()) {
      m_usingCachedVersion = true;
      if (debug_AstModel && !precompiled)
        std::cout << m_fileContent->printObjects();
      return true;
    }
  } else {
    bool ok = true;
    for (ParseFile* child : m_children) {
      ParseCache cache(child);

      if (cache.restore()) {
        child->m_fileContent->setParent(m_fileContent);
        m_usingCachedVersion = true;
        if (debug_AstModel && !precompiled)
          std::cout << child->m_fileContent->printObjects();
      } else {
        ok = false;
      }
    }
    if (ok) {
      return true;
    }
  }

  // This is not a parent Parser object
  if (m_children.empty()) {
    // std::cout << std::endl << "Parsing " << getSymbol(m_ppFileId) << "
    // Line: " << m_offsetLine << std::endl << std::flush;

    parseOneFile_(getSymbol(m_ppFileId), m_offsetLine);

    // m_listener = new SV3_1aTreeShapeListener (this,
    // m_antlrParserHandler->m_tokens, m_offsetLine);
    // tree::ParseTreeWalker::DEFAULT.walk (m_listener,
    // m_antlrParserHandler->m_tree); std::cout << std::endl << "End Parsing "
    // << getSymbol(m_ppFileId) << " Line: " << m_offsetLine << std::endl <<
    // std::flush;
  }

  // This is either a parent Parser object of this Parser object has no parent
  if (!m_children.empty() || (m_parent == nullptr)) {
    if ((m_parent == nullptr) && (m_children.empty())) {
      Timer tmr;

      m_listener = new SV3_1aTreeShapeListener(
          this, m_antlrParserHandler->m_tokens, m_offsetLine);
      antlr4::tree::ParseTreeWalker::DEFAULT.walk(m_listener,
                                                  m_antlrParserHandler->m_tree);

      if (debug_AstModel && !precompiled)
        std::cout << m_fileContent->printObjects();

      if (getCompileSourceFile()->getCommandLineParser()->profile()) {
        // m_profileInfo += "AST Walking: " + std::to_string
        // (tmr.elapsed_rounded ()) + "\n";
        tmr.reset();
      }

      ParseCache cache(this);
      if (!cache.save()) {
        return false;
      }

      if (getCompileSourceFile()->getCommandLineParser()->profile()) {
        m_profileInfo +=
            "Cache saving: " + std::to_string(tmr.elapsed_rounded()) + "s\n";
        std::cout << "Cache saving: " + std::to_string(tmr.elapsed_rounded()) +
                         "s\n"
                  << std::flush;
        tmr.reset();
      }
    }

    if (!m_children.empty()) {
      for (ParseFile* child : m_children) {
        if (child->m_antlrParserHandler) {
          // Only visit the chunks that got re-parsed
          // TODO: Incrementally regenerate the FileContent
          child->m_fileContent->setParent(m_fileContent);
          child->m_listener = new SV3_1aTreeShapeListener(
              child, child->m_antlrParserHandler->m_tokens,
              child->m_offsetLine);

          Timer tmr;
          antlr4::tree::ParseTreeWalker::DEFAULT.walk(
              child->m_listener, child->m_antlrParserHandler->m_tree);

          if (getCompileSourceFile()->getCommandLineParser()->profile()) {
            // m_profileInfo += "For file " + getSymbol
            // (child->m_ppFileId) + ", AST Walking took" +
            // std::to_string (tmr.elapsed_rounded ()) + "\n";
            tmr.reset();
          }

          if (debug_AstModel && !precompiled)
            std::cout << child->m_fileContent->printObjects();

          ParseCache cache(child);
          if (!cache.save()) {
            return false;
          }
        }
      }
    }
  }
  return true;
}
}  // namespace SURELOG
