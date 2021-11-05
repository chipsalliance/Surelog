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
#include "SourceCompile/ParseFile.h"

#include <cstdlib>
#include <iostream>

#include "Cache/ParseCache.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorContainer.h"
#include "Package/Precompiled.h"
#include "Recognizer.h"
#include "SourceCompile/AntlrParserErrorListener.h"
#include "SourceCompile/AntlrParserHandler.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/SV3_1aTreeShapeListener.h"
#include "SourceCompile/SymbolTable.h"
#include "Utils/FileUtils.h"
#include "Utils/ParseUtils.h"
#include "Utils/StringUtils.h"
#include "Utils/Timer.h"
#include "antlr4-runtime.h"
#include "atn/ParserATNSimulator.h"
#include "parser/SV3_1aLexer.h"
#include "parser/SV3_1aParser.h"
#include "parser/SV3_1aParserBaseListener.h"

namespace SURELOG {
ParseFile::ParseFile(SymbolId fileId, SymbolTable* symbolTable,
                     ErrorContainer* errors)
    : m_fileId(fileId),
      m_ppFileId(0),
      m_compileSourceFile(NULL),
      m_compilationUnit(NULL),
      m_library(NULL),
      m_antlrParserHandler(NULL),
      m_listener(NULL),
      m_usingCachedVersion(false),
      m_keepParserHandler(false),
      m_fileContent(NULL),
      debug_AstModel(false),
      m_parent(NULL),
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
      m_antlrParserHandler(NULL),
      m_listener(NULL),
      m_usingCachedVersion(false),
      m_keepParserHandler(keepParserHandler),
      m_fileContent(NULL),
      debug_AstModel(false),
      m_parent(NULL),
      m_offsetLine(0),
      m_symbolTable(NULL),
      m_errors(NULL) {
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
      m_antlrParserHandler(NULL),
      m_listener(NULL),
      m_usingCachedVersion(false),
      m_keepParserHandler(parent->m_keepParserHandler),
      m_fileContent(parent->m_fileContent),
      debug_AstModel(false),
      m_parent(parent),
      m_offsetLine(offsetLine),
      m_symbolTable(NULL),
      m_errors(NULL) {
  parent->m_children.push_back(this);
}

ParseFile::ParseFile(std::string_view text, CompileSourceFile* csf,
                     CompilationUnit* compilationUnit, Library* library)
    : m_fileId(0),
      m_ppFileId(0),
      m_compileSourceFile(csf),
      m_compilationUnit(compilationUnit),
      m_library(library),
      m_antlrParserHandler(NULL),
      m_listener(NULL),
      m_usingCachedVersion(false),
      m_keepParserHandler(false),
      m_fileContent(NULL),
      debug_AstModel(false),
      m_parent(NULL),
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

SymbolTable* ParseFile::getSymbolTable() const {
  return m_symbolTable ? m_symbolTable : m_compileSourceFile->getSymbolTable();
}

ErrorContainer* ParseFile::getErrorContainer() const {
  return m_errors ? m_errors : m_compileSourceFile->getErrorContainer();
}

SymbolId ParseFile::registerSymbol(std::string_view symbol) {
  return getCompileSourceFile()->getSymbolTable()->registerSymbol(symbol);
}

SymbolId ParseFile::getId(std::string_view symbol) const {
  return getCompileSourceFile()->getSymbolTable()->getId(symbol);
}

std::string_view ParseFile::getSymbol(SymbolId id) const {
  return getCompileSourceFile()->getSymbolTable()->getSymbol(id);
}

std::string_view ParseFile::getFileName(unsigned int line) {
  return getSymbol(getFileId(line));
}

void ParseFile::addError(Error& error) {
  getCompileSourceFile()->getErrorContainer()->addError(error);
}

void ParseFile::buildLineInfoCache_() {
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  if (!pp) return;
  auto& infos = pp->getIncludeFileInfo();
  if (infos.size()) {
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
        if ((lineItr >= infos[index].m_originalLine) &&
            (infos[index].m_type == IncludeFileInfo::POP)) {
          SymbolId fileId = infos[index].m_sectionFile;
          fileInfoCache[lineItr] = fileId;
          unsigned int l = infos[index].m_sectionStartLine +
                           (lineItr - infos[index].m_originalLine);
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
        if ((lineItr >= infos[index].m_originalLine) &&
            (infos[index].m_type == IncludeFileInfo::PUSH) &&
            (infos[index].m_indexClosing > -1) &&
            (lineItr < infos[infos[index].m_indexClosing].m_originalLine)) {
          SymbolId fileId = infos[index].m_sectionFile;
          fileInfoCache[lineItr] = fileId;
          unsigned int l = infos[index].m_sectionStartLine +
                           (lineItr - infos[index].m_originalLine);
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
  if (infos.size()) {
    if (fileInfoCache.empty()) {
      buildLineInfoCache_();
    }
    if (line >= fileInfoCache.size()) {
      SymbolId fileId = registerSymbol("CACHE OUT OF BOUND");
      Location ppfile(fileId);
      Error err(ErrorDefinition::PA_INTERNAL_ERROR, ppfile);
      addError(err);
      return m_fileId;
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
  if (infos.size()) {
    if (lineInfoCache.empty()) {
      buildLineInfoCache_();
    }
    if (line >= lineInfoCache.size()) {
      SymbolId fileId = registerSymbol("CACHE OUT OF BOUND");
      Location ppfile(fileId);
      Error err(ErrorDefinition::PA_INTERNAL_ERROR, ppfile);
      addError(err);
      return line;
    }
    return lineInfoCache[line];
  } else {
    return line;
  }
}

bool ParseFile::parseOneFile_(std::string_view fileName,
                              unsigned int lineOffset) {
  CommandLineParser* clp = getCompileSourceFile()->getCommandLineParser();
  PreprocessFile* pp = getCompileSourceFile()->getPreprocessor();
  Timer tmr;
  AntlrParserHandler* antlrParserHandler = new AntlrParserHandler();
  m_antlrParserHandler = antlrParserHandler;
  std::ifstream stream;
  std::stringstream ss(m_sourceText);
  if (m_sourceText.empty()) {
    stream.open(std::string(fileName));
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
    std::string baseFileName = FileUtils::basename(fileName);
    const std::string_view suffix = StringUtils::leaf(fileName);
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

  m_antlrParserHandler->m_parser
      ->getInterpreter<antlr4::atn::ParserATNSimulator>()
      ->setPredictionMode(antlr4::atn::PredictionMode::SLL);
  m_antlrParserHandler->m_parser->setErrorHandler(
      std::make_shared<antlr4::BailErrorStrategy>());
  m_antlrParserHandler->m_parser->removeErrorListeners();

  try {
    m_antlrParserHandler->m_tree =
        m_antlrParserHandler->m_parser->top_level_rule();

    if (getCompileSourceFile()->getCommandLineParser()->profile()) {
      m_profileInfo.append("SLL Parsing: ")
          .append(StringUtils::to_string(tmr.elapsed_rounded()))
          .append("s ")
          .append(fileName)
          .append("\n");
      tmr.reset();
    }
  } catch (antlr4::ParseCancellationException& pex) {
    m_antlrParserHandler->m_tokens->reset();
    m_antlrParserHandler->m_parser->reset();

    m_antlrParserHandler->m_parser->setErrorHandler(
        std::make_shared<antlr4::DefaultErrorStrategy>());
    antlrParserHandler->m_parser->removeErrorListeners();
    antlrParserHandler->m_parser->addErrorListener(
        antlrParserHandler->m_errorListener);
    antlrParserHandler->m_parser
        ->getInterpreter<antlr4::atn::ParserATNSimulator>()
        ->setPredictionMode(antlr4::atn::PredictionMode::LL);
    antlrParserHandler->m_tree = antlrParserHandler->m_parser->top_level_rule();

    if (getCompileSourceFile()->getCommandLineParser()->profile()) {
      m_profileInfo.append("LL  Parsing: ")
          .append(StringUtils::to_string(tmr.elapsed_rounded()))
          .append(" ")
          .append(fileName)
          .append("\n");
      tmr.reset();
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

std::string ParseFile::getProfileInfo() {
  std::string profile;
  profile = m_profileInfo;
  for (unsigned int i = 0; i < m_children.size(); i++)
    profile += m_children[i]->m_profileInfo;

  return profile;
}

bool ParseFile::parse() {
  Precompiled* prec = Precompiled::getSingleton();
  std::string root = FileUtils::basename(this->getPpFileName());
  bool precompiled = false;
  if (prec->isFilePrecompiled(root)) precompiled = true;

  if (m_children.size() == 0) {
    ParseCache cache(this);

    if (cache.restore()) {
      m_usingCachedVersion = true;
      if (debug_AstModel && !precompiled)
        std::cout << m_fileContent->printObjects();
      return true;
    }
  } else {
    bool ok = true;
    for (unsigned int i = 0; i < m_children.size(); i++) {
      ParseCache cache(m_children[i]);

      if (cache.restore()) {
        m_children[i]->m_fileContent->setParent(m_fileContent);
        m_usingCachedVersion = true;
        if (debug_AstModel && !precompiled)
          std::cout << m_children[i]->m_fileContent->printObjects();
      } else {
        ok = false;
      }
    }
    if (ok) {
      return true;
    }
  }

  // This is not a parent Parser object
  if (m_children.size() == 0) {
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
  if ((m_children.size() != 0) || (m_parent == NULL)) {
    if ((m_parent == NULL) && (m_children.size() == 0)) {
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

    if (m_children.size() != 0) {
      for (unsigned int i = 0; i < m_children.size(); i++) {
        if (m_children[i]->m_antlrParserHandler) {
          // Only visit the chunks that got re-parsed
          // TODO: Incrementally regenerate the FileContent
          m_children[i]->m_fileContent->setParent(m_fileContent);
          m_children[i]->m_listener = new SV3_1aTreeShapeListener(
              m_children[i], m_children[i]->m_antlrParserHandler->m_tokens,
              m_children[i]->m_offsetLine);

          Timer tmr;
          antlr4::tree::ParseTreeWalker::DEFAULT.walk(
              m_children[i]->m_listener,
              m_children[i]->m_antlrParserHandler->m_tree);

          if (getCompileSourceFile()->getCommandLineParser()->profile()) {
            // m_profileInfo += "For file " + getSymbol
            // (m_children[i]->m_ppFileId) + ", AST Walking took" +
            // std::to_string (tmr.elapsed_rounded ()) + "\n";
            tmr.reset();
          }

          if (debug_AstModel && !precompiled)
            std::cout << m_children[i]->m_fileContent->printObjects();

          ParseCache cache(m_children[i]);
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
