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

#include "SourceCompile/SymbolTable.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/PreprocessFile.h"
#include "Utils/StringUtils.h"

#include <cstdlib>
#include <iostream>
#include <regex>

using namespace std;
using namespace SURELOG;

#include "parser/SV3_1aPpLexer.h"
#include "parser/SV3_1aPpParser.h"
#include "parser/SV3_1aPpParserBaseListener.h"
using namespace antlr4;
#include "Utils/ParseUtils.h"
#include "Utils/FileUtils.h"

#include "SourceCompile/SV3_1aPpTreeShapeListener.h"

void SV3_1aPpTreeShapeListener::logError(ErrorDefinition::ErrorType error,
                                         ParserRuleContext* ctx,
                                         std::string object, bool printColumn) {
  if (m_instructions.m_mute) return;
  std::pair<int, int> lineCol =
      ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (m_pp->getMacroInfo()) {
    Location loc(m_pp->getMacroInfo()->m_file,
                 m_pp->getMacroInfo()->m_line + lineCol.first - 1,
                 lineCol.second, getSymbolTable()->registerSymbol(object));
    Location extraLoc(m_pp->getIncluderFileId(m_pp->getIncluderLine()),
                      m_pp->getIncluderLine(), 0, 0);
    Error err(error, loc, extraLoc);
    m_pp->addError(err);
  } else {
    Location loc(m_pp->getFileId(lineCol.first), m_pp->getLineNb(lineCol.first),
                 printColumn ? lineCol.second : 0,
                 getSymbolTable()->registerSymbol(object));
    Error err(error, loc);
    m_pp->addError(err);
  }
}

void SV3_1aPpTreeShapeListener::logError(ErrorDefinition::ErrorType error,
                                         Location& loc, bool showDuplicates) {
  if (m_instructions.m_mute) return;
  Error err(error, loc);
  m_pp->getCompileSourceFile()->getErrorContainer()->addError(err,
                                                              showDuplicates);
}

void SV3_1aPpTreeShapeListener::logError(ErrorDefinition::ErrorType error,
                                         Location& loc, Location& extraLoc,
                                         bool showDuplicates) {
  if (m_instructions.m_mute) return;
  std::vector<Location> extras;
  extras.push_back(extraLoc);
  Error err(error, loc, &extras);
  m_pp->getCompileSourceFile()->getErrorContainer()->addError(err,
                                                              showDuplicates);
}

void SV3_1aPpTreeShapeListener::enterComments(
    SV3_1aPpParser::CommentsContext* ctx) {
  // if (m_pp->getIncluder ())
  //  return;
  if (!m_pp->getCompileSourceFile()->getCommandLineParser()->filterComments()) {
    if (m_inActiveBranch &&
        (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
        (!m_inMacroDefinitionParsing)) {
      if (ctx->Block_comment()) {
        m_pp->append(ctx->Block_comment()->getText());
      } else if (ctx->One_line_comment()) {
        m_pp->append(ctx->One_line_comment()->getText());
      }
    }
  }
}

void SV3_1aPpTreeShapeListener::enterNumber(
    SV3_1aPpParser::NumberContext* ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion))) {
    if (!m_inMacroDefinitionParsing) {
      std::string text = ctx->Number()->getText();
      std::string text2;
      bool firstNonSpace = false;
      unsigned int size = text.size();
      for (unsigned int i = 0; i < size; i++) {
        if (text[i] != ' ') {
          firstNonSpace = true;
        }
        if (firstNonSpace) {
          if ((i < size - 1) && (text[i] == ' ')) {
            continue;
          }
          text2 += text[i];
        }
      }
      m_pp->append(text2);
    }
  }
}

void SV3_1aPpTreeShapeListener::forwardToParser(ParserRuleContext* ctx) {
  if (m_inActiveBranch && (!m_inMacroDefinitionParsing) &&
      (!m_pp->getCompileSourceFile()
            ->getCommandLineParser()
            ->filterSimpleDirectives()) &&
      (!(m_filterProtectedRegions && m_inProtectedRegion))) {
    m_pp->append(ctx->getText() + "\n");
  }
}

void SV3_1aPpTreeShapeListener::checkMultiplyDefinedMacro(
    std::string& macroName, ParserRuleContext* ctx) {
  std::set<PreprocessFile*> visited;
  MacroInfo* macroInf = m_pp->getMacro(macroName);
  if (macroInf) {
    std::pair<int, int> lineCol =
        ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
    if ((macroInf->m_file == m_pp->getFileId(lineCol.first)) &&
        (m_pp->getLineNb(lineCol.first) == macroInf->m_line))
      return;
    Location loc(m_pp->getFileId(lineCol.first), m_pp->getLineNb(lineCol.first),
                 0, getSymbolTable()->getId(macroName));
    Location extraLoc(macroInf->m_file, macroInf->m_line, 0, 0);
    logError(ErrorDefinition::PP_MULTIPLY_DEFINED_MACRO, loc, extraLoc);
    visited.erase(visited.begin(), visited.end());
    // So we can store the latest declaration
    m_pp->deleteMacro(macroName, visited);
  }
}

void SV3_1aPpTreeShapeListener::enterUnterminated_string (
                            SV3_1aPpParser::Unterminated_stringContext *ctx) {
  std::string st = ctx->getText ();
  logError (ErrorDefinition::PP_UNTERMINATED_STRING, ctx, st, true);
  m_pp->append(st);
}

void SV3_1aPpTreeShapeListener::enterInclude_directive(
    SV3_1aPpParser::Include_directiveContext* ctx) {
  if (m_inActiveBranch && (!m_inMacroDefinitionParsing)) {
    std::pair<int, int> lineCol =
        ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
    std::string fileName;
    int openingIndex = -1;
    if (ctx->String()) {
      fileName = ctx->String()->getText();
    } else if (ctx->macro_instance()) {
      fileName = m_pp->evaluateMacroInstance(
          ctx->macro_instance()->getText(), m_pp, lineCol.first,
          PreprocessFile::SpecialInstructions::CheckLoop,
          PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
    } else {
      Location loc(m_pp->getFileId(lineCol.first),
                   m_pp->getLineNb(lineCol.first), 0, 0);
      logError(ErrorDefinition::PP_INVALID_INCLUDE_FILENAME, loc);
      return;
    }

    if (m_pp->m_debugPP)
      std::cout << "PP INCLUDE DIRECTIVE " << fileName << std::endl;
    if (fileName.size() && fileName[0] == '\"')
      fileName = fileName.substr(1, fileName.size() - 2);

    SymbolId fileId = getSymbolTable()->registerSymbol(fileName);
    SymbolId locfileId = FileUtils::locateFile(fileId, getSymbolTable(),
                                               m_pp->getCompileSourceFile()
                                                   ->getCommandLineParser()
                                                   ->getIncludePaths());
    if (locfileId != getSymbolTable()->getBadId()) {
      fileName = getSymbolTable()->getSymbol(locfileId);
      fileId = locfileId;
    }

    if (m_pp->getCompileSourceFile()->getCommandLineParser()->verbose()) {
      Location loc(fileId);
      logError(ErrorDefinition::PP_PROCESSING_INCLUDE_FILE, loc, true);
    }

    // Detect include loop
    PreprocessFile* tmp = m_pp;
    while (tmp) {
      if (tmp->getFileId(0) == fileId) {
        Location loc(m_pp->getFileId(lineCol.first), lineCol.first, 0, fileId);
        logError(ErrorDefinition::PP_RECURSIVE_INCLUDE_DIRECTIVE, loc, true);
        return;
      }
      tmp = tmp->getIncluder();
    }

    // unsigned int sectionStartLine, SymbolId sectionFile, unsigned int
    // originalLine, unsigned int type
    IncludeFileInfo info(1, fileId, m_pp->getSumLineCount() + 1, 1);
    m_pp->getSourceFile()->getIncludeFileInfo().push_back(info);
    openingIndex = m_pp->getSourceFile()->getIncludeFileInfo().size() - 1;

    PreprocessFile* pp = new PreprocessFile(
        fileId, m_pp, lineCol.first, m_pp->getCompileSourceFile(),
        m_instructions, m_pp->getCompilationUnit(), m_pp->getLibrary());
    m_pp->getCompileSourceFile()->registerPP(pp);
    if (!pp->preprocess()) {
      return;
    }

    std::string pre;
    std::string post;

    if (!m_pp->m_instructions.m_filterFileLine) {
      pre = "SLline 1 \"" + fileName + "\" 1\n";
      if (m_pp->getCompileSourceFile()
              ->getCommandLineParser()
              ->lineOffsetsAsComments()) {
        pre = "/* " + pre + " */";
      }

      if (m_pp->isMacroBody() && m_pp->getMacroInfo()) {
        MacroInfo* info = m_pp->getMacroInfo();
        if (m_pp->getCompileSourceFile()
                ->getCommandLineParser()
                ->lineOffsetsAsComments()) {
          post = "\n/* SLline " + std::to_string(info->m_line + lineCol.first) +
                 " \"" + getSymbolTable()->getSymbol(info->m_file) +
                 "\" 0 */\n";
        } else {
          post = "\nSLline " + std::to_string(info->m_line + lineCol.first) +
                 " \"" + getSymbolTable()->getSymbol(info->m_file) + "\" 0\n";
        }
      } else {
        if (m_pp->getCompileSourceFile()
                ->getCommandLineParser()
                ->lineOffsetsAsComments()) {
          post = "\n/* SLline " + std::to_string(lineCol.first + 1) + " \"" +
                 m_pp->getFileName(lineCol.first) + "\" 2 */\n";
        } else {
          post = "\nSLline " + std::to_string(lineCol.first + 1) + " \"" +
                 m_pp->getFileName(lineCol.first) + "\" 2\n";
        }
      }
    }
    std::string pp_result = pp->getPreProcessedFileContent();
    if (pp_result != "") m_pp->append(pre + pp_result + post);
    if (ctx->macro_instance()) {
      m_append_paused_context = ctx;
      m_pp->pauseAppend();
    }

    IncludeFileInfo infop(lineCol.first, m_pp->getFileId(lineCol.first),
                          m_pp->getSumLineCount() + 1, 2);
    infop.m_indexOpening = openingIndex;
    m_pp->getSourceFile()->getIncludeFileInfo().push_back(infop);
    if (openingIndex >= 0)
      m_pp->getSourceFile()->getIncludeFileInfo(openingIndex).m_indexClosing =
          m_pp->getSourceFile()->getIncludeFileInfo().size() - 1;
  }
}

void SV3_1aPpTreeShapeListener::exitInclude_directive(
    SV3_1aPpParser::Include_directiveContext* ctx) {
  if (m_append_paused_context == ctx) {
    m_append_paused_context = NULL;
    m_pp->resumeAppend();
  }
}

void SV3_1aPpTreeShapeListener::enterSimple_no_args_macro_definition(
    SV3_1aPpParser::Simple_no_args_macro_definitionContext* ctx) {
  if (m_inActiveBranch) {
    std::string macroName;
    if (ctx->Simple_identifier())
      macroName = ctx->Simple_identifier()->getText();
    else if (ctx->Escaped_identifier()) {
      macroName = ctx->Escaped_identifier()->getText();
      macroName.erase(0, 1);
      StringUtils::rtrim(macroName);
    }
    m_inMacroDefinitionParsing = true;
    SV3_1aPpParser::Simple_macro_definition_bodyContext* cBody =
        ctx->simple_macro_definition_body();
    std::vector<Token*> tokens = ParseUtils::getFlatTokenList(cBody);
    std::vector<std::string> body_tokens;
    for (auto token : tokens) {
      body_tokens.push_back(token->getText());
    }
    std::pair<int, int> lineCol = ParseUtils::getLineColumn(
        ctx->Simple_identifier() ? ctx->Simple_identifier()
                                 : ctx->Escaped_identifier());
    checkMultiplyDefinedMacro(macroName, ctx);
    m_pp->recordMacro(macroName, m_pp->getLineNb(lineCol.first), lineCol.second,
                      "", body_tokens);
  }
}

void SV3_1aPpTreeShapeListener::exitSimple_no_args_macro_definition(
    SV3_1aPpParser::Simple_no_args_macro_definitionContext* ctx) {
  m_inMacroDefinitionParsing = false;
}

void SV3_1aPpTreeShapeListener::enterMacroInstanceWithArgs(
    SV3_1aPpParser::MacroInstanceWithArgsContext* ctx) {
  if (m_inActiveBranch && (!m_inMacroDefinitionParsing)) {
    std::string macroName;
    if (ctx->Macro_identifier())
      macroName = ctx->Macro_identifier()->getText();
    else if (ctx->Macro_Escaped_identifier()) {
      macroName = ctx->Macro_Escaped_identifier()->getText();
      macroName.erase(0, 1);
      StringUtils::rtrim(macroName);
    }
    std::string macroArgs = ctx->macro_actual_args()->getText();
    std::vector<tree::ParseTree*> tokens =
        ParseUtils::getTopTokenList(ctx->macro_actual_args());
    std::vector<std::string> actualArgs;
    ParseUtils::tokenizeAtComma(actualArgs, tokens);
    macroName.erase(macroName.begin());
    std::string macroBody;
    int openingIndex = -1;
    std::pair<int, int> lineCol =
        ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
    if (!m_pp->isMacroBody()) {
      m_pp->getSourceFile()->m_loopChecker.clear();
    }

    MacroInfo* macroInf = m_pp->getMacro(macroName);
    if (macroInf) {
      IncludeFileInfo info(macroInf->m_line, macroInf->m_file,
                           m_pp->getSumLineCount(), 1);
      m_pp->getSourceFile()->getIncludeFileInfo().push_back(info);
      openingIndex = m_pp->getSourceFile()->getIncludeFileInfo().size() - 1;
      macroBody = m_pp->getMacro(macroName, actualArgs, m_pp, lineCol.first,
                                 m_pp->getSourceFile()->m_loopChecker,
                                 m_pp->m_instructions, macroInf->m_line,
                                 macroInf->m_file);
    } else {
      macroBody = m_pp->getMacro(macroName, actualArgs, m_pp, lineCol.first,
                                 m_pp->getSourceFile()->m_loopChecker,
                                 m_pp->m_instructions);
    }
    if (m_pp->m_debugMacro)
      std::cout << "FIND MACRO: " << macroName << " ARGS: " << macroArgs
                << " BODY: |" << macroBody << "|" << std::endl;
    if (macroBody == PreprocessFile::MacroNotDefined) {
      macroBody += ":" + macroName + "!!! ";
      logError(ErrorDefinition::PP_UNKOWN_MACRO, ctx, macroName, true);
    }
    std::string pre;
    std::string post;

    if (macroInf) {
      if (!m_pp->m_instructions.m_filterFileLine) {
        if (lineCol.second == 0) {
          pre = "SLline " + std::to_string(macroInf->m_line) + " \"" +
                getSymbolTable()->getSymbol(macroInf->m_file) + "\" 0";
          post = "SLline " + std::to_string(lineCol.first + 1) + " \"" +
                 m_pp->getFileName(lineCol.first) + "\" 0";
          if (m_pp->getCompileSourceFile()
                  ->getCommandLineParser()
                  ->lineOffsetsAsComments()) {
            pre = "/* " + pre + "*/";
            post = "/* " + post + "*/";
          } else {
            // Don't insert as parser does not know how to process this
            // directive in this lexical context
            pre = "";
            post = "";
          }
        }
      }
    }
    m_pp->append(pre + macroBody + post);
    // if (macroArgs.find('`') != std::string::npos)
    //  {
    if (m_append_paused_context == NULL) {
      m_append_paused_context = ctx;
      m_pp->pauseAppend();
    }
    //  }
    if (openingIndex >= 0) {
      SymbolId fileId = 0;
      unsigned int line = 0;
      if (m_pp->getEmbeddedMacroCallFile()) {
        fileId = m_pp->getEmbeddedMacroCallFile();
        line = m_pp->getEmbeddedMacroCallLine() + lineCol.first;
      } else {
        fileId = m_pp->getFileId(lineCol.first);
        line = lineCol.first;
      }
      IncludeFileInfo infop(line, fileId, m_pp->getSumLineCount(), 2);
      infop.m_indexOpening = openingIndex;
      m_pp->getSourceFile()->getIncludeFileInfo().push_back(infop);
      if (openingIndex >= 0)
        m_pp->getSourceFile()->getIncludeFileInfo(openingIndex).m_indexClosing =
            m_pp->getSourceFile()->getIncludeFileInfo().size() - 1;
    }
  }
}

void SV3_1aPpTreeShapeListener::exitMacroInstanceWithArgs(
    SV3_1aPpParser::MacroInstanceWithArgsContext* ctx) {
  if (m_append_paused_context == ctx) {
    m_append_paused_context = NULL;
    m_pp->resumeAppend();
  }
}

void SV3_1aPpTreeShapeListener::enterMacroInstanceNoArgs(
    SV3_1aPpParser::MacroInstanceNoArgsContext* ctx) {
  if (m_inActiveBranch && (!m_inMacroDefinitionParsing)) {
    std::string macroName;
    if (ctx->Macro_identifier())
      macroName = ctx->Macro_identifier()->getText();
    else if (ctx->Macro_Escaped_identifier()) {
      macroName = ctx->Macro_Escaped_identifier()->getText();
      macroName.erase(0, 1);
      StringUtils::rtrim(macroName);
    }
    macroName.erase(macroName.begin());
    std::pair<int, int> lineCol =
        ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
    std::vector<std::string> args;
    if (!m_pp->isMacroBody()) {
      m_pp->getSourceFile()->m_loopChecker.clear();
    }

    std::string macroBody;
    int openingIndex = -1;
    MacroInfo* macroInf = m_pp->getMacro(macroName);
    if (macroInf) {
      if (macroInf->m_type == MacroInfo::WITH_ARGS) {
        Location loc(m_pp->getFileId(lineCol.first),
                     m_pp->getLineNb(lineCol.first), 0,
                     getSymbolTable()->getId(macroName));
        Location extraLoc(macroInf->m_file, macroInf->m_line, 0);
        logError(ErrorDefinition::PP_MACRO_PARENTHESIS_NEEDED, loc, extraLoc);
      }

      IncludeFileInfo info(macroInf->m_line, macroInf->m_file,
                           m_pp->getSumLineCount(), 1);
      m_pp->getSourceFile()->getIncludeFileInfo().push_back(info);
      openingIndex = m_pp->getSourceFile()->getIncludeFileInfo().size() - 1;

      macroBody = m_pp->getMacro(macroName, args, m_pp, lineCol.first,
                                 m_pp->getSourceFile()->m_loopChecker,
                                 m_pp->m_instructions, macroInf->m_line,
                                 macroInf->m_file);
    } else {
      macroBody = m_pp->getMacro(macroName, args, m_pp, lineCol.first,
                                 m_pp->getSourceFile()->m_loopChecker,
                                 m_pp->m_instructions);
    }
    if (m_pp->m_debugMacro)
      std::cout << "FIND MACRO: " << macroName << ", BODY: |" << macroBody
                << "|" << std::endl;
    if ((macroBody == "") && m_instructions.m_mark_empty_macro) {
      macroBody = SymbolTable::getEmptyMacroMarker();
    }
    if (macroBody == PreprocessFile::MacroNotDefined) {
      macroBody += ":" + macroName + "!!! ";
      logError(ErrorDefinition::PP_UNKOWN_MACRO, ctx, macroName, true);
    }

    std::string pre;
    std::string post;

    if (macroInf) {
      if (!m_pp->m_instructions.m_filterFileLine) {
        if (lineCol.second == 0) {
          if (macroInf->m_file)
            pre = "SLline " + std::to_string(macroInf->m_line) + " \"" +
                  getSymbolTable()->getSymbol(macroInf->m_file) + "\" 0";
          post = "SLline " + std::to_string(lineCol.first + 1) + " \"" +
                 m_pp->getFileName(lineCol.first) + "\" 0";
          if (m_pp->getCompileSourceFile()
                  ->getCommandLineParser()
                  ->lineOffsetsAsComments()) {
            pre = "/* " + pre + "*/";
            post = "/* " + post + "*/";
          } else {
            // Don't insert as parser does not know how to process this
            // directive in this lexical context
            pre = "";
            post = "";
          }
        }
      }
    }
    m_pp->append(pre + macroBody + post);

    if (openingIndex >= 0) {
      SymbolId fileId = 0;
      unsigned int line = 0;
      if (m_pp->getEmbeddedMacroCallFile()) {
        fileId = m_pp->getEmbeddedMacroCallFile();
        line = m_pp->getEmbeddedMacroCallLine() + lineCol.first;
      } else {
        fileId = m_pp->getFileId(lineCol.first);
        line = lineCol.first;
      }
      IncludeFileInfo infop(line, fileId, m_pp->getSumLineCount(), 2);
      infop.m_indexOpening = openingIndex;
      m_pp->getSourceFile()->getIncludeFileInfo().push_back(infop);
      if (openingIndex >= 0)
        m_pp->getSourceFile()->getIncludeFileInfo(openingIndex).m_indexClosing =
            m_pp->getSourceFile()->getIncludeFileInfo().size() - 1;
    }
  }
}

void SV3_1aPpTreeShapeListener::enterPragma_directive(
    SV3_1aPpParser::Pragma_directiveContext* ctx) {
  std::string type;
  if (ctx->Simple_identifier()) type = ctx->Simple_identifier()->getText();
  bool endOfSection = false;
  if (type == "protect") {
    if (m_pp->getCompileSourceFile()
            ->getCommandLineParser()
            ->filterProtectedRegions()) {
      m_filterProtectedRegions = true;

      const std::vector<SV3_1aPpParser::Pragma_expressionContext*>& exprs =
          ctx->pragma_expression();
      for (auto expr : exprs) {
        if (expr->Simple_identifier()) {
          const std::string key = expr->Simple_identifier()->getText();
          if (key == "begin_protected") {
            m_inProtectedRegion = true;
            break;
          }
          if (key == "end_protected") {
            m_inProtectedRegion = false;
            endOfSection = true;
            break;
          }
        }
      }
    }
  }
  if ((!(m_filterProtectedRegions && m_inProtectedRegion)) && (!endOfSection)) {
    forwardToParser(ctx);
    m_pp->pauseAppend();
  }
}


void SV3_1aPpTreeShapeListener::exitPragma_directive(
    SV3_1aPpParser::Pragma_directiveContext* ctx) {
  if ((!(m_filterProtectedRegions && m_inProtectedRegion))) {
    m_pp->resumeAppend();
  }
}

// Helper function

void SV3_1aPpTreeShapeListener::setCurrentBranchActivity() {
  PreprocessFile::IfElseStack& stack = m_pp->getStack();
  if (stack.size()) {
    int index = stack.size() - 1;
    bool checkPrev = true;
    while (checkPrev) {
      PreprocessFile::IfElseItem& tmpitem = stack.at(index);
      switch (tmpitem.m_type) {
        case PreprocessFile::IfElseItem::IFDEF:
        case PreprocessFile::IfElseItem::IFNDEF:
          m_inActiveBranch = tmpitem.m_previousActiveState;
          checkPrev = false;
          break;
        default:
          checkPrev = true;
          index--;
          if (index < 0) checkPrev = false;
      }
    }

    index = stack.size() - 1;
    PreprocessFile::IfElseItem& tmpitem = stack.at(index);
    switch (tmpitem.m_type) {
      case PreprocessFile::IfElseItem::IFDEF: {
        if (!tmpitem.m_defined) {
          m_inActiveBranch = false;
        }
        break;
      }
      case PreprocessFile::IfElseItem::IFNDEF: {
        if (tmpitem.m_defined) {
          m_inActiveBranch = false;
        }
        break;
      }
      case PreprocessFile::IfElseItem::ELSIF:
      case PreprocessFile::IfElseItem::ELSE: {
        if (!tmpitem.m_defined) {
          m_inActiveBranch = false;
        }
        break;
      }
    }
  } else {
    m_inActiveBranch = true;
  }
}

// Helper function

bool SV3_1aPpTreeShapeListener::isPreviousBranchActive() {
  PreprocessFile::IfElseStack& stack = m_pp->getStack();
  bool previousBranchActive = false;
  bool checkPrev = true;
  if (stack.size() == 0) {
    return false;
  }
  int index = stack.size() - 1;
  while (checkPrev) {
    checkPrev = false;
    PreprocessFile::IfElseItem& tmpitem = stack.at(index);
    switch (tmpitem.m_type) {
      case PreprocessFile::IfElseItem::IFDEF:
        if (tmpitem.m_defined) {
          previousBranchActive = true;
        }
        checkPrev = false;
        break;
      case PreprocessFile::IfElseItem::ELSIF:
        if (tmpitem.m_defined) {
          previousBranchActive = true;
          checkPrev = false;
        } else {
          checkPrev = true;
        }
        break;
      case PreprocessFile::IfElseItem::IFNDEF:
        if (!tmpitem.m_defined) {
          previousBranchActive = true;
        }
        checkPrev = false;
        break;
      default:
        break;
    }
    if (index > 0) {
      index--;
    } else {
      if (checkPrev) previousBranchActive = false;
      checkPrev = false;
    }
  }
  return previousBranchActive;
}

void SV3_1aPpTreeShapeListener::enterSv_file_directive(
    SV3_1aPpParser::Sv_file_directiveContext* ctx) {
  if (m_inActiveBranch && (!m_inMacroDefinitionParsing)) {
    if (m_pp->getMacroInfo()) {
      m_pp->append(PreprocessFile::PP__File__Marking);
    } else {
      std::pair<int, int> lineCol =
          ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
      m_pp->append("\"" + m_pp->getFileName(lineCol.first) + "\"");
    }
  }
  m_pp->pauseAppend();
}
// void exitSv_file_directive(SV3_1aPpParser::Sv_file_directiveContext *
// /*ctx*/)  { }

void SV3_1aPpTreeShapeListener::enterSv_line_directive(
    SV3_1aPpParser::Sv_line_directiveContext* ctx) {
  if (m_inActiveBranch && (!m_inMacroDefinitionParsing)) {
    std::pair<int, int> lineCol =
        ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);

    if (m_pp->getMacroInfo()) {
      // Macro 1rst line + offset of directive within the macro -1
      // m_pp->append (std::to_string (m_pp->getLineNb(lineCol.first) +
      // m_pp->getMacroInfo()->m_line - 1));
      m_pp->append(PreprocessFile::PP__Line__Marking);
    } else {
      m_pp->append(std::to_string(m_pp->getLineNb(lineCol.first)));
    }
  }
  m_pp->pauseAppend();
}

void SV3_1aPpTreeShapeListener::enterLine_directive(
    SV3_1aPpParser::Line_directiveContext* ctx) {
  std::pair<int, int> lineCol =
      ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  std::string fileName;
  if (ctx->String()) fileName = ctx->String()->getText();
  if (fileName.size()) fileName = fileName.substr(1, fileName.size() - 2);
  std::string number;
  if (ctx->number().size()) number = ctx->number()[0]->getText();
  SymbolId newFileId = getSymbolTable()->registerSymbol(fileName);
  int currentLine = lineCol.first;
  int newLine = atoi(number.c_str());
  PreprocessFile::LineTranslationInfo info(newFileId, currentLine, newLine);
  m_pp->addLineTranslationInfo(info);
  m_pp->pauseAppend();
}

void SV3_1aPpTreeShapeListener::init() {
  m_reservedMacroNames = {"define",
                          "celldefine",
                          "endcelldefine",
                          "default_nettype",
                          "undef",
                          "ifdef",
                          "ifndef",
                          "else",
                          "elsif",
                          "endif",
                          "include",
                          "pragma",
                          "begin_keywords",
                          "end_keywords",
                          "resetall",
                          "timescale",
                          "unconnected_drive",
                          "nounconnected_drive",
                          "line",
                          "default_decay_time",
                          "default_trireg_strength",
                          "delay_mode_distributed",
                          "delay_mode_path",
                          "delay_mode_unit",
                          "delay_mode_zero",
                          "undefineall",
                          "accelerate",
                          "noaccelerate",
                          "protect",
                          "uselib",
                          "disable_portfaults",
                          "enable_portfaults",
                          "nosuppress_faults",
                          "suppress_faults",
                          "signed",
                          "unsigned",
                          "endprotect",
                          "protected",
                          "endprotected",
                          "expand_vectornets",
                          "noexpand_vectornets",
                          "autoexpand_vectornets",
                          "remove_gatename",
                          "noremove_gatenames",
                          "remove_netname",
                          "noremove_netnames"};

  for (std::vector<std::string>::iterator itr = m_reservedMacroNames.begin();
       itr != m_reservedMacroNames.end(); itr++) {
    m_reservedMacroNamesSet.insert(*itr);
    getSymbolTable()->registerSymbol(*itr);
  }
}

void SV3_1aPpTreeShapeListener::enterDefine_directive(
    SV3_1aPpParser::Define_directiveContext* ctx) {
  if (m_inActiveBranch) {
    std::string macroName;
    if (ctx->Simple_identifier())
      macroName = ctx->Simple_identifier()->getText();
    else if (ctx->Escaped_identifier()) {
      macroName = ctx->Escaped_identifier()->getText();
      macroName.erase(0, 1);
      StringUtils::rtrim(macroName);
    }
    if (m_reservedMacroNamesSet.find(macroName) !=
        m_reservedMacroNamesSet.end()) {
      logError(ErrorDefinition::PP_MACRO_NAME_RESERVED, ctx, macroName, 0);
    }
  }
}

void SV3_1aPpTreeShapeListener::exitDefine_directive(
    SV3_1aPpParser::Define_directiveContext* ctx) {
  if (m_inActiveBranch) {
    std::string macroName;
    if (ctx->Simple_identifier())
      macroName = ctx->Simple_identifier()->getText();
    else if (ctx->Escaped_identifier()) {
      macroName = ctx->Escaped_identifier()->getText();
      macroName.erase(0, 1);
      StringUtils::rtrim(macroName);
    }
    MacroInfo* macroInf = m_pp->getMacro(macroName);
    if (macroInf == NULL) {
      std::pair<int, int> lineCol = ParseUtils::getLineColumn(
          ctx->Simple_identifier() ? ctx->Simple_identifier()
                                   : ctx->Escaped_identifier());
      checkMultiplyDefinedMacro(macroName, ctx);
      std::vector<std::string> body_tokens;
      m_pp->recordMacro(macroName, m_pp->getLineNb(lineCol.first),
                        lineCol.second, "", body_tokens);
    }
  }
}

void SV3_1aPpTreeShapeListener::enterString(
    SV3_1aPpParser::StringContext* ctx) {
  std::string stringContent = ctx->getText();
  std::pair<int, int> lineCol =
      ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  bool escaped = false;
  for (unsigned int i = 1; i < stringContent.size() - 1; i++) {
    if (stringContent[i] == '"') {
      if (escaped == false) {
        std::string character;
        character += stringContent[i];
        Location loc(m_pp->getFileId(lineCol.first),
                     m_pp->getLineNb(lineCol.first), lineCol.second + i + 1,
                     getSymbolTable()->registerSymbol(character));
        logError(ErrorDefinition::PP_UNESCAPED_CHARACTER_IN_STRING, loc);
      }
    }
    if (stringContent[i] == '\\') {
      escaped = true;
      if (i == stringContent.size() - 2) {
        std::string character;
        character += stringContent[i];
        Location loc(m_pp->getFileId(lineCol.first),
                     m_pp->getLineNb(lineCol.first), lineCol.second + i + 1,
                     getSymbolTable()->registerSymbol(character));
        logError(ErrorDefinition::PP_UNRECOGNIZED_ESCAPED_SEQUENCE, loc);
      } else {
        if (stringContent[i + 1] == '\\') {
          i++;
          escaped = false;
          continue;
        }
        char sc = stringContent[i + 1];
        if ((sc != 'n') && (sc != '"') && (sc != '\\') && (sc != 't') &&
            (sc != 'v') && (sc != 'f') && (sc != 'a') && (sc != 'd') &&
            (sc != '%') && (sc != 'x') && (sc != '\n') && (sc != '0') &&
            (sc != 'r')) {
          std::string character = "\\";
          character += stringContent[i + 1];
          Location loc(m_pp->getFileId(lineCol.first),
                       m_pp->getLineNb(lineCol.first), lineCol.second + i + 1,
                       getSymbolTable()->registerSymbol(character));
          logError(ErrorDefinition::PP_UNRECOGNIZED_ESCAPED_SEQUENCE, loc);
        }
      }
    } else {
      escaped = false;
    }
  }
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    if (stringContent.find("`") != std::string::npos) {
      std::string stringData = stringContent;
      /* No macro substitution in strings (LRM)
      stringData.erase(0,1);
      stringData.erase(stringData.end() -1, stringData.end());
      stringContent = "\"" + m_pp->evaluateMacroInstance(stringData,m_pp,
      lineCol.first, PreprocessFile::SpecialInstructions::DontCheckLoop,
                                                         PreprocessFile::SpecialInstructions::AsIsUndefinedMacro
                                                         ) + "\"" ;
       */
      stringContent =
          std::regex_replace(stringContent, std::regex("``.``"), ".");
      stringContent =
          std::regex_replace(stringContent, std::regex("``-``"), "-");
    }
    m_pp->append(stringContent);
  }
}

void SV3_1aPpTreeShapeListener::enterEscaped_identifier(
    SV3_1aPpParser::Escaped_identifierContext* ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion))) {
    if (!m_inMacroDefinitionParsing) {
      std::string text = ctx->getText();
      std::string trunc;
      for (unsigned int i = 1; i < text.size() - 1; i++) trunc += text[i];
      m_pp->append(EscapeSequence + trunc + EscapeSequence);
    }
  }
}
