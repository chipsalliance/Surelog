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

SV3_1aPpTreeShapeListener::SV3_1aPpTreeShapeListener(PreprocessFile* pp,
        antlr4::CommonTokenStream* tokens,
        PreprocessFile::SpecialInstructions& instructions) :
	SV3_1aPpTreeListenerHelper::SV3_1aPpTreeListenerHelper(pp, instructions) {
  m_tokens = tokens;
}

void SV3_1aPpTreeShapeListener::enterTop_level_rule(
    SV3_1aPpParser::Top_level_ruleContext * /*ctx*/) {
  if (m_pp->getFileContent() == NULL) {
    m_fileContent = new FileContent(
        m_pp->getFileId(0), m_pp->getLibrary(),
        m_pp->getCompileSourceFile()->getSymbolTable(),
        m_pp->getCompileSourceFile()->getErrorContainer(), NULL, 0);
    m_pp->setFileContent(m_fileContent);
    m_pp->getCompileSourceFile()->getCompiler()->getDesign()->addPPFileContent(
        m_pp->getFileId(0), m_fileContent);
  } else {
    m_fileContent = m_pp->getFileContent();
  }
}

void SV3_1aPpTreeShapeListener::enterComments(
        SV3_1aPpParser::CommentsContext* ctx)
{
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
        SV3_1aPpParser::NumberContext* ctx)
{
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

void SV3_1aPpTreeShapeListener::exitDescription(SV3_1aPpParser::DescriptionContext * ctx) {
  if (ctx->text_blob()) {
    if (ctx->text_blob()->CR())
      addVObject (ctx, VObjectType::slText_blob);
    else if (ctx->text_blob()->Spaces())
      addVObject (ctx, VObjectType::slText_blob);
    else
      addVObject (ctx, ctx->getText(), VObjectType::slText_blob);
  } else {
    addVObject (ctx, ctx->getText(), VObjectType::slDescription);
  }
}


void SV3_1aPpTreeShapeListener::exitComments(SV3_1aPpParser::CommentsContext * ctx) {
  if (!m_pp->getCompileSourceFile()->getCommandLineParser()->filterComments()) {
    if (m_inActiveBranch &&
            (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
            (!m_inMacroDefinitionParsing)) {
      if (ctx->Block_comment()) {
        addVObject (ctx, ctx->Block_comment()->getText(), VObjectType::slComments);
      } else if (ctx->One_line_comment()) {
        addVObject (ctx, ctx->One_line_comment()->getText(), VObjectType::slComments);
      }
    } else {
      addLineFiller(ctx);
    }
  }
}

void SV3_1aPpTreeShapeListener::exitNumber(SV3_1aPpParser::NumberContext * ctx) {
 if (m_inActiveBranch &&
          (!(m_filterProtectedRegions && m_inProtectedRegion))) {
    if (!m_inMacroDefinitionParsing) {
      std::string text = ctx->Number()->getText();
      addVObject (ctx, text, VObjectType::slNumber);
    }
 }
}

void SV3_1aPpTreeShapeListener::exitEscaped_macro_definition_body(SV3_1aPpParser::Escaped_macro_definition_bodyContext * ctx) {
  addVObject (ctx, ctx->getText(), VObjectType::slText_blob);
}

void SV3_1aPpTreeShapeListener::exitSimple_macro_definition_body(SV3_1aPpParser::Simple_macro_definition_bodyContext * ctx) {
  addVObject (ctx, ctx->getText(), VObjectType::slText_blob);
}

void SV3_1aPpTreeShapeListener::exitPragma_expression(SV3_1aPpParser::Pragma_expressionContext * ctx) {
  addVObject (ctx, ctx->getText(), VObjectType::slPragma_expression);
}

void SV3_1aPpTreeShapeListener::exitMacro_arg(SV3_1aPpParser::Macro_argContext * ctx) {
  addVObject (ctx, ctx->getText(), VObjectType::slText_blob);
}

void SV3_1aPpTreeShapeListener::exitString_blob(SV3_1aPpParser::String_blobContext * ctx) {
  addVObject (ctx, ctx->getText(), VObjectType::slString);
}

void SV3_1aPpTreeShapeListener::exitDefault_value(SV3_1aPpParser::Default_valueContext * ctx) {
  addVObject (ctx, ctx->getText(), VObjectType::slText_blob);
}


void SV3_1aPpTreeShapeListener::enterUnterminated_string(
        SV3_1aPpParser::Unterminated_stringContext *ctx)
{
  std::string st = ctx->getText();
  if (m_pp->getMacroInfo() == nullptr)
    logError(ErrorDefinition::PP_UNTERMINATED_STRING, ctx, st, true);
  m_pp->append(st);
}

void SV3_1aPpTreeShapeListener::enterInclude_directive(
        SV3_1aPpParser::Include_directiveContext* ctx)
{
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
      pre = "`line 1 \"" + fileName + "\" 1\n";
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
          post = "\n`line " + std::to_string(info->m_line + lineCol.first) +
                  " \"" + getSymbolTable()->getSymbol(info->m_file) + "\" 0\n";
        }
      } else {
        if (m_pp->getCompileSourceFile()
                ->getCommandLineParser()
                ->lineOffsetsAsComments()) {
          post = "\n/* SLline " + std::to_string(lineCol.first + 1) + " \"" +
                  m_pp->getFileName(lineCol.first) + "\" 2 */\n";
        } else {
          post = "\n`line " + std::to_string(lineCol.first + 1) + " \"" +
                  m_pp->getFileName(lineCol.first) + "\" 2\n";
        }
      }
    }
    std::string pp_result = pp->getPreProcessedFileContent();
    if (!pp_result.empty()) m_pp->append(pre + pp_result + post);
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
        SV3_1aPpParser::Include_directiveContext* ctx)
{
  if (m_append_paused_context == ctx) {
    m_append_paused_context = NULL;
    m_pp->resumeAppend();
  }
  std::string text;
  if (ctx->Escaped_identifier()) {
    text = ctx->Escaped_identifier()->getText();
    addVObject((ParserRuleContext*) ctx->Escaped_identifier(), text, VObjectType::slEscaped_identifier);
  } else if (ctx->Simple_identifier()) {
    text = ctx->Simple_identifier()->getText();
    addVObject((ParserRuleContext*) ctx->Simple_identifier(), text, VObjectType::slPs_identifier);
  } else if (ctx->String()) {
    text = ctx->String()->getText();
    addVObject((ParserRuleContext*) ctx->String(), text, VObjectType::slString);
  }
  addVObject(ctx, VObjectType::slInclude_statement);

}

void SV3_1aPpTreeShapeListener::enterSimple_no_args_macro_definition(
        SV3_1aPpParser::Simple_no_args_macro_definitionContext* ctx)
{
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

    std::pair<int, int> lineCol = ParseUtils::getLineColumn(
            ctx->Simple_identifier() ? ctx->Simple_identifier()
            : ctx->Escaped_identifier());
    std::vector<Token*> tokens = ParseUtils::getFlatTokenList(cBody);
    std::vector<std::string> body_tokens;
    for (auto token : tokens) {
      body_tokens.push_back(token->getText());
    }


    checkMultiplyDefinedMacro(macroName, ctx);
    m_pp->recordMacro(macroName, m_pp->getLineNb(lineCol.first), lineCol.second,
            "", body_tokens);
    addLineFiller(ctx);
  } else {
    addLineFiller(ctx);
  }
}

void SV3_1aPpTreeShapeListener::exitSimple_no_args_macro_definition(
        SV3_1aPpParser::Simple_no_args_macro_definitionContext* ctx)
{
  m_inMacroDefinitionParsing = false;
  addVObject(ctx, VObjectType::slMacro_definition);
}

void SV3_1aPpTreeShapeListener::enterMacroInstanceWithArgs(
        SV3_1aPpParser::MacroInstanceWithArgsContext* ctx)
{
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
    int nbCRinArgs = std::count(macroArgs.begin(), macroArgs.end(),'\n');
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
              m_pp->getSumLineCount() + 1, 1);
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
          pre = "`line " + std::to_string(macroInf->m_line) + " \"" +
                  getSymbolTable()->getSymbol(macroInf->m_file) + "\" 0";
          post = "`line " + std::to_string(lineCol.first + 1) + " \"" +
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
    bool emptyMacroBody = false;
    if (macroBody.empty()) {
      emptyMacroBody = true;
      for (int i = 0; i < nbCRinArgs; i++)
        macroBody += "\n";
    }

    m_pp->append(pre + macroBody + post);
    
    if (m_append_paused_context == NULL) {
      m_append_paused_context = ctx;
      m_pp->pauseAppend();
    }
    
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
      int totalLineCount = m_pp->getSumLineCount() + 1;
      int origLine = line;
      if (emptyMacroBody) {
        if (nbCRinArgs)
          totalLineCount -= nbCRinArgs;
      }
      IncludeFileInfo infop(origLine, fileId, totalLineCount, 2);
      infop.m_indexOpening = openingIndex;
      m_pp->getSourceFile()->getIncludeFileInfo().push_back(infop);
      if (openingIndex >= 0)
        m_pp->getSourceFile()->getIncludeFileInfo(openingIndex).m_indexClosing =
            m_pp->getSourceFile()->getIncludeFileInfo().size() - 1;
    }
  }
}

void SV3_1aPpTreeShapeListener::exitMacroInstanceWithArgs(
        SV3_1aPpParser::MacroInstanceWithArgsContext* ctx)
{
  if (m_append_paused_context == ctx) {
    m_append_paused_context = NULL;
    m_pp->resumeAppend();
    addVObject(ctx, VObjectType::slMacroInstanceWithArgs);
  }
}

void SV3_1aPpTreeShapeListener::enterMacroInstanceNoArgs(
        SV3_1aPpParser::MacroInstanceNoArgsContext* ctx)
{
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
              m_pp->getSumLineCount() + 1, 1);
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
    if (macroBody.empty() && m_instructions.m_mark_empty_macro) {
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
            pre = "`line " + std::to_string(macroInf->m_line) + " \"" +
            getSymbolTable()->getSymbol(macroInf->m_file) + "\" 0";
          post = "`line " + std::to_string(lineCol.first + 1) + " \"" +
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
      int nbCRinMacroBody = std::count(macroBody.begin(), macroBody.end(),'\n');
      if (nbCRinMacroBody) {
        IncludeFileInfo infop(line, fileId, m_pp->getSumLineCount() + 1, 2);
        infop.m_indexOpening = openingIndex;
        m_pp->getSourceFile()->getIncludeFileInfo().push_back(infop);
        if (openingIndex >= 0)
          m_pp->getSourceFile()->getIncludeFileInfo(openingIndex).m_indexClosing =
              m_pp->getSourceFile()->getIncludeFileInfo().size() - 1;
      }
    }
  }
}

void SV3_1aPpTreeShapeListener::enterPragma_directive(
        SV3_1aPpParser::Pragma_directiveContext* ctx)
{
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
        SV3_1aPpParser::Pragma_directiveContext* ctx)
{
  if ((!(m_filterProtectedRegions && m_inProtectedRegion))) {
    m_pp->resumeAppend();
  }
}

void SV3_1aPpTreeShapeListener::enterSv_file_directive(
        SV3_1aPpParser::Sv_file_directiveContext* ctx)
{
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
// void SV3_1aPpTreeShapeListener::exitSv_file_directive(SV3_1aPpParser::Sv_file_directiveContext *
// /*ctx*/)  { }

void SV3_1aPpTreeShapeListener::enterSv_line_directive(
        SV3_1aPpParser::Sv_line_directiveContext* ctx)
{
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
        SV3_1aPpParser::Line_directiveContext* ctx)
{
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

void SV3_1aPpTreeShapeListener::enterDefine_directive(
        SV3_1aPpParser::Define_directiveContext* ctx)
{
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
        SV3_1aPpParser::Define_directiveContext* ctx)
{
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
      addLineFiller(ctx);
    }
  } else {
    addLineFiller(ctx);
  }
}

void SV3_1aPpTreeShapeListener::enterString(
        SV3_1aPpParser::StringContext* ctx)
{
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
        SV3_1aPpParser::Escaped_identifierContext* ctx)
{
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

void SV3_1aPpTreeShapeListener::enterSource_text(SV3_1aPpParser::Source_textContext * /*ctx*/)
{
  m_pp->getCompilationUnit()->setCurrentTimeInfo(m_pp->getFileId(0));
}

void SV3_1aPpTreeShapeListener::exitLine_directive(SV3_1aPpParser::Line_directiveContext * /*ctx*/)
{
  m_pp->resumeAppend();
}

void SV3_1aPpTreeShapeListener::enterDefault_nettype_directive(SV3_1aPpParser::Default_nettype_directiveContext * ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::exitSv_file_directive(SV3_1aPpParser::Sv_file_directiveContext * /*ctx*/)
{
  m_pp->resumeAppend();
}

void SV3_1aPpTreeShapeListener::exitSv_line_directive(SV3_1aPpParser::Sv_line_directiveContext * /*ctx*/)
{
  m_pp->resumeAppend();
}

void SV3_1aPpTreeShapeListener::enterTimescale_directive(SV3_1aPpParser::Timescale_directiveContext * ctx)
{
  if (m_pp->getCompilationUnit()->isInDesignElement()) {
    std::string directive = "`timescale";
    getSymbolTable()->registerSymbol(directive);
    logError(ErrorDefinition::PP_ILLEGAL_DIRECTIVE_IN_DESIGN_ELEMENT, ctx, directive);
  }
  forwardToParser(ctx);

  TimeInfo compUnitTimeInfo;
  compUnitTimeInfo.m_type = TimeInfo::Type::Timescale;
  compUnitTimeInfo.m_fileId = m_pp->getFileId(0);
  std::pair<int, int> lineCol = ParseUtils::getLineColumn(ctx->TIMESCALE());
  compUnitTimeInfo.m_line = lineCol.first;
  std::regex base_regex("[ ]*([0-9]+)([mnsupf]+)[ ]*/[ ]*([0-9]+)([mnsupf]+)[ ]*");
  std::smatch base_match;
  std::string value = ctx->TIMESCALE()->getText().c_str();
  if (std::regex_match(value, base_match, base_regex)) {
    std::ssub_match base1_sub_match = base_match[1];
    std::string base1 = base1_sub_match.str();
    compUnitTimeInfo.m_timeUnitValue = atoi(base1.c_str());
    compUnitTimeInfo.m_timeUnit = TimeInfo::unitFromString(base_match[2].str());
    std::ssub_match base2_sub_match = base_match[3];
    std::string base2 = base2_sub_match.str();
    compUnitTimeInfo.m_timePrecisionValue = atoi(base2.c_str());
    compUnitTimeInfo.m_timePrecision = TimeInfo::unitFromString(base_match[4].str());
  }
  m_pp->getCompilationUnit()->recordTimeInfo(compUnitTimeInfo);

}

void SV3_1aPpTreeShapeListener::enterUndef_directive(SV3_1aPpParser::Undef_directiveContext *ctx)
{
  std::string macroName;
  std::pair<int, int> lineCol = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (ctx->Simple_identifier())
    macroName = ctx->Simple_identifier()->getText();
  else if (ctx->Escaped_identifier()) {
    macroName = ctx->Escaped_identifier()->getText();
    macroName.erase(0, 1);
    StringUtils::rtrim(macroName);
  } else if (ctx->macro_instance()) {
    macroName = m_pp->evaluateMacroInstance(ctx->macro_instance()->getText(), m_pp, lineCol.first,
            PreprocessFile::SpecialInstructions::CheckLoop,
            PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  }
  if (m_pp->m_debugMacro) std::cout << "Undefining macro: " << macroName << std::endl;
  std::set<PreprocessFile*> visited;
  if (m_inActiveBranch && (!m_inMacroDefinitionParsing)) {
    bool found = m_pp->deleteMacro(macroName, visited);
    if (!found) {
      logError(ErrorDefinition::PP_UNDEF_UNKOWN_MACRO, ctx, macroName);
    }
  }
}

void SV3_1aPpTreeShapeListener::enterIfdef_directive(SV3_1aPpParser::Ifdef_directiveContext * ctx)
{
  PreprocessFile::IfElseItem item;
  std::string macroName;
  std::pair<int, int> lineCol = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (ctx->Simple_identifier())
    macroName = ctx->Simple_identifier()->getText();
  else if (ctx->Escaped_identifier()) {
    macroName = ctx->Escaped_identifier()->getText();
    macroName.erase(0, 1);
    StringUtils::rtrim(macroName);
  } else if (ctx->macro_instance()) {
    macroName = m_pp->evaluateMacroInstance(ctx->macro_instance()->getText(), m_pp, lineCol.first,
            PreprocessFile::SpecialInstructions::CheckLoop,
            PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  }
  item.m_macroName = macroName;
  std::vector<std::string> args;
  if (!m_pp->isMacroBody()) {
    m_pp->getSourceFile()->m_loopChecker.clear();
  }
  PreprocessFile::SpecialInstructions instr = m_pp->m_instructions;
  instr.m_evaluate = PreprocessFile::SpecialInstructions::DontEvaluate;
  std::string macroBody = m_pp->getMacro(item.m_macroName, args, m_pp, 0, m_pp->getSourceFile()->m_loopChecker, instr);
  item.m_defined = (macroBody != PreprocessFile::MacroNotDefined);
  item.m_type = PreprocessFile::IfElseItem::IFDEF;
  item.m_previousActiveState = m_inActiveBranch;
  m_pp->getStack().push_back(item);
  setCurrentBranchActivity(lineCol.first);
}

void SV3_1aPpTreeShapeListener::enterIfndef_directive(SV3_1aPpParser::Ifndef_directiveContext * ctx)
{
  PreprocessFile::IfElseItem item;
  std::string macroName;
  std::pair<int, int> lineCol = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (ctx->Simple_identifier())
    macroName = ctx->Simple_identifier()->getText();
  else if (ctx->Escaped_identifier()) {
    macroName = ctx->Escaped_identifier()->getText();
    macroName.erase(0, 1);
    StringUtils::rtrim(macroName);
  } else if (ctx->macro_instance()) {
    macroName = m_pp->evaluateMacroInstance(ctx->macro_instance()->getText(), m_pp, lineCol.first,
            PreprocessFile::SpecialInstructions::CheckLoop,
            PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  }
  item.m_macroName = macroName;
  std::vector<std::string> args;
  if (!m_pp->isMacroBody()) {
    m_pp->getSourceFile()->m_loopChecker.clear();
  }
  PreprocessFile::SpecialInstructions instr = m_pp->m_instructions;
  instr.m_evaluate = PreprocessFile::SpecialInstructions::DontEvaluate;
  std::string macroBody = m_pp->getMacro(item.m_macroName, args, m_pp, 0, m_pp->getSourceFile()->m_loopChecker, instr);
  item.m_defined = (macroBody != PreprocessFile::MacroNotDefined);
  item.m_type = PreprocessFile::IfElseItem::IFNDEF;
  item.m_previousActiveState = m_inActiveBranch;
  m_pp->getStack().push_back(item);
  setCurrentBranchActivity(lineCol.first);
}

void SV3_1aPpTreeShapeListener::enterElsif_directive(SV3_1aPpParser::Elsif_directiveContext * ctx)
{
  PreprocessFile::IfElseItem item;
  std::string macroName;
  std::pair<int, int> lineCol = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (ctx->Simple_identifier())
    macroName = ctx->Simple_identifier()->getText();
  else if (ctx->Escaped_identifier()) {
    macroName = ctx->Escaped_identifier()->getText();
    macroName.erase(0, 1);
    StringUtils::rtrim(macroName);
  } else if (ctx->macro_instance()) {
    macroName = m_pp->evaluateMacroInstance(ctx->macro_instance()->getText(), m_pp, lineCol.first,
            PreprocessFile::SpecialInstructions::CheckLoop,
            PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  }
  item.m_macroName = macroName;
  bool previousBranchActive = isPreviousBranchActive();
  std::vector<std::string> args;
  if (!m_pp->isMacroBody()) {
    m_pp->getSourceFile()->m_loopChecker.clear();
  }
  PreprocessFile::SpecialInstructions instr = m_pp->m_instructions;
  instr.m_evaluate = PreprocessFile::SpecialInstructions::DontEvaluate;
  std::string macroBody = m_pp->getMacro(item.m_macroName, args, m_pp, 0, m_pp->getSourceFile()->m_loopChecker, instr);
  item.m_defined = (macroBody != PreprocessFile::MacroNotDefined) && (!previousBranchActive);
  item.m_type = PreprocessFile::IfElseItem::ELSIF;
  m_pp->getStack().push_back(item);
  setCurrentBranchActivity(lineCol.first);
}

void SV3_1aPpTreeShapeListener::enterElse_directive(SV3_1aPpParser::Else_directiveContext * ctx)
{
  PreprocessFile::IfElseItem item;
  std::pair<int, int> lineCol = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  bool previousBranchActive = isPreviousBranchActive();
  item.m_defined = !previousBranchActive;
  item.m_type = PreprocessFile::IfElseItem::ELSE;
  m_pp->getStack().push_back(item);
  setCurrentBranchActivity(lineCol.first);
}

void SV3_1aPpTreeShapeListener::enterEndif_directive(SV3_1aPpParser::Endif_directiveContext * ctx)
{
  PreprocessFile::IfElseStack& stack = m_pp->getStack();
  std::pair<int, int> lineCol = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (stack.size()) {
    bool unroll = true;
    while (unroll) {
      PreprocessFile::IfElseItem& item = stack.back();
      switch (item.m_type) {
      case PreprocessFile::IfElseItem::IFDEF:
      case PreprocessFile::IfElseItem::IFNDEF:
        //std::cout << "STACK SIZE: " << m_pp->getStack ().size () << std::endl;
        m_inActiveBranch = item.m_previousActiveState;
        stack.pop_back();
        unroll = false;
        break;
      case PreprocessFile::IfElseItem::ELSIF:
      case PreprocessFile::IfElseItem::ELSE:
        stack.pop_back();
        break;
      default:
        break;
      }
    }
  }
  setCurrentBranchActivity(lineCol.first);
}

void SV3_1aPpTreeShapeListener::enterResetall_directive(SV3_1aPpParser::Resetall_directiveContext *ctx)
{
  if (m_pp->getCompilationUnit()->isInDesignElement()) {
    std::string directive = "`resetall";
    getSymbolTable()->registerSymbol(directive);
    logError(ErrorDefinition::PP_ILLEGAL_DIRECTIVE_IN_DESIGN_ELEMENT, ctx, directive);
  }
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterBegin_keywords_directive(SV3_1aPpParser::Begin_keywords_directiveContext * ctx)
{
  std::string version = ctx->String()->getText();
  if (version == "\"1364-1995\"") {
    m_pp->setVerilogVersion(Verilog1995);
  } else if (version == "\"1364-2001\"") {
    m_pp->setVerilogVersion(Verilog2001);
  } else if (version == "\"1364-2005\"") {
    m_pp->setVerilogVersion(Verilog2005);
  } else if (version == "\"1800-2005\"") {
    m_pp->setVerilogVersion(Verilog2005);
  } else if (version == "\"1800-2009\"") {
    m_pp->setVerilogVersion(Verilog2009);
  } else if (version == "\"1800-2012\"") {
    m_pp->setVerilogVersion(SystemVerilog);
  } else if (version == "\"1800-2017\"") {
    m_pp->setVerilogVersion(SystemVerilog);
  } else {
    logError(ErrorDefinition::PA_UNSUPPORTED_KEYWORD_LIST, ctx, version);
  }
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterEnd_keywords_directive(SV3_1aPpParser::End_keywords_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterCelldefine_directive(SV3_1aPpParser::Celldefine_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterEndcelldefine_directive(SV3_1aPpParser::Endcelldefine_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterProtect_directive(SV3_1aPpParser::Protect_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterEndprotect_directive(SV3_1aPpParser::Endprotect_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterProtected_directive(SV3_1aPpParser::Protected_directiveContext *ctx)
{
  m_inProtectedRegion = true;
  if (m_pp->getCompileSourceFile()->getCommandLineParser()->filterProtectedRegions()) {
    m_filterProtectedRegions = true;
  } else {
    forwardToParser(ctx);
  }
}

void SV3_1aPpTreeShapeListener::enterEndprotected_directive(SV3_1aPpParser::Endprotected_directiveContext *ctx)
{
  m_inProtectedRegion = false;
  if (!m_pp->getCompileSourceFile()->getCommandLineParser()->filterProtectedRegions())
    forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterExpand_vectornets_directive(SV3_1aPpParser::Expand_vectornets_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterNoexpand_vectornets_directive(SV3_1aPpParser::Noexpand_vectornets_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterAutoexpand_vectornets_directive(SV3_1aPpParser::Autoexpand_vectornets_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterUselib_directive(SV3_1aPpParser::Uselib_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDisable_portfaults_directive(SV3_1aPpParser::Disable_portfaults_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterEnable_portfaults_directive(SV3_1aPpParser::Enable_portfaults_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterNosuppress_faults_directive(SV3_1aPpParser::Nosuppress_faults_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterSuppress_faults_directive(SV3_1aPpParser::Suppress_faults_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterSigned_directive(SV3_1aPpParser::Signed_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterUnsigned_directive(SV3_1aPpParser::Unsigned_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterRemove_gatename_directive(SV3_1aPpParser::Remove_gatename_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterNoremove_gatenames_directive(SV3_1aPpParser::Noremove_gatenames_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterRemove_netname_directive(SV3_1aPpParser::Remove_netname_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterNoremove_netnames_directive(SV3_1aPpParser::Noremove_netnames_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterAccelerate_directive(SV3_1aPpParser::Accelerate_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterNoaccelerate_directive(SV3_1aPpParser::Noaccelerate_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDefault_trireg_strenght_directive(SV3_1aPpParser::Default_trireg_strenght_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDefault_decay_time_directive(SV3_1aPpParser::Default_decay_time_directiveContext *ctx)
{
  forwardToParser(ctx);
  m_pp->pauseAppend();
}

void SV3_1aPpTreeShapeListener::exitDefault_decay_time_directive(SV3_1aPpParser::Default_decay_time_directiveContext * /*ctx*/)
{
  m_pp->resumeAppend();
}

void SV3_1aPpTreeShapeListener::enterUnconnected_drive_directive(SV3_1aPpParser::Unconnected_drive_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterNounconnected_drive_directive(SV3_1aPpParser::Nounconnected_drive_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDelay_mode_distributed_directive(SV3_1aPpParser::Delay_mode_distributed_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDelay_mode_path_directive(SV3_1aPpParser::Delay_mode_path_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDelay_mode_unit_directive(SV3_1aPpParser::Delay_mode_unit_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDelay_mode_zero_directive(SV3_1aPpParser::Delay_mode_zero_directiveContext *ctx)
{
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterUndefineall_directive(SV3_1aPpParser::Undefineall_directiveContext * /*ctx*/)
{
  std::set<PreprocessFile*> visited;
  if (m_pp->m_debugMacro) std::cout << "Undefining all macros" << std::endl;
  m_pp->undefineAllMacros(visited);
}

void SV3_1aPpTreeShapeListener::enterMultiline_no_args_macro_definition(SV3_1aPpParser::Multiline_no_args_macro_definitionContext * ctx)
{
  if (m_inActiveBranch) {
    std::string macroName;
    if (ctx->Simple_identifier())
      macroName = ctx->Simple_identifier()->getText();
    else if (ctx->Escaped_identifier()) {
      macroName = ctx->Escaped_identifier()->getText();
      macroName.erase(0, 1);
      StringUtils::rtrim(macroName);
    }
    std::pair<int, int> lineCol = ParseUtils::getLineColumn(ctx->Simple_identifier() ? ctx->Simple_identifier() : ctx->Escaped_identifier());

    if (m_pp->m_debugMacro) std::cout << "Defining macro:" << macroName << std::endl;
    m_inMacroDefinitionParsing = true;
    SV3_1aPpParser::Escaped_macro_definition_bodyContext* cBody = ctx->escaped_macro_definition_body();
    std::vector<Token*> tokens = ParseUtils::getFlatTokenList(cBody);
    std::vector<std::string> body_tokens;
    for (auto token : tokens) {
      body_tokens.push_back(token->getText());
    }

    checkMultiplyDefinedMacro(macroName, ctx);

    m_pp->recordMacro(macroName, m_pp->getLineNb(lineCol.first), lineCol.second, "", body_tokens);
    addLineFiller(ctx);
  } else {
    addLineFiller(ctx);
  }
}

void SV3_1aPpTreeShapeListener::exitMultiline_no_args_macro_definition(SV3_1aPpParser::Multiline_no_args_macro_definitionContext *ctx)
{
  m_inMacroDefinitionParsing = false;
  addVObject(ctx, VObjectType::slMacro_definition);
}

void SV3_1aPpTreeShapeListener::enterMultiline_args_macro_definition(SV3_1aPpParser::Multiline_args_macro_definitionContext *ctx)
{
  if (m_inActiveBranch) {
    std::string macroName;
    if (ctx->Simple_identifier())
      macroName = ctx->Simple_identifier()->getText();
    else if (ctx->Escaped_identifier()) {
      macroName = ctx->Escaped_identifier()->getText();
      macroName.erase(0, 1);
      StringUtils::rtrim(macroName);
    }
    if (m_pp->m_debugMacro) std::cout << "Defining macro:" << macroName << std::endl;
    m_inMacroDefinitionParsing = true;
    SV3_1aPpParser::Escaped_macro_definition_bodyContext* cBody = ctx->escaped_macro_definition_body();
    std::string arguments = ctx->macro_arguments()->getText();
    std::vector<Token*> tokens = ParseUtils::getFlatTokenList(cBody);
    std::vector<std::string> body_tokens;
    for (auto token : tokens) {
      body_tokens.push_back(token->getText());
    }
    std::pair<int, int> lineCol = ParseUtils::getLineColumn(ctx->Simple_identifier() ? ctx->Simple_identifier() : ctx->Escaped_identifier());

    checkMultiplyDefinedMacro(macroName, ctx);
    m_pp->recordMacro(macroName, m_pp->getLineNb(lineCol.first), lineCol.second, arguments, body_tokens);
    addLineFiller(ctx);
  } else {
    addLineFiller(ctx);
  }
}

void SV3_1aPpTreeShapeListener::exitMultiline_args_macro_definition(SV3_1aPpParser::Multiline_args_macro_definitionContext *ctx)
{
  m_inMacroDefinitionParsing = false;
  addVObject(ctx, VObjectType::slMacro_definition);
}

void SV3_1aPpTreeShapeListener::enterSimple_args_macro_definition(SV3_1aPpParser::Simple_args_macro_definitionContext *ctx)
{
  if (m_inActiveBranch) {
    std::string macroName;
    if (ctx->Simple_identifier())
      macroName = ctx->Simple_identifier()->getText();
    else if (ctx->Escaped_identifier()) {
      macroName = ctx->Escaped_identifier()->getText();
      macroName.erase(0, 1);
      StringUtils::rtrim(macroName);
    }
    if (m_pp->m_debugMacro) std::cout << "Defining macro:" << macroName << std::endl;
    m_inMacroDefinitionParsing = true;
    //std::string wholeMacro = ctx->getText();
    SV3_1aPpParser::Simple_macro_definition_bodyContext* cBody = ctx->simple_macro_definition_body();
    std::string arguments = ctx->macro_arguments()->getText();
    std::vector<Token*> tokens = ParseUtils::getFlatTokenList(cBody);
    std::vector<std::string> body_tokens;
    for (auto token : tokens) {
      body_tokens.push_back(token->getText());
    }
    std::pair<int, int> lineCol = ParseUtils::getLineColumn(ctx->Simple_identifier() ? ctx->Simple_identifier() : ctx->Escaped_identifier());
    checkMultiplyDefinedMacro(macroName, ctx);
    m_pp->recordMacro(macroName, m_pp->getLineNb(lineCol.first), lineCol.second, arguments, body_tokens);
    addLineFiller(ctx);
  } else {
    addLineFiller(ctx);
  }
}

void SV3_1aPpTreeShapeListener::exitSimple_args_macro_definition(SV3_1aPpParser::Simple_args_macro_definitionContext *ctx)
{
  m_inMacroDefinitionParsing = false;
  addVObject(ctx, VObjectType::slMacro_definition);
}

void SV3_1aPpTreeShapeListener::enterText_blob(SV3_1aPpParser::Text_blobContext * ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion))) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
  } else {
    addLineFiller(ctx);
  }
}

void SV3_1aPpTreeShapeListener::exitText_blob(SV3_1aPpParser::Text_blobContext * ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion))) {

    if (ctx->Simple_identifier()) {
      addVObject(ctx, ctx->Simple_identifier()->getText(), VObjectType::slPs_identifier);
    } else if (ctx->number()) {
      addVObject(ctx, ctx->number()->getText(), VObjectType::slNumber);
    } else if (ctx->CR()) {
      addVObject(ctx, VObjectType::slCR);
    } else if (ctx->Spaces()) {
      addVObject(ctx, VObjectType::slSpaces);
    } else if (ctx->Fixed_point_number()) {
      addVObject(ctx, ctx->Fixed_point_number()->getText(), VObjectType::slNumber);
    } else if (ctx->ESCAPED_CR()) {
      addVObject(ctx, VObjectType::slEscapedCR);
    } else if (ctx->String()) {
      addVObject(ctx, ctx->ESCAPED_CR()->getText(), VObjectType::slString);
    } else if (ctx->PARENS_OPEN()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->PARENS_CLOSE()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->COMMA()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->EQUAL_OP()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->DOUBLE_QUOTE()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->Special()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->CURLY_OPEN()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->CURLY_CLOSE()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->SQUARE_OPEN()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->SQUARE_CLOSE()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->TICK_TICK()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->TICK_VARIABLE()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->TIMESCALE()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->ANY()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->pound_delay()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->pound_pound_delay()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->TICK_QUOTE()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->TICK_BACKSLASH_TICK_QUOTE()) {
      addVObject(ctx, ctx->getText(), VObjectType::slText_blob);
    } else if (ctx->TEXT_CR()) {
      addVObject(ctx, VObjectType::slCR);
    }
  }
}

void SV3_1aPpTreeShapeListener::enterModule(SV3_1aPpParser::ModuleContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndmodule(SV3_1aPpParser::EndmoduleContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterSv_interface(SV3_1aPpParser::Sv_interfaceContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndinterface(SV3_1aPpParser::EndinterfaceContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterProgram(SV3_1aPpParser::ProgramContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndprogram(SV3_1aPpParser::EndprogramContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterPrimitive(SV3_1aPpParser::PrimitiveContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndprimitive(SV3_1aPpParser::EndprimitiveContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion))&& (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterSv_package(SV3_1aPpParser::Sv_packageContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndpackage(SV3_1aPpParser::EndpackageContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterChecker(SV3_1aPpParser::CheckerContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndchecker(SV3_1aPpParser::EndcheckerContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterConfig(SV3_1aPpParser::ConfigContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndconfig(SV3_1aPpParser::EndconfigContext *ctx)
{
  if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterElseif_directive(SV3_1aPpParser::Elseif_directiveContext *ctx)
{
  logError(ErrorDefinition::PP_ILLEGAL_DIRECTIVE_ELSEIF, ctx, "");
}

void SV3_1aPpTreeShapeListener::enterEveryRule(antlr4::ParserRuleContext *ctx) {}
void SV3_1aPpTreeShapeListener::exitEveryRule(antlr4::ParserRuleContext *ctx) {}
void SV3_1aPpTreeShapeListener::visitTerminal(antlr4::tree::TerminalNode *node) {}
void SV3_1aPpTreeShapeListener::visitErrorNode(antlr4::tree::ErrorNode *node) {}
