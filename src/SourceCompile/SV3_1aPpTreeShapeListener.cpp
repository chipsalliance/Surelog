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

#include "Surelog/SourceCompile/SV3_1aPpTreeShapeListener.h"

#include <regex>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Design/Design.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/SourceCompile/CompilationUnit.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/MacroInfo.h"
#include "Surelog/SourceCompile/PreprocessFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Utils/ParseUtils.h"
#include "Surelog/Utils/StringUtils.h"

namespace SURELOG {

SV3_1aPpTreeShapeListener::SV3_1aPpTreeShapeListener(
    PreprocessFile *pp, antlr4::CommonTokenStream *tokens,
    PreprocessFile::SpecialInstructions &instructions)
    : SV3_1aPpTreeListenerHelper::SV3_1aPpTreeListenerHelper(pp, instructions,
                                                             tokens) {}

void SV3_1aPpTreeShapeListener::enterTop_level_rule(
    SV3_1aPpParser::Top_level_ruleContext * /*ctx*/) {
  // TODO: setting m_fileContent should happen at construction time.
  // This also makes it hard to know who the owner is.
  if (m_pp->getFileContent() == nullptr) {
    m_fileContent = new FileContent(
        m_pp->getFileId(0), m_pp->getLibrary(),
        m_pp->getCompileSourceFile()->getSymbolTable(),
        m_pp->getCompileSourceFile()->getErrorContainer(), nullptr, BadPathId);
    m_pp->setFileContent(m_fileContent);
    m_pp->getCompileSourceFile()->getCompiler()->getDesign()->addPPFileContent(
        m_pp->getFileId(0), m_fileContent);
  } else {
    m_fileContent = m_pp->getFileContent();
  }
}

void SV3_1aPpTreeShapeListener::enterComment(
    SV3_1aPpParser::CommentContext *ctx) {
  if (m_pp->getCompileSourceFile()
          ->getCommandLineParser()
          ->reportNonSynthesizable()) {
    if (ctx->One_line_comment()) {
      static const std::regex reg1(R"(\/\/\s*synopsys\s+translate_off\s*)");
      static const std::regex reg2(R"(\/\/\s*pragma\s+translate_off\s*)");
      const std::string &text = ctx->One_line_comment()->getText();
      if (std::regex_match(text, reg1) || std::regex_match(text, reg2)) {
        m_filterProtectedRegions = true;
        m_inProtectedRegion = true;
      }
    }
  }
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
  if (m_pp->getCompileSourceFile()
          ->getCommandLineParser()
          ->reportNonSynthesizable()) {
    if (ctx->One_line_comment()) {
      static const std::regex reg1(R"(\/\/\s*synopsys\s+translate_on\s*)");
      static const std::regex reg2(R"(\/\/\s*pragma\s+translate_on\s*)");
      const std::string &text = ctx->One_line_comment()->getText();
      if (std::regex_match(text, reg1) || std::regex_match(text, reg2)) {
        if (!m_pp->getCompileSourceFile()
                 ->getCommandLineParser()
                 ->filterProtectedRegions()) {
          m_filterProtectedRegions = false;
        }
        m_inProtectedRegion = false;
        addLineFiller(ctx);
      }
    }
  }
}

void SV3_1aPpTreeShapeListener::enterIntegral_number(
    SV3_1aPpParser::Integral_numberContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion))) {
    if (!m_inMacroDefinitionParsing) {
      std::string text;
      if (ctx->INTEGRAL_NUMBER()) {
        text = ctx->INTEGRAL_NUMBER()->getText();
      } else {
        text = ctx->getText();
      }
      std::string text2;
      bool firstNonSpace = false;
      uint32_t size = text.size();
      for (uint32_t i = 0; i < size; i++) {
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

void SV3_1aPpTreeShapeListener::exitDescription(
    SV3_1aPpParser::DescriptionContext *ctx) {
  if (ctx->text_blob()) {
    if (ctx->text_blob()->CR())
      addVObject(ctx, VObjectType::ppText_blob);
    else if (ctx->text_blob()->Spaces())
      addVObject(ctx, VObjectType::ppText_blob);
    else
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
  } else {
    addVObject(ctx, ctx->getText(), VObjectType::ppDescription);
  }
}

void SV3_1aPpTreeShapeListener::exitComment(
    SV3_1aPpParser::CommentContext *ctx) {
  if (!m_pp->getCompileSourceFile()->getCommandLineParser()->filterComments()) {
    if (m_inActiveBranch &&
        (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
        (!m_inMacroDefinitionParsing)) {
      if (ctx->Block_comment()) {
        addVObject(ctx, ctx->Block_comment()->getText(),
                   VObjectType::ppComment);
      } else if (ctx->One_line_comment()) {
        addVObject(ctx, ctx->One_line_comment()->getText(),
                   VObjectType::ppComment);
      }
    } else {
      addLineFiller(ctx);
    }
  }
}

void SV3_1aPpTreeShapeListener::exitIntegral_number(
    SV3_1aPpParser::Integral_numberContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion))) {
    if (!m_inMacroDefinitionParsing) {
      std::string text;
      if (ctx->INTEGRAL_NUMBER())
        text = ctx->INTEGRAL_NUMBER()->getText();
      else
        text = ctx->getText();
      addVObject(ctx, text, VObjectType::ppNumber);
    }
  }
}

void SV3_1aPpTreeShapeListener::exitEscaped_macro_definition_body(
    SV3_1aPpParser::Escaped_macro_definition_bodyContext *ctx) {
  addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
}

void SV3_1aPpTreeShapeListener::exitSimple_macro_definition_body(
    SV3_1aPpParser::Simple_macro_definition_bodyContext *ctx) {
  addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
}

void SV3_1aPpTreeShapeListener::exitPragma_expression(
    SV3_1aPpParser::Pragma_expressionContext *ctx) {
  addVObject(ctx, ctx->getText(), VObjectType::ppPragma_expression);
}

void SV3_1aPpTreeShapeListener::exitMacro_arg(
    SV3_1aPpParser::Macro_argContext *ctx) {
  addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
}

void SV3_1aPpTreeShapeListener::exitString_blob(
    SV3_1aPpParser::String_blobContext *ctx) {
  addVObject(ctx, ctx->getText(), VObjectType::ppString);
}

void SV3_1aPpTreeShapeListener::exitDefault_value(
    SV3_1aPpParser::Default_valueContext *ctx) {
  addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
}

void SV3_1aPpTreeShapeListener::enterUnterminated_string(
    SV3_1aPpParser::Unterminated_stringContext *ctx) {
  std::string st = ctx->getText();
  if (m_pp->getMacroInfo() == nullptr)
    logError(ErrorDefinition::PP_UNTERMINATED_STRING, ctx, st, true);
  m_pp->append(st);
}

void SV3_1aPpTreeShapeListener::enterInclude_directive(
    SV3_1aPpParser::Include_directiveContext *ctx) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  if (m_inActiveBranch && (!m_inMacroDefinitionParsing)) {
    ParseUtils::LineColumn startLineCol =
        ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
    ParseUtils::LineColumn endLineCol =
        ParseUtils::getEndLineColumn(m_pp->getTokenStream(), ctx);
    int32_t openingIndex = -1;
    std::string fileName;
    if (ctx->STRING()) {
      fileName = ctx->STRING()->getText();
      startLineCol = ParseUtils::getLineColumn(ctx->STRING());
      endLineCol = ParseUtils::getEndLineColumn(ctx->STRING());
    } else if (ctx->macro_instance()) {
      startLineCol = ParseUtils::getLineColumn(m_pp->getTokenStream(),
                                               ctx->macro_instance());
      endLineCol = ParseUtils::getEndLineColumn(m_pp->getTokenStream(),
                                                ctx->macro_instance());
      fileName = m_pp->evaluateMacroInstance(
          ctx->macro_instance()->getText(), m_pp, startLineCol.first,
          PreprocessFile::SpecialInstructions::CheckLoop,
          PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
    } else {
      Location loc(m_pp->getFileId(startLineCol.first),
                   m_pp->getLineNb(startLineCol.first), startLineCol.second);
      logError(ErrorDefinition::PP_INVALID_INCLUDE_FILENAME, loc);
      return;
    }

    fileName = StringUtils::unquoted(StringUtils::trim(fileName));
    if (m_pp->m_debugPP)
      std::cout << "PP INCLUDE DIRECTIVE " << fileName << std::endl;

    PathId fileId = fileSystem->locate(
        fileName,
        m_pp->getCompileSourceFile()->getCommandLineParser()->getIncludePaths(),
        getSymbolTable());
    if (!fileId) {
      // If failed to locate, then assume the same folder as the includer file
      // and let it fail down the stream.
      fileId = fileSystem->getSibling(m_pp->getCompileSourceFile()->getFileId(),
                                      fileName, getSymbolTable());
    }

    const std::string_view filePath = fileSystem->toPath(fileId);
    const SymbolId symbolId = getSymbolTable()->registerSymbol(fileName);

    if (m_pp->getCompileSourceFile()->getCommandLineParser()->verbose()) {
      Location loc(fileId);
      logError(ErrorDefinition::PP_PROCESSING_INCLUDE_FILE, loc, true);
    }

    // Detect include loop
    PreprocessFile *tmp = m_pp;
    while (tmp) {
      if (tmp->getFileId(0) == fileId) {
        Location loc(m_pp->getFileId(startLineCol.first), startLineCol.first,
                     startLineCol.second, (SymbolId)fileId);
        logError(ErrorDefinition::PP_RECURSIVE_INCLUDE_DIRECTIVE, loc, true);
        return;
      }
      tmp = tmp->getIncluder();
    }

    uint32_t lineSum = m_pp->getSumLineCount() + 1;
    openingIndex = m_pp->getSourceFile()->addIncludeFileInfo(
        /* context */ IncludeFileInfo::Context::INCLUDE,
        /* sectionStartLine*/ 1, /* sectionSymbolId */ symbolId,
        /* sectionFileId */ fileId,
        /* originalStartLine */ lineSum,
        /* originalStartColumn */ startLineCol.second,
        /* originalEndLine */ lineSum + (endLineCol.first - startLineCol.first),
        /* originalEndColumn */ endLineCol.second,
        /* action */ IncludeFileInfo::Action::PUSH);

    PreprocessFile *pp =
        new PreprocessFile(fileId, m_pp->getCompileSourceFile(), m_instructions,
                           m_pp->getCompilationUnit(), m_pp->getLibrary(), m_pp,
                           startLineCol.first);
    m_pp->getCompileSourceFile()->registerPP(pp);
    if (!pp->preprocess()) {
      return;
    }

    std::string pre;
    std::string post;

    if (!m_pp->m_instructions.m_filterFileLine) {
      pre = StrCat("`line 1 \"", filePath, "\" 1\n");
      if (m_pp->getCompileSourceFile()
              ->getCommandLineParser()
              ->lineOffsetsAsComments()) {
        pre = "/* " + pre + " */";
      }

      if (m_pp->isMacroBody() && m_pp->getMacroInfo()) {
        MacroInfo *info = m_pp->getMacroInfo();
        if (m_pp->getCompileSourceFile()
                ->getCommandLineParser()
                ->lineOffsetsAsComments()) {
          post = StrCat("\n/* SLline ", info->m_startLine + startLineCol.first,
                        R"( ""^")", fileSystem->toPath(info->m_fileId),
                        "\" 0 */\n");
        } else {
          post = StrCat("\n`line ", info->m_startLine + startLineCol.first,
                        " \"", fileSystem->toPath(info->m_fileId), "\" 0\n");
        }
      } else {
        if (m_pp->getCompileSourceFile()
                ->getCommandLineParser()
                ->lineOffsetsAsComments()) {
          post = StrCat("\n/* SLline ", startLineCol.first + 1, R"( ""^")",
                        fileSystem->toPath(m_pp->getFileId(startLineCol.first)),
                        "\" 2 */\n");
        } else {
          post = StrCat("\n`line ", startLineCol.first + 1, " \"",
                        fileSystem->toPath(m_pp->getFileId(startLineCol.first)),
                        "\" 2\n");
        }
      }
    }
    std::string pp_result = pp->getPreProcessedFileContent();
    if (!pp_result.empty()) m_pp->append(pre + pp_result + post);
    if (ctx->macro_instance()) {
      m_append_paused_context = ctx;
      m_pp->pauseAppend();
    }

    lineSum = m_pp->getSumLineCount() + 1;
    int32_t closingIndex = m_pp->getSourceFile()->addIncludeFileInfo(
        /* context */ IncludeFileInfo::Context::INCLUDE,
        /* sectionStartLine */ startLineCol.first,
        /* sectionSymbolId */ BadSymbolId,
        /* sectionFileId */ m_pp->getFileId(startLineCol.first),
        /* originalStartLine */ lineSum,
        /* originalStartColumn */ startLineCol.second,
        /* originalEndLine */ lineSum + (endLineCol.first - startLineCol.first),
        /* originalEndColumn */ endLineCol.second,
        /* action */ IncludeFileInfo::Action::POP, openingIndex, 0);
    if (openingIndex >= 0) {
      m_pp->getSourceFile()->getIncludeFileInfo(openingIndex).m_indexClosing =
          closingIndex;
    }
  }
}

void SV3_1aPpTreeShapeListener::exitInclude_directive(
    SV3_1aPpParser::Include_directiveContext *ctx) {
  if (m_append_paused_context == ctx) {
    m_append_paused_context = nullptr;
    m_pp->resumeAppend();
  }
  std::string text;
  if (ctx->ESCAPED_IDENTIFIER()) {
    text = ctx->ESCAPED_IDENTIFIER()->getText();
    addVObject((antlr4::ParserRuleContext *)ctx->ESCAPED_IDENTIFIER(), text,
               VObjectType::ppEscaped_identifier);
  } else if (ctx->Simple_identifier()) {
    text = ctx->Simple_identifier()->getText();
    addVObject((antlr4::ParserRuleContext *)ctx->Simple_identifier(), text,
               VObjectType::ppPs_identifier);
  } else if (ctx->STRING()) {
    text = ctx->STRING()->getText();
    addVObject((antlr4::ParserRuleContext *)ctx->STRING(), text,
               VObjectType::ppString);
  }
  addVObject(ctx, VObjectType::ppInclude_directive);
}

void SV3_1aPpTreeShapeListener::enterSimple_no_args_macro_definition(
    SV3_1aPpParser::Simple_no_args_macro_definitionContext *ctx) {
  if (m_inActiveBranch) {
    std::string macroName;
    if (ctx->Simple_identifier())
      macroName = ctx->Simple_identifier()->getText();
    else if (ctx->ESCAPED_IDENTIFIER()) {
      macroName = ctx->ESCAPED_IDENTIFIER()->getText();
      macroName.erase(0, 1);
      macroName = StringUtils::rtrim(macroName);
    }
    if (m_reservedMacroNamesSet.find(macroName) !=
        m_reservedMacroNamesSet.end()) {
      logError(ErrorDefinition::PP_MACRO_NAME_RESERVED, ctx, macroName, 0);
    }
    m_inMacroDefinitionParsing = true;
    SV3_1aPpParser::Simple_macro_definition_bodyContext *cBody =
        ctx->simple_macro_definition_body();

    antlr4::tree::TerminalNode *const identifier =
        ctx->Simple_identifier() ? ctx->Simple_identifier()
                                 : ctx->ESCAPED_IDENTIFIER();
    ParseUtils::LineColumn startLineCol = ParseUtils::getLineColumn(identifier);
    ParseUtils::LineColumn endLineCol =
        ParseUtils::getEndLineColumn(identifier);
    std::vector<antlr4::Token *> tokens = ParseUtils::getFlatTokenList(cBody);
    std::vector<std::string> body_tokens;
    body_tokens.reserve(tokens.size());
    for (auto token : tokens) {
      body_tokens.push_back(token->getText());
    }

    checkMultiplyDefinedMacro(macroName, ctx);
    m_pp->recordMacro(macroName, m_pp->getLineNb(startLineCol.first),
                      startLineCol.second,
                      m_pp->getLineNb(startLineCol.first) +
                          (endLineCol.first - startLineCol.first),
                      endLineCol.second, "", body_tokens);
    addLineFiller(ctx);
  } else {
    addLineFiller(ctx);
  }
}

void SV3_1aPpTreeShapeListener::exitSimple_no_args_macro_definition(
    SV3_1aPpParser::Simple_no_args_macro_definitionContext *ctx) {
  m_inMacroDefinitionParsing = false;
  addVObject(ctx, VObjectType::ppMacro_definition);
}

void SV3_1aPpTreeShapeListener::enterMacroInstanceWithArgs(
    SV3_1aPpParser::MacroInstanceWithArgsContext *ctx) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  if (m_filterProtectedRegions && m_inProtectedRegion) {
    return;
  }
  if (m_inActiveBranch && (!m_inMacroDefinitionParsing)) {
    ParseUtils::LineColumn startLineCol =
        ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
    ParseUtils::LineColumn endLineCol =
        ParseUtils::getEndLineColumn(m_pp->getTokenStream(), ctx);
    std::string macroName;
    if (ctx->Macro_identifier()) {
      macroName = ctx->Macro_identifier()->getText();
      startLineCol = ParseUtils::getLineColumn(ctx->Macro_identifier());
      endLineCol = ParseUtils::getEndLineColumn(ctx->Macro_identifier());
    } else if (ctx->Macro_Escaped_identifier()) {
      macroName = ctx->Macro_Escaped_identifier()->getText();
      macroName.erase(0, 1);
      macroName = StringUtils::rtrim(macroName);
      startLineCol = ParseUtils::getLineColumn(ctx->Macro_Escaped_identifier());
      endLineCol =
          ParseUtils::getEndLineColumn(ctx->Macro_Escaped_identifier());
    }
    std::string macroArgs = ctx->macro_actual_args()->getText();
    int32_t nbCRinArgs = std::count(macroArgs.begin(), macroArgs.end(), '\n');
    std::vector<antlr4::tree::ParseTree *> tokens =
        ParseUtils::getTopTokenList(ctx->macro_actual_args());
    std::vector<std::string> actualArgs;
    ParseUtils::tokenizeAtComma(actualArgs, tokens);
    macroName.erase(macroName.begin());
    std::string macroBody;
    int32_t openingIndex = -1;
    if (!m_pp->isMacroBody()) {
      m_pp->getSourceFile()->m_loopChecker.clear();
    }

    MacroInfo *macroInf = m_pp->getMacro(macroName);
    if (macroInf) {
      uint32_t lineSum = m_pp->getSumLineCount() + 1;
      openingIndex = m_pp->getSourceFile()->addIncludeFileInfo(
          IncludeFileInfo::Context::MACRO, macroInf->m_startLine, BadSymbolId,
          macroInf->m_fileId, lineSum, startLineCol.second,
          lineSum + (endLineCol.first - startLineCol.first), endLineCol.second,
          IncludeFileInfo::Action::PUSH);
      macroBody = m_pp->getMacro(
          macroName, actualArgs, m_pp, startLineCol.first,
          m_pp->getSourceFile()->m_loopChecker, m_pp->m_instructions,
          macroInf->m_startLine, macroInf->m_fileId);
    } else {
      macroBody = m_pp->getMacro(
          macroName, actualArgs, m_pp, startLineCol.first,
          m_pp->getSourceFile()->m_loopChecker, m_pp->m_instructions);
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
        if (startLineCol.second == 0) {
          pre = StrCat("`line ", macroInf->m_startLine, " \"",
                       fileSystem->toPath(macroInf->m_fileId), "\" 0");
          post = StrCat("`line ", startLineCol.first + 1, " \"",
                        fileSystem->toPath(m_pp->getFileId(startLineCol.first)),
                        "\" 0");
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
      macroBody.append(nbCRinArgs, '\n');
    }

    m_pp->append(pre + macroBody + post);

    if (m_append_paused_context == nullptr) {
      m_append_paused_context = ctx;
      m_pp->pauseAppend();
    }

    if (openingIndex >= 0) {
      PathId fileId;
      uint32_t line = 0;
      if (m_pp->getEmbeddedMacroCallFile()) {
        fileId = m_pp->getEmbeddedMacroCallFile();
        line = m_pp->getEmbeddedMacroCallLine() + startLineCol.first;
      } else {
        fileId = m_pp->getFileId(startLineCol.first);
        line = startLineCol.first;
      }
      uint32_t lineSum = m_pp->getSumLineCount() + 1;
      int32_t origLine = line;
      int32_t closingIndex = -1;
      if (emptyMacroBody) {
        if (nbCRinArgs) lineSum -= nbCRinArgs;

        closingIndex = m_pp->getSourceFile()->addIncludeFileInfo(
            IncludeFileInfo::Context::MACRO, origLine, BadSymbolId, fileId,
            lineSum, startLineCol.second,
            lineSum + (endLineCol.first - startLineCol.first),
            endLineCol.second, IncludeFileInfo::Action::POP, openingIndex, 0);
      } else {
        closingIndex = m_pp->getSourceFile()->addIncludeFileInfo(
            IncludeFileInfo::Context::MACRO, origLine + nbCRinArgs, BadSymbolId,
            fileId, lineSum, startLineCol.second,
            lineSum + (endLineCol.first - startLineCol.first),
            endLineCol.second, IncludeFileInfo::Action::POP, openingIndex, 0);
      }
      if (openingIndex >= 0) {
        m_pp->getSourceFile()->getIncludeFileInfo(openingIndex).m_indexClosing =
            closingIndex;
      }
    }
  } else if ((!m_inActiveBranch) && (!m_inMacroDefinitionParsing)) {
    std::string macroArgs = ctx->macro_actual_args()->getText();
    int32_t nbCRinArgs = std::count(macroArgs.begin(), macroArgs.end(), '\n');
    m_pp->append(std::string(nbCRinArgs, '\n'));
  }
}

void SV3_1aPpTreeShapeListener::exitMacroInstanceWithArgs(
    SV3_1aPpParser::MacroInstanceWithArgsContext *ctx) {
  if (m_filterProtectedRegions && m_inProtectedRegion) {
    return;
  }
  if (m_append_paused_context == ctx) {
    m_append_paused_context = nullptr;
    m_pp->resumeAppend();
    addVObject(ctx, VObjectType::ppMacroInstanceWithArgs);
  }
}

void SV3_1aPpTreeShapeListener::enterMacroInstanceNoArgs(
    SV3_1aPpParser::MacroInstanceNoArgsContext *ctx) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  if (m_filterProtectedRegions && m_inProtectedRegion) {
    return;
  }
  if (m_inActiveBranch && (!m_inMacroDefinitionParsing)) {
    std::string macroName;
    ParseUtils::LineColumn startLineCol =
        ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
    ParseUtils::LineColumn endLineCol =
        ParseUtils::getEndLineColumn(m_pp->getTokenStream(), ctx);
    if (ctx->Macro_identifier()) {
      macroName = ctx->Macro_identifier()->getText();
      startLineCol = ParseUtils::getLineColumn(ctx->Macro_identifier());
      endLineCol = ParseUtils::getEndLineColumn(ctx->Macro_identifier());
    } else if (ctx->Macro_Escaped_identifier()) {
      macroName = ctx->Macro_Escaped_identifier()->getText();
      macroName.erase(0, 1);
      macroName = StringUtils::rtrim(macroName);
      startLineCol = ParseUtils::getLineColumn(ctx->Macro_Escaped_identifier());
      endLineCol =
          ParseUtils::getEndLineColumn(ctx->Macro_Escaped_identifier());
    }
    macroName.erase(macroName.begin());
    std::vector<std::string> args;
    if (!m_pp->isMacroBody()) {
      m_pp->getSourceFile()->m_loopChecker.clear();
    }

    std::string macroBody;
    int32_t openingIndex = -1;
    MacroInfo *macroInf = m_pp->getMacro(macroName);
    if (macroInf) {
      if (macroInf->m_type == MacroInfo::WITH_ARGS) {
        Location loc(m_pp->getFileId(startLineCol.first),
                     m_pp->getLineNb(startLineCol.first), startLineCol.second,
                     getSymbolTable()->getId(macroName));
        Location extraLoc(macroInf->m_fileId, macroInf->m_startLine,
                          macroInf->m_startColumn);
        logError(ErrorDefinition::PP_MACRO_PARENTHESIS_NEEDED, loc, extraLoc);
      }

      uint32_t lineSum = m_pp->getSumLineCount() + 1;
      openingIndex = m_pp->getSourceFile()->addIncludeFileInfo(
          IncludeFileInfo::Context::MACRO, macroInf->m_startLine, BadSymbolId,
          macroInf->m_fileId, lineSum, startLineCol.second,
          lineSum + (endLineCol.first - startLineCol.first), endLineCol.second,
          IncludeFileInfo::Action::PUSH);
      macroBody = m_pp->getMacro(macroName, args, m_pp, startLineCol.first,
                                 m_pp->getSourceFile()->m_loopChecker,
                                 m_pp->m_instructions, macroInf->m_startLine,
                                 macroInf->m_fileId);
    } else {
      macroBody = m_pp->getMacro(macroName, args, m_pp, startLineCol.first,
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
        if (startLineCol.second == 0) {
          if (macroInf->m_fileId)
            pre = StrCat("`line ", macroInf->m_startLine, " \"",
                         fileSystem->toPath(macroInf->m_fileId), "\" 0");
          post = StrCat("`line ", startLineCol.first + 1, " \"",
                        fileSystem->toPath(m_pp->getFileId(startLineCol.first)),
                        "\" 0");
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
      PathId fileId;
      uint32_t line = 0;
      if (m_pp->getEmbeddedMacroCallFile()) {
        fileId = m_pp->getEmbeddedMacroCallFile();
        line = m_pp->getEmbeddedMacroCallLine() + startLineCol.first;
      } else {
        fileId = m_pp->getFileId(startLineCol.first);
        line = startLineCol.first;
      }
      int32_t nbCRinMacroBody =
          std::count(macroBody.begin(), macroBody.end(), '\n');
      if (nbCRinMacroBody) {
        uint32_t lineSum = m_pp->getSumLineCount() + 1;
        int32_t closingIndex = m_pp->getSourceFile()->addIncludeFileInfo(
            IncludeFileInfo::Context::MACRO, line, BadSymbolId, fileId, lineSum,
            startLineCol.first,
            lineSum + (endLineCol.first - startLineCol.first),
            endLineCol.second, IncludeFileInfo::Action::POP, openingIndex, 0);
        if (openingIndex >= 0) {
          m_pp->getSourceFile()
              ->getIncludeFileInfo(openingIndex)
              .m_indexClosing = closingIndex;
        }
      }
    }
  }
}

void SV3_1aPpTreeShapeListener::enterPragma_directive(
    SV3_1aPpParser::Pragma_directiveContext *ctx) {
  std::string type;
  if (ctx->Simple_identifier()) type = ctx->Simple_identifier()->getText();
  bool endOfSection = false;
  if (type == "protect") {
    if (m_pp->getCompileSourceFile()
            ->getCommandLineParser()
            ->filterProtectedRegions()) {
      m_filterProtectedRegions = true;

      const std::vector<SV3_1aPpParser::Pragma_expressionContext *> &exprs =
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
    SV3_1aPpParser::Pragma_directiveContext *ctx) {
  if ((!(m_filterProtectedRegions && m_inProtectedRegion))) {
    m_pp->resumeAppend();
  }
}

void SV3_1aPpTreeShapeListener::enterSv_file_directive(
    SV3_1aPpParser::Sv_file_directiveContext *ctx) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  if (m_inActiveBranch && (!m_inMacroDefinitionParsing)) {
    if (m_pp->getMacroInfo()) {
      m_pp->append(PreprocessFile::PP__File__Marking);
    } else {
      ParseUtils::LineColumn lineCol =
          ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
      m_pp->append(StrCat(
          "\"", fileSystem->toPath(m_pp->getFileId(lineCol.first)), "\""));
    }
  }
  m_pp->pauseAppend();
}

void SV3_1aPpTreeShapeListener::enterSv_line_directive(
    SV3_1aPpParser::Sv_line_directiveContext *ctx) {
  if (m_inActiveBranch && (!m_inMacroDefinitionParsing)) {
    ParseUtils::LineColumn lineCol =
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
    SV3_1aPpParser::Line_directiveContext *ctx) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  ParseUtils::LineColumn lineCol =
      ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  PathId newFileId;
  if (ctx->STRING()) {
    std::string fileName(StringUtils::unquoted(ctx->STRING()->getText()));
    newFileId = fileSystem->locate(
        fileName,
        m_pp->getCompileSourceFile()->getCommandLineParser()->getIncludePaths(),
        getSymbolTable());
    if (!newFileId) {
      // If failed to locate, then assume the same folder as the includer file
      // and let it fail down the stream.
      newFileId =
          fileSystem->getSibling(m_pp->getCompileSourceFile()->getFileId(),
                                 fileName, getSymbolTable());
    }
  }
  std::string number;
  if (!ctx->integral_number().empty())
    number = ctx->integral_number()[0]->getText();
  if (ctx->integral_number().size() > 1) {
    std::string type = ctx->integral_number()[1]->getText();
    int32_t newType = atoi(type.c_str());
    if (newType < 0 || newType > 2) {
      Location loc(m_pp->getFileId(lineCol.first),
                   m_pp->getLineNb(lineCol.first), lineCol.second,
                   getSymbolTable()->registerSymbol(type));
      logError(ErrorDefinition::PP_ILLEGAL_TICK_LINE_VALUE, loc);
    }
  }
  int32_t currentLine = lineCol.first;
  int32_t newLine = atoi(number.c_str());
  PreprocessFile::LineTranslationInfo info(newFileId, currentLine, newLine);
  m_pp->addLineTranslationInfo(info);
  m_pp->pauseAppend();
}

void SV3_1aPpTreeShapeListener::enterDefine_directive(
    SV3_1aPpParser::Define_directiveContext *ctx) {
  if (m_inActiveBranch) {
    std::string macroName;
    if (ctx->Simple_identifier())
      macroName = ctx->Simple_identifier()->getText();
    else if (ctx->ESCAPED_IDENTIFIER()) {
      macroName = ctx->ESCAPED_IDENTIFIER()->getText();
      macroName.erase(0, 1);
      macroName = StringUtils::rtrim(macroName);
    }
    if (m_reservedMacroNamesSet.find(macroName) !=
        m_reservedMacroNamesSet.end()) {
      logError(ErrorDefinition::PP_MACRO_NAME_RESERVED, ctx, macroName, 0);
    }
  }
}

void SV3_1aPpTreeShapeListener::exitDefine_directive(
    SV3_1aPpParser::Define_directiveContext *ctx) {
  if (m_inActiveBranch) {
    std::string macroName;
    if (ctx->Simple_identifier())
      macroName = ctx->Simple_identifier()->getText();
    else if (ctx->ESCAPED_IDENTIFIER()) {
      macroName = ctx->ESCAPED_IDENTIFIER()->getText();
      macroName.erase(0, 1);
      macroName = StringUtils::rtrim(macroName);
    }
    MacroInfo *macroInf = m_pp->getMacro(macroName);
    if (macroInf == nullptr) {
      antlr4::tree::TerminalNode *const identifier =
          ctx->Simple_identifier() ? ctx->Simple_identifier()
                                   : ctx->ESCAPED_IDENTIFIER();
      ParseUtils::LineColumn startLineCol =
          ParseUtils::getLineColumn(identifier);
      ParseUtils::LineColumn endLineCol =
          ParseUtils::getEndLineColumn(identifier);
      checkMultiplyDefinedMacro(macroName, ctx);
      std::vector<std::string> body_tokens;
      m_pp->recordMacro(macroName, m_pp->getLineNb(startLineCol.first),
                        startLineCol.second,
                        m_pp->getLineNb(startLineCol.first) +
                            (endLineCol.first - startLineCol.first),
                        endLineCol.second, "", body_tokens);
      addLineFiller(ctx);
    }
  } else {
    addLineFiller(ctx);
  }
}

void SV3_1aPpTreeShapeListener::enterString(
    SV3_1aPpParser::StringContext *ctx) {
  std::string stringContent = ctx->getText();
  ParseUtils::LineColumn lineCol =
      ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  bool escaped = false;
  for (uint32_t i = 1; i < stringContent.size() - 1; i++) {
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
    if (stringContent.find('`') != std::string::npos) {
      std::string stringData = stringContent;
      stringData.erase(0, 1);
      stringData.erase(stringData.end() - 1, stringData.end());
      static const std::regex backtick_dot_re("``.``");
      static const std::regex backtick_dash_re("``-``");
      stringData = std::regex_replace(stringData, backtick_dot_re, ".");
      stringData = std::regex_replace(stringData, backtick_dash_re, "-");
      std::string mem = stringData;
      stringData = m_pp->evaluateMacroInstance(
          stringData, m_pp, lineCol.first,
          PreprocessFile::SpecialInstructions::DontCheckLoop,
          PreprocessFile::SpecialInstructions::AsIsUndefinedMacro);
      stringContent = "\"" + stringData + "\"";
    }
    m_pp->append(stringContent);
  }
}

void SV3_1aPpTreeShapeListener::enterEscaped_identifier(
    SV3_1aPpParser::Escaped_identifierContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion))) {
    if (!m_inMacroDefinitionParsing) {
      std::string text = ctx->getText();
      std::string trunc;
      for (uint32_t i = 1; i < text.size() - 1; i++) trunc += text[i];
      m_pp->append(EscapeSequence + trunc + EscapeSequence);
    }
  }
}

void SV3_1aPpTreeShapeListener::enterSource_text(
    SV3_1aPpParser::Source_textContext * /*ctx*/) {
  m_pp->getCompilationUnit()->setCurrentTimeInfo(m_pp->getFileId(0));
}

void SV3_1aPpTreeShapeListener::exitLine_directive(
    SV3_1aPpParser::Line_directiveContext * /*ctx*/) {
  m_pp->resumeAppend();
}

void SV3_1aPpTreeShapeListener::enterDefault_nettype_directive(
    SV3_1aPpParser::Default_nettype_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::exitSv_file_directive(
    SV3_1aPpParser::Sv_file_directiveContext * /*ctx*/) {
  m_pp->resumeAppend();
}

void SV3_1aPpTreeShapeListener::exitSv_line_directive(
    SV3_1aPpParser::Sv_line_directiveContext * /*ctx*/) {
  m_pp->resumeAppend();
}

void SV3_1aPpTreeShapeListener::enterTimescale_directive(
    SV3_1aPpParser::Timescale_directiveContext *ctx) {
  if (m_pp->getCompilationUnit()->isInDesignElement()) {
    std::string directive = "`timescale";
    getSymbolTable()->registerSymbol(directive);
    logError(ErrorDefinition::PP_ILLEGAL_DIRECTIVE_IN_DESIGN_ELEMENT, ctx,
             directive);
  }
  forwardToParser(ctx);

  TimeInfo compUnitTimeInfo;
  compUnitTimeInfo.m_type = TimeInfo::Type::Timescale;
  compUnitTimeInfo.m_fileId = m_pp->getFileId(0);
  ParseUtils::LineColumn lineCol = ParseUtils::getLineColumn(ctx->TIMESCALE());
  compUnitTimeInfo.m_line = lineCol.first;
  static const std::regex base_regex(
      "[ ]*([0-9]+)([mnsupf]+)[ ]*/[ ]*([0-9]+)([mnsupf]+)[ ]*");
  std::smatch base_match;
  const std::string value = ctx->TIMESCALE()->getText();
  if (std::regex_match(value, base_match, base_regex)) {
    std::ssub_match base1_sub_match = base_match[1];
    std::string base1 = base1_sub_match.str();
    compUnitTimeInfo.m_timeUnitValue = atoi(base1.c_str());
    compUnitTimeInfo.m_timeUnit = TimeInfo::unitFromString(base_match[2].str());
    std::ssub_match base2_sub_match = base_match[3];
    std::string base2 = base2_sub_match.str();
    compUnitTimeInfo.m_timePrecisionValue = atoi(base2.c_str());
    compUnitTimeInfo.m_timePrecision =
        TimeInfo::unitFromString(base_match[4].str());
  }
  m_pp->getCompilationUnit()->recordTimeInfo(compUnitTimeInfo);
}

void SV3_1aPpTreeShapeListener::enterUndef_directive(
    SV3_1aPpParser::Undef_directiveContext *ctx) {
  std::string macroName;
  ParseUtils::LineColumn lineCol =
      ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (ctx->Simple_identifier()) {
    lineCol = ParseUtils::getLineColumn(ctx->Simple_identifier());
    macroName = ctx->Simple_identifier()->getText();
  } else if (ctx->ESCAPED_IDENTIFIER()) {
    lineCol = ParseUtils::getLineColumn(ctx->ESCAPED_IDENTIFIER());
    macroName = ctx->ESCAPED_IDENTIFIER()->getText();
    macroName.erase(0, 1);
    macroName = StringUtils::rtrim(macroName);
  } else if (ctx->macro_instance()) {
    lineCol = ParseUtils::getLineColumn(m_pp->getTokenStream(),
                                        ctx->macro_instance());
    macroName = m_pp->evaluateMacroInstance(
        ctx->macro_instance()->getText(), m_pp, lineCol.first,
        PreprocessFile::SpecialInstructions::CheckLoop,
        PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  }
  if (m_reservedMacroNamesSet.find(macroName) !=
      m_reservedMacroNamesSet.end()) {
    logError(ErrorDefinition::PP_MACRO_NAME_RESERVED, ctx, macroName, 0);
  }
  if (m_pp->m_debugMacro)
    std::cout << "Undefining macro: " << macroName << std::endl;
  std::set<PreprocessFile *> visited;
  if (m_inActiveBranch && (!m_inMacroDefinitionParsing)) {
    bool found = m_pp->deleteMacro(macroName, visited);
    if (!found) {
      logError(ErrorDefinition::PP_UNDEF_UNKOWN_MACRO, ctx, macroName);
    }
  }
}

void SV3_1aPpTreeShapeListener::enterIfdef_directive(
    SV3_1aPpParser::Ifdef_directiveContext *ctx) {
  PreprocessFile::IfElseItem item;
  std::string macroName;
  ParseUtils::LineColumn lineCol =
      ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (ctx->Simple_identifier()) {
    lineCol = ParseUtils::getLineColumn(ctx->Simple_identifier());
    macroName = ctx->Simple_identifier()->getText();
  } else if (ctx->ESCAPED_IDENTIFIER()) {
    lineCol = ParseUtils::getLineColumn(ctx->ESCAPED_IDENTIFIER());
    macroName = ctx->ESCAPED_IDENTIFIER()->getText();
    macroName.erase(0, 1);
    macroName = StringUtils::rtrim(macroName);
  } else if (ctx->macro_instance()) {
    lineCol = ParseUtils::getLineColumn(m_pp->getTokenStream(),
                                        ctx->macro_instance());
    macroName = m_pp->evaluateMacroInstance(
        ctx->macro_instance()->getText(), m_pp, lineCol.first,
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
  std::string macroBody =
      m_pp->getMacro(item.m_macroName, args, m_pp, 0,
                     m_pp->getSourceFile()->m_loopChecker, instr);
  item.m_defined = (macroBody != PreprocessFile::MacroNotDefined);
  item.m_type = PreprocessFile::IfElseItem::IFDEF;
  item.m_previousActiveState = m_inActiveBranch;
  m_pp->getStack().push_back(item);
  setCurrentBranchActivity(lineCol.first);
}

void SV3_1aPpTreeShapeListener::enterIfndef_directive(
    SV3_1aPpParser::Ifndef_directiveContext *ctx) {
  PreprocessFile::IfElseItem item;
  std::string macroName;
  ParseUtils::LineColumn lineCol =
      ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (ctx->Simple_identifier()) {
    lineCol = ParseUtils::getLineColumn(ctx->Simple_identifier());
    macroName = ctx->Simple_identifier()->getText();
  } else if (ctx->ESCAPED_IDENTIFIER()) {
    lineCol = ParseUtils::getLineColumn(ctx->ESCAPED_IDENTIFIER());
    macroName = ctx->ESCAPED_IDENTIFIER()->getText();
    macroName.erase(0, 1);
    macroName = StringUtils::rtrim(macroName);
  } else if (ctx->macro_instance()) {
    lineCol = ParseUtils::getLineColumn(m_pp->getTokenStream(),
                                        ctx->macro_instance());
    macroName = m_pp->evaluateMacroInstance(
        ctx->macro_instance()->getText(), m_pp, lineCol.first,
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
  std::string macroBody =
      m_pp->getMacro(item.m_macroName, args, m_pp, 0,
                     m_pp->getSourceFile()->m_loopChecker, instr);
  item.m_defined = (macroBody != PreprocessFile::MacroNotDefined);
  item.m_type = PreprocessFile::IfElseItem::IFNDEF;
  item.m_previousActiveState = m_inActiveBranch;
  m_pp->getStack().push_back(item);
  setCurrentBranchActivity(lineCol.first);
}

void SV3_1aPpTreeShapeListener::enterElsif_directive(
    SV3_1aPpParser::Elsif_directiveContext *ctx) {
  PreprocessFile::IfElseItem item;
  std::string macroName;
  ParseUtils::LineColumn lineCol =
      ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (ctx->Simple_identifier()) {
    lineCol = ParseUtils::getLineColumn(ctx->Simple_identifier());
    macroName = ctx->Simple_identifier()->getText();
  } else if (ctx->ESCAPED_IDENTIFIER()) {
    lineCol = ParseUtils::getLineColumn(ctx->ESCAPED_IDENTIFIER());
    macroName = ctx->ESCAPED_IDENTIFIER()->getText();
    macroName.erase(0, 1);
    macroName = StringUtils::rtrim(macroName);
  } else if (ctx->macro_instance()) {
    lineCol = ParseUtils::getLineColumn(m_pp->getTokenStream(),
                                        ctx->macro_instance());
    macroName = m_pp->evaluateMacroInstance(
        ctx->macro_instance()->getText(), m_pp, lineCol.first,
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
  std::string macroBody =
      m_pp->getMacro(item.m_macroName, args, m_pp, 0,
                     m_pp->getSourceFile()->m_loopChecker, instr);
  item.m_defined =
      (macroBody != PreprocessFile::MacroNotDefined) && (!previousBranchActive);
  item.m_type = PreprocessFile::IfElseItem::ELSIF;
  m_pp->getStack().push_back(item);
  setCurrentBranchActivity(lineCol.first);
}

void SV3_1aPpTreeShapeListener::enterElse_directive(
    SV3_1aPpParser::Else_directiveContext *ctx) {
  PreprocessFile::IfElseItem item;
  ParseUtils::LineColumn lineCol =
      ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  bool previousBranchActive = isPreviousBranchActive();
  item.m_defined = !previousBranchActive;
  item.m_type = PreprocessFile::IfElseItem::ELSE;
  m_pp->getStack().push_back(item);
  setCurrentBranchActivity(lineCol.first);
}

void SV3_1aPpTreeShapeListener::enterEndif_directive(
    SV3_1aPpParser::Endif_directiveContext *ctx) {
  PreprocessFile::IfElseStack &stack = m_pp->getStack();
  ParseUtils::LineColumn lineCol =
      ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (!stack.empty()) {
    bool unroll = true;
    if (ctx->One_line_comment()) {
      addLineFiller(ctx);
    }
    while (unroll && (!stack.empty())) {
      PreprocessFile::IfElseItem &item = stack.back();
      switch (item.m_type) {
        case PreprocessFile::IfElseItem::IFDEF:
        case PreprocessFile::IfElseItem::IFNDEF:
          m_inActiveBranch = item.m_previousActiveState;
          stack.pop_back();
          unroll = false;
          break;
        case PreprocessFile::IfElseItem::ELSIF:
        case PreprocessFile::IfElseItem::ELSE:
          stack.pop_back();
          break;
        default:
          unroll = false;
          break;
      }
    }
  }
  setCurrentBranchActivity(lineCol.first);
}

void SV3_1aPpTreeShapeListener::enterResetall_directive(
    SV3_1aPpParser::Resetall_directiveContext *ctx) {
  if (m_pp->getCompilationUnit()->isInDesignElement()) {
    std::string directive = "`resetall";
    getSymbolTable()->registerSymbol(directive);
    logError(ErrorDefinition::PP_ILLEGAL_DIRECTIVE_IN_DESIGN_ELEMENT, ctx,
             directive);
  }
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterBegin_keywords_directive(
    SV3_1aPpParser::Begin_keywords_directiveContext *ctx) {
  std::string version = ctx->STRING()->getText();
  if (version == "\"1364-1995\"") {
    m_pp->setVerilogVersion(Verilog1995);
  } else if (version == "\"1364-2001\"") {
    m_pp->setVerilogVersion(Verilog2001);
  } else if (version == "\"1364-2005\"") {
    m_pp->setVerilogVersion(Verilog2005);
  } else if (version == "\"1800-2005\"") {
    m_pp->setVerilogVersion(SVerilog2005);
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

void SV3_1aPpTreeShapeListener::enterEnd_keywords_directive(
    SV3_1aPpParser::End_keywords_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterCelldefine_directive(
    SV3_1aPpParser::Celldefine_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterEndcelldefine_directive(
    SV3_1aPpParser::Endcelldefine_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterProtect_directive(
    SV3_1aPpParser::Protect_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterEndprotect_directive(
    SV3_1aPpParser::Endprotect_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterProtected_directive(
    SV3_1aPpParser::Protected_directiveContext *ctx) {
  m_inProtectedRegion = true;
  if (m_pp->getCompileSourceFile()
          ->getCommandLineParser()
          ->filterProtectedRegions()) {
    m_filterProtectedRegions = true;
  } else {
    forwardToParser(ctx);
  }
}

void SV3_1aPpTreeShapeListener::enterEndprotected_directive(
    SV3_1aPpParser::Endprotected_directiveContext *ctx) {
  m_inProtectedRegion = false;
  if (!m_pp->getCompileSourceFile()
           ->getCommandLineParser()
           ->filterProtectedRegions())
    forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterExpand_vectornets_directive(
    SV3_1aPpParser::Expand_vectornets_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterNoexpand_vectornets_directive(
    SV3_1aPpParser::Noexpand_vectornets_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterAutoexpand_vectornets_directive(
    SV3_1aPpParser::Autoexpand_vectornets_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterUselib_directive(
    SV3_1aPpParser::Uselib_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDisable_portfaults_directive(
    SV3_1aPpParser::Disable_portfaults_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterEnable_portfaults_directive(
    SV3_1aPpParser::Enable_portfaults_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterNosuppress_faults_directive(
    SV3_1aPpParser::Nosuppress_faults_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterSuppress_faults_directive(
    SV3_1aPpParser::Suppress_faults_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterSigned_directive(
    SV3_1aPpParser::Signed_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterUnsigned_directive(
    SV3_1aPpParser::Unsigned_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterRemove_gatename_directive(
    SV3_1aPpParser::Remove_gatename_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterNoremove_gatenames_directive(
    SV3_1aPpParser::Noremove_gatenames_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterRemove_netname_directive(
    SV3_1aPpParser::Remove_netname_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterNoremove_netnames_directive(
    SV3_1aPpParser::Noremove_netnames_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterAccelerate_directive(
    SV3_1aPpParser::Accelerate_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterNoaccelerate_directive(
    SV3_1aPpParser::Noaccelerate_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDefault_trireg_strength_directive(
    SV3_1aPpParser::Default_trireg_strength_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDefault_decay_time_directive(
    SV3_1aPpParser::Default_decay_time_directiveContext *ctx) {
  forwardToParser(ctx);
  m_pp->pauseAppend();
}

void SV3_1aPpTreeShapeListener::exitDefault_decay_time_directive(
    SV3_1aPpParser::Default_decay_time_directiveContext * /*ctx*/) {
  m_pp->resumeAppend();
}

void SV3_1aPpTreeShapeListener::enterUnconnected_drive_directive(
    SV3_1aPpParser::Unconnected_drive_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterNounconnected_drive_directive(
    SV3_1aPpParser::Nounconnected_drive_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDelay_mode_distributed_directive(
    SV3_1aPpParser::Delay_mode_distributed_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDelay_mode_path_directive(
    SV3_1aPpParser::Delay_mode_path_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDelay_mode_unit_directive(
    SV3_1aPpParser::Delay_mode_unit_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterDelay_mode_zero_directive(
    SV3_1aPpParser::Delay_mode_zero_directiveContext *ctx) {
  forwardToParser(ctx);
}

void SV3_1aPpTreeShapeListener::enterUndefineall_directive(
    SV3_1aPpParser::Undefineall_directiveContext * /*ctx*/) {
  std::set<PreprocessFile *> visited;
  if (m_pp->m_debugMacro) std::cout << "Undefining all macros" << std::endl;
  m_pp->undefineAllMacros(visited);
}

void SV3_1aPpTreeShapeListener::enterMultiline_no_args_macro_definition(
    SV3_1aPpParser::Multiline_no_args_macro_definitionContext *ctx) {
  if (m_inActiveBranch) {
    std::string macroName;
    if (ctx->Simple_identifier())
      macroName = ctx->Simple_identifier()->getText();
    else if (ctx->ESCAPED_IDENTIFIER()) {
      macroName = ctx->ESCAPED_IDENTIFIER()->getText();
      macroName.erase(0, 1);
      macroName = StringUtils::rtrim(macroName);
    }
    if (m_reservedMacroNamesSet.find(macroName) !=
        m_reservedMacroNamesSet.end()) {
      logError(ErrorDefinition::PP_MACRO_NAME_RESERVED, ctx, macroName, 0);
    }
    antlr4::tree::TerminalNode *const identifier =
        ctx->Simple_identifier() ? ctx->Simple_identifier()
                                 : ctx->ESCAPED_IDENTIFIER();
    ParseUtils::LineColumn startLineCol = ParseUtils::getLineColumn(identifier);
    ParseUtils::LineColumn endLineCol =
        ParseUtils::getEndLineColumn(identifier);

    if (m_pp->m_debugMacro)
      std::cout << "Defining macro:" << macroName << std::endl;
    m_inMacroDefinitionParsing = true;
    SV3_1aPpParser::Escaped_macro_definition_bodyContext *cBody =
        ctx->escaped_macro_definition_body();
    std::vector<antlr4::Token *> tokens = ParseUtils::getFlatTokenList(cBody);
    std::vector<std::string> body_tokens;
    body_tokens.reserve(tokens.size());
    for (auto token : tokens) {
      body_tokens.push_back(token->getText());
    }

    checkMultiplyDefinedMacro(macroName, ctx);

    m_pp->recordMacro(macroName, m_pp->getLineNb(startLineCol.first),
                      startLineCol.second,
                      m_pp->getLineNb(startLineCol.first) +
                          (endLineCol.first - startLineCol.first),
                      endLineCol.second, "", body_tokens);
    addLineFiller(ctx);
  } else {
    addLineFiller(ctx);
  }
}

void SV3_1aPpTreeShapeListener::exitMultiline_no_args_macro_definition(
    SV3_1aPpParser::Multiline_no_args_macro_definitionContext *ctx) {
  m_inMacroDefinitionParsing = false;
  addVObject(ctx, VObjectType::ppMacro_definition);
}

void SV3_1aPpTreeShapeListener::enterMultiline_args_macro_definition(
    SV3_1aPpParser::Multiline_args_macro_definitionContext *ctx) {
  if (m_inActiveBranch) {
    std::string macroName;
    if (ctx->Simple_identifier())
      macroName = ctx->Simple_identifier()->getText();
    else if (ctx->ESCAPED_IDENTIFIER()) {
      macroName = ctx->ESCAPED_IDENTIFIER()->getText();
      macroName.erase(0, 1);
      macroName = StringUtils::rtrim(macroName);
    }
    if (m_reservedMacroNamesSet.find(macroName) !=
        m_reservedMacroNamesSet.end()) {
      logError(ErrorDefinition::PP_MACRO_NAME_RESERVED, ctx, macroName, 0);
    }
    if (m_pp->m_debugMacro)
      std::cout << "Defining macro:" << macroName << std::endl;
    m_inMacroDefinitionParsing = true;
    SV3_1aPpParser::Escaped_macro_definition_bodyContext *cBody =
        ctx->escaped_macro_definition_body();
    std::string arguments = ctx->macro_arguments()->getText();
    std::vector<antlr4::Token *> tokens = ParseUtils::getFlatTokenList(cBody);
    std::vector<std::string> body_tokens;
    body_tokens.reserve(tokens.size());
    for (auto token : tokens) {
      body_tokens.push_back(token->getText());
    }
    antlr4::tree::TerminalNode *const identifier =
        ctx->Simple_identifier() ? ctx->Simple_identifier()
                                 : ctx->ESCAPED_IDENTIFIER();
    ParseUtils::LineColumn startLineCol = ParseUtils::getLineColumn(identifier);
    ParseUtils::LineColumn endLineCol =
        ParseUtils::getEndLineColumn(identifier);

    checkMultiplyDefinedMacro(macroName, ctx);
    m_pp->recordMacro(macroName, m_pp->getLineNb(startLineCol.first),
                      startLineCol.second,
                      m_pp->getLineNb(startLineCol.first) +
                          (endLineCol.first - startLineCol.first),
                      endLineCol.second, arguments, body_tokens);
    addLineFiller(ctx);
  } else {
    addLineFiller(ctx);
  }
}

void SV3_1aPpTreeShapeListener::exitMultiline_args_macro_definition(
    SV3_1aPpParser::Multiline_args_macro_definitionContext *ctx) {
  m_inMacroDefinitionParsing = false;
  addVObject(ctx, VObjectType::ppMacro_definition);
}

void SV3_1aPpTreeShapeListener::enterSimple_args_macro_definition(
    SV3_1aPpParser::Simple_args_macro_definitionContext *ctx) {
  if (m_inActiveBranch) {
    std::string macroName;
    if (ctx->Simple_identifier())
      macroName = ctx->Simple_identifier()->getText();
    else if (ctx->ESCAPED_IDENTIFIER()) {
      macroName = ctx->ESCAPED_IDENTIFIER()->getText();
      macroName.erase(0, 1);
      macroName = StringUtils::rtrim(macroName);
    }
    if (m_reservedMacroNamesSet.find(macroName) !=
        m_reservedMacroNamesSet.end()) {
      logError(ErrorDefinition::PP_MACRO_NAME_RESERVED, ctx, macroName, 0);
    }
    if (m_pp->m_debugMacro)
      std::cout << "Defining macro:" << macroName << std::endl;
    m_inMacroDefinitionParsing = true;
    // std::string wholeMacro = ctx->getText();
    SV3_1aPpParser::Simple_macro_definition_bodyContext *cBody =
        ctx->simple_macro_definition_body();
    std::string arguments = ctx->macro_arguments()->getText();
    std::vector<antlr4::Token *> tokens = ParseUtils::getFlatTokenList(cBody);
    std::vector<std::string> body_tokens;
    body_tokens.reserve(tokens.size());
    for (auto token : tokens) {
      body_tokens.push_back(token->getText());
    }
    antlr4::tree::TerminalNode *const identifier =
        ctx->Simple_identifier() ? ctx->Simple_identifier()
                                 : ctx->ESCAPED_IDENTIFIER();
    ParseUtils::LineColumn startLineCol = ParseUtils::getLineColumn(identifier);
    ParseUtils::LineColumn endLineCol =
        ParseUtils::getEndLineColumn(identifier);
    checkMultiplyDefinedMacro(macroName, ctx);
    m_pp->recordMacro(macroName, m_pp->getLineNb(startLineCol.first),
                      startLineCol.second,
                      m_pp->getLineNb(startLineCol.first) +
                          (endLineCol.first - startLineCol.first),
                      endLineCol.second, arguments, body_tokens);
    addLineFiller(ctx);
  } else {
    addLineFiller(ctx);
  }
}

void SV3_1aPpTreeShapeListener::exitSimple_args_macro_definition(
    SV3_1aPpParser::Simple_args_macro_definitionContext *ctx) {
  m_inMacroDefinitionParsing = false;
  addVObject(ctx, VObjectType::ppMacro_definition);
}

void SV3_1aPpTreeShapeListener::enterText_blob(
    SV3_1aPpParser::Text_blobContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion))) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
  } else {
    addLineFiller(ctx);
  }
}

void SV3_1aPpTreeShapeListener::exitText_blob(
    SV3_1aPpParser::Text_blobContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion))) {
    if (ctx->Simple_identifier()) {
      addVObject(ctx, ctx->Simple_identifier()->getText(),
                 VObjectType::ppPs_identifier);
    } else if (ctx->CR()) {
      addVObject(ctx, VObjectType::ppCR);
    } else if (ctx->Spaces()) {
      addVObject(ctx, VObjectType::ppSpaces);
    } else if (ctx->Fixed_point_number()) {
      addVObject(ctx, ctx->Fixed_point_number()->getText(),
                 VObjectType::ppNumber);
    } else if (ctx->ESCAPED_CR()) {
      addVObject(ctx, VObjectType::ppESCAPED_CR);
    } else if (ctx->STRING()) {
      addVObject(ctx, ctx->ESCAPED_CR()->getText(), VObjectType::ppString);
    } else if (ctx->OPEN_PARENS()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->CLOSE_PARENS()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->COMMA()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->ASSIGN_OP()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->DOUBLE_QUOTE()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->Special()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->OPEN_CURLY()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->CLOSE_CURLY()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->OPEN_BRACKET()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->CLOSE_BRACKET()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->TICK_TICK()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->TICK_VARIABLE()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->TIMESCALE()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->ANY()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->pound_delay()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->pound_pound_delay()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->TICK_QUOTE()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->TICK_BACKSLASH_TICK_QUOTE()) {
      addVObject(ctx, ctx->getText(), VObjectType::ppText_blob);
    } else if (ctx->TEXT_CR()) {
      addVObject(ctx, VObjectType::ppCR);
    }
  }
}

void SV3_1aPpTreeShapeListener::enterModule(
    SV3_1aPpParser::ModuleContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndmodule(
    SV3_1aPpParser::EndmoduleContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterSv_interface(
    SV3_1aPpParser::Sv_interfaceContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndinterface(
    SV3_1aPpParser::EndinterfaceContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterProgram(
    SV3_1aPpParser::ProgramContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndprogram(
    SV3_1aPpParser::EndprogramContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterPrimitive(
    SV3_1aPpParser::PrimitiveContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndprimitive(
    SV3_1aPpParser::EndprimitiveContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterSv_package(
    SV3_1aPpParser::Sv_packageContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndpackage(
    SV3_1aPpParser::EndpackageContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterChecker(
    SV3_1aPpParser::CheckerContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndchecker(
    SV3_1aPpParser::EndcheckerContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterConfig(
    SV3_1aPpParser::ConfigContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->setInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterEndconfig(
    SV3_1aPpParser::EndconfigContext *ctx) {
  if (m_inActiveBranch &&
      (!(m_filterProtectedRegions && m_inProtectedRegion)) &&
      (!m_inMacroDefinitionParsing)) {
    std::string text_blob = ctx->getText();
    m_pp->append(text_blob);
    m_pp->getCompilationUnit()->unsetInDesignElement();
  }
}

void SV3_1aPpTreeShapeListener::enterElseif_directive(
    SV3_1aPpParser::Elseif_directiveContext *ctx) {
  logError(ErrorDefinition::PP_ILLEGAL_DIRECTIVE_ELSEIF, ctx, "");
}

void SV3_1aPpTreeShapeListener::enterEveryRule(antlr4::ParserRuleContext *ctx) {
}
void SV3_1aPpTreeShapeListener::exitEveryRule(antlr4::ParserRuleContext *ctx) {}
void SV3_1aPpTreeShapeListener::visitTerminal(
    antlr4::tree::TerminalNode *node) {}
void SV3_1aPpTreeShapeListener::visitErrorNode(antlr4::tree::ErrorNode *node) {}
}  // namespace SURELOG
