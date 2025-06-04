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
 * File:   SV3_1aPreprocessorTreeListener.cpp
 * Author: hs
 *
 * Created on January 31, 2023, 12:00 PM
 */

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/FileSystem.h>
#include <Surelog/Common/Session.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/SourceCompile/CompileSourceFile.h>
#include <Surelog/SourceCompile/MacroInfo.h>
#include <Surelog/SourceCompile/PreprocessFile.h>
#include <Surelog/SourceCompile/SV3_1aPreprocessorTreeListener.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/ParseUtils.h>
#include <Surelog/Utils/StringUtils.h>
#include <parser/SV3_1aPpParser.h>

namespace SURELOG {
SV3_1aPreprocessorTreeListener::SV3_1aPreprocessorTreeListener(
    Session *session, PreprocessFile *pp, antlr4::CommonTokenStream *tokens,
    PreprocessFile::SpecialInstructions &instructions)
    : SV3_1aPpTreeListenerHelper(session, pp, instructions, tokens) {
  if (m_pp->getFileContent() == nullptr) {
    m_fileContent = new FileContent(session, m_pp->getFileId(0),
                                    m_pp->getLibrary(), nullptr, BadPathId);
    m_pp->setFileContent(m_fileContent);
  } else {
    m_fileContent = m_pp->getFileContent();
  }
}

NodeId SV3_1aPreprocessorTreeListener::addVObject(antlr4::tree::TerminalNode *node,
                                             VObjectType objectType) {
  NodeId nodeId;
  if (objectType == VObjectType::ppOne_line_comment) {
    const std::string text = node->getText();
    const LineColumn lc = ParseUtils::getLineColumn(node->getSymbol());

    bool hasCR = false;
    std::string_view trimmed = text;
    if (!trimmed.empty() && (trimmed.back() == '\n')) {
      trimmed.remove_suffix(1);
      hasCR = true;
    }

    if (!trimmed.empty()) {
      nodeId = addVObject(node, trimmed, VObjectType::paOne_line_comment);
      // Adjust the end location of the object
      VObject *const object = m_fileContent->MutableObject(nodeId);
      --object->m_endLine;
      object->m_endColumn = object->m_ppEndColumn =
          lc.second + trimmed.length();
    }
    if (hasCR) {
      nodeId = addVObject(node, "\n", VObjectType::ppCR);
      VObject *const object = m_fileContent->MutableObject(nodeId);
      object->m_startColumn = object->m_ppStartColumn =
          lc.second + trimmed.length();
    }
  } else {
    nodeId = addVObject(node, node->getText(), objectType);
  }
  return nodeId;
}

void SV3_1aPreprocessorTreeListener::adjustMacroDefinitionLocation(
    antlr4::tree::ParseTree *tree, NodeId nodeId) {
  if (!m_inMacroDefinitionParsing) return;

  LineColumn elc = ParseUtils::getEndLineColumn(m_pp->getTokenStream(), tree);
  std::string text = tree->getText();

  if (!text.empty() && (text.back() == '\n')) {
    VObject *const object = m_fileContent->MutableObject(nodeId);
    object->m_endLine = object->m_ppEndLine = elc.first - 1;
    text.pop_back();
    const size_t pos = text.rfind('\n');
    object->m_endColumn = object->m_ppEndColumn =
        (pos == std::string::npos) ? (object->m_startColumn + text.length())
                                   : text.length() - pos;
  }
}

void SV3_1aPreprocessorTreeListener::appendPreprocBegin() {
  if (m_pp != m_pp->getSourceFile()) return;

  const size_t index = m_fileContent->getVObjects().size();
  m_pp->append(StrCat(kPreprocBeginPrefix, index, kPreprocBeginSuffix));
}

void SV3_1aPreprocessorTreeListener::appendPreprocEnd() {
  if (m_pp != m_pp->getSourceFile()) return;

  const NodeId parentId = m_fileContent->addObject(
      BadSymbolId, BadPathId, VObjectType::paPREPROC_END, 0, 0, 0, 0);
  m_pp->append(StrCat(kPreprocEndPrefix, parentId, kPreprocEndSuffix));

  std::vector<VObject> &objects = *m_fileContent->mutableVObjects();

  std::set<NodeId> childrenIds;
  for (const auto &[ctx, nodeId] : m_contextToObjectMap) {
    if (!objects[nodeId].m_parent) childrenIds.insert(nodeId);
  }

  NodeId prevChildId = parentId;
  for (const NodeId &childId : childrenIds) {
    VObject &child = objects[childId];
    if (!child.m_parent) {
      child.m_parent = parentId;
      if (prevChildId == parentId) {
        objects[parentId].m_child = childId;
      } else {
        objects[prevChildId].m_sibling = childId;
      }
      prevChildId = childId;
    }
  }
  m_contextToObjectMap.clear();
}

void SV3_1aPreprocessorTreeListener::enterString(
    SV3_1aPpParser::StringContext *ctx) {
  if (m_inMacroDefinitionParsing || !m_inActiveBranch || m_inProtectedRegion) {
    return;
  }

  SymbolTable *const symbols = m_session->getSymbolTable();
  std::string stringContent = ctx->getText();
  LineColumn lineCol = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  bool escaped = false;
  for (uint32_t i = 1, ni = stringContent.size() - 1; i < ni; ++i) {
    if ((stringContent[i] == '"') && !escaped) {
      const std::string character(1, stringContent[i]);
      Location loc(m_pp->getFileId(lineCol.first),
                   m_pp->getLineNb(lineCol.first), lineCol.second + i + 1,
                   symbols->registerSymbol(character));
      logError(ErrorDefinition::PP_UNESCAPED_CHARACTER_IN_STRING, loc);
    }
    if (stringContent[i] == '\\') {
      escaped = true;
      if (i == stringContent.size() - 2) {
        const std::string character(1, stringContent[i]);
        Location loc(m_pp->getFileId(lineCol.first),
                     m_pp->getLineNb(lineCol.first), lineCol.second + i + 1,
                     symbols->registerSymbol(character));
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
                       symbols->registerSymbol(character));
          logError(ErrorDefinition::PP_UNRECOGNIZED_ESCAPED_SEQUENCE, loc);
        }
      }
    } else {
      escaped = false;
    }
  }
  if (stringContent.find('`') != std::string::npos) {
    LineColumn callingLocation = lineCol;
    if (m_pp->getEmbeddedMacroCallFile()) {
      callingLocation.first += m_pp->getEmbeddedMacroCallLine() - 1;
      callingLocation.second =
          (lineCol.first == 1)
              ? lineCol.second + m_pp->getEmbeddedMacroCallColumn() - 1
              : lineCol.second;
    }
    std::string stringData = stringContent;
    stringData.front() = stringData.back() = ' ';
    static const std::regex backtick_re("``(.)``");
    stringData = std::regex_replace(stringData, backtick_re, "$1");
    stringContent = m_pp->evaluateMacroInstance(
        stringData, m_pp, callingLocation.first, callingLocation.second,
        PreprocessFile::SpecialInstructions::DontCheckLoop,
        PreprocessFile::SpecialInstructions::AsIsUndefinedMacro);
    stringContent.front() = stringContent.back() = '\"';
  }
  m_pp->append(stringContent);
}

void SV3_1aPreprocessorTreeListener::enterEscaped_identifier(
    SV3_1aPpParser::Escaped_identifierContext *ctx) {
  if (m_inActiveBranch && !m_inProtectedRegion && !m_inMacroDefinitionParsing) {
    const std::string text = ctx->getText();

    std::string sequence = kEscapeSequence;
    sequence.append(++text.cbegin(), text.cend());
    sequence.append(kEscapeSequence);

    m_pp->append(sequence);
  }
}

void SV3_1aPreprocessorTreeListener::enterIfdef_directive(
    SV3_1aPpParser::Ifdef_directiveContext *ctx) {
  if (m_inProtectedRegion || m_inMacroDefinitionParsing) return;

  std::string macroName;
  LineColumn lc = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (antlr4::tree::TerminalNode *const simpleIdentifierNode =
          ctx->Simple_identifier()) {
    lc = ParseUtils::getLineColumn(simpleIdentifierNode);
    macroName = simpleIdentifierNode->getText();
  } else if (antlr4::tree::TerminalNode *const escapedIdentifierNode =
                 ctx->ESCAPED_IDENTIFIER()) {
    lc = ParseUtils::getLineColumn(escapedIdentifierNode);
    macroName = escapedIdentifierNode->getText();
    std::string_view svname = macroName;
    svname.remove_prefix(1);
    macroName = StringUtils::rtrim(svname);
  } else if (SV3_1aPpParser::Macro_instanceContext *const macroInstanceNode =
                 ctx->macro_instance()) {
    lc = ParseUtils::getLineColumn(m_pp->getTokenStream(), macroInstanceNode);
    macroName = m_pp->evaluateMacroInstance(
        macroInstanceNode->getText(), m_pp, lc.first, lc.second,
        PreprocessFile::SpecialInstructions::CheckLoop,
        PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  }

  if (!m_pp->isMacroBody()) {
    m_pp->getSourceFile()->m_loopChecker.clear();
  }

  std::vector<std::string> args;
  PreprocessFile::SpecialInstructions instructions = m_pp->m_instructions;
  instructions.m_evaluate = PreprocessFile::SpecialInstructions::DontEvaluate;
  const auto [result, macroBody, tokenPositions, sectionEnd] =
      m_pp->getMacro(macroName, args, m_pp, 0,
                     m_pp->getSourceFile()->m_loopChecker, instructions);

  PreprocessFile::IfElseItem &item = m_pp->getStack().emplace_back();
  item.m_macroName = macroName;
  item.m_defined = (macroBody != PreprocessFile::MacroNotDefined);
  item.m_type = PreprocessFile::IfElseItem::IFDEF;
  item.m_previousActiveState = m_inActiveBranch;
  setCurrentBranchActivity(lc.first);

  if (!m_passThrough) {
    appendPreprocBegin();
    m_passThrough = true;
  }
}

void SV3_1aPreprocessorTreeListener::exitIfdef_directive(
    SV3_1aPpParser::Ifdef_directiveContext *ctx) {
  if (m_inProtectedRegion || m_inMacroDefinitionParsing) return;

  if (!m_passThrough) {
    addVObject(ctx, VObjectType::ppIfdef_directive);

    std::string text = ctx->getText();
    std::replace_if(
        text.begin(), text.end(), [](char ch) { return ch != '\n'; }, ' ');
    m_pp->append(text);
  }

  if (m_inActiveBranch) {
    appendPreprocEnd();
    m_passThrough = false;
  }
}

void SV3_1aPreprocessorTreeListener::enterIfndef_directive(
    SV3_1aPpParser::Ifndef_directiveContext *ctx) {
  if (m_inProtectedRegion || m_inMacroDefinitionParsing) return;

  std::string macroName;
  LineColumn lc = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (antlr4::tree::TerminalNode *const simpleIdentifierNode =
          ctx->Simple_identifier()) {
    lc = ParseUtils::getLineColumn(simpleIdentifierNode);
    macroName = simpleIdentifierNode->getText();
  } else if (antlr4::tree::TerminalNode *const escapedIdentifierNode =
                 ctx->ESCAPED_IDENTIFIER()) {
    lc = ParseUtils::getLineColumn(escapedIdentifierNode);
    macroName = escapedIdentifierNode->getText();
    std::string_view svname = macroName;
    svname.remove_prefix(1);
    macroName = StringUtils::rtrim(svname);
  } else if (SV3_1aPpParser::Macro_instanceContext *const macroInstanceNode =
                 ctx->macro_instance()) {
    lc = ParseUtils::getLineColumn(m_pp->getTokenStream(), macroInstanceNode);
    macroName = m_pp->evaluateMacroInstance(
        macroInstanceNode->getText(), m_pp, lc.first, lc.second,
        PreprocessFile::SpecialInstructions::CheckLoop,
        PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  }

  if (!m_pp->isMacroBody()) {
    m_pp->getSourceFile()->m_loopChecker.clear();
  }

  std::vector<std::string> args;
  PreprocessFile::SpecialInstructions instructions = m_pp->m_instructions;
  instructions.m_evaluate = PreprocessFile::SpecialInstructions::DontEvaluate;
  const auto [result, macroBody, tokenPositions, sectionEnd] =
      m_pp->getMacro(macroName, args, m_pp, 0,
                     m_pp->getSourceFile()->m_loopChecker, instructions);

  PreprocessFile::IfElseItem &item = m_pp->getStack().emplace_back();
  item.m_macroName = macroName;
  item.m_defined = (macroBody != PreprocessFile::MacroNotDefined);
  item.m_type = PreprocessFile::IfElseItem::IFNDEF;
  item.m_previousActiveState = m_inActiveBranch;
  setCurrentBranchActivity(lc.first);

  if (!m_passThrough) {
    appendPreprocBegin();
    m_passThrough = true;
  }
}

void SV3_1aPreprocessorTreeListener::exitIfndef_directive(
    SV3_1aPpParser::Ifndef_directiveContext *ctx) {
  if (m_inProtectedRegion || m_inMacroDefinitionParsing) return;

  if (!m_passThrough) {
    addVObject(ctx, VObjectType::ppIfndef_directive);

    std::string text = ctx->getText();
    std::replace_if(
        text.begin(), text.end(), [](char ch) { return ch != '\n'; }, ' ');
    m_pp->append(text);
  }

  if (m_inActiveBranch) {
    appendPreprocEnd();
    m_passThrough = false;
  }
}

void SV3_1aPreprocessorTreeListener::enterUndef_directive(
    SV3_1aPpParser::Undef_directiveContext *ctx) {
  if (m_inProtectedRegion || m_inMacroDefinitionParsing) return;

  if (!m_passThrough) {
    appendPreprocBegin();
    m_passThrough = true;
  }
}

void SV3_1aPreprocessorTreeListener::exitUndef_directive(
    SV3_1aPpParser::Undef_directiveContext *ctx) {
  if (m_inProtectedRegion || m_inMacroDefinitionParsing) return;

  if (!m_passThrough) {
    addVObject(ctx, VObjectType::ppUndef_directive);

    std::string text = ctx->getText();
    std::replace_if(
        text.begin(), text.end(), [](char ch) { return ch != '\n'; }, ' ');
    m_pp->append(text);
  }

  if (m_inActiveBranch) {
    appendPreprocEnd();
    m_passThrough = false;
  }
}

void SV3_1aPreprocessorTreeListener::enterElsif_directive(
    SV3_1aPpParser::Elsif_directiveContext *ctx) {
  if (m_inProtectedRegion || m_inMacroDefinitionParsing) return;

  std::string macroName;
  LineColumn lc = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  if (antlr4::tree::TerminalNode *const simpleIdentifierNode =
          ctx->Simple_identifier()) {
    lc = ParseUtils::getLineColumn(simpleIdentifierNode);
    macroName = simpleIdentifierNode->getText();
  } else if (antlr4::tree::TerminalNode *const escapedIdentifierNode =
                 ctx->ESCAPED_IDENTIFIER()) {
    lc = ParseUtils::getLineColumn(escapedIdentifierNode);
    macroName = escapedIdentifierNode->getText();
    std::string_view svname = macroName;
    svname.remove_prefix(1);
    macroName = StringUtils::rtrim(svname);
  } else if (SV3_1aPpParser::Macro_instanceContext *const macroInstanceNode =
                 ctx->macro_instance()) {
    lc = ParseUtils::getLineColumn(m_pp->getTokenStream(), macroInstanceNode);
    macroName = m_pp->evaluateMacroInstance(
        macroInstanceNode->getText(), m_pp, lc.first, lc.second,
        PreprocessFile::SpecialInstructions::CheckLoop,
        PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  }

  if (!m_pp->isMacroBody()) {
    m_pp->getSourceFile()->m_loopChecker.clear();
  }

  std::vector<std::string> args;
  PreprocessFile::SpecialInstructions instructions = m_pp->m_instructions;
  instructions.m_evaluate = PreprocessFile::SpecialInstructions::DontEvaluate;
  const auto [result, macroBody, tokenPositions, sectionEnd] =
      m_pp->getMacro(macroName, args, m_pp, 0,
                     m_pp->getSourceFile()->m_loopChecker, instructions);

  const bool previousBranchActive = isPreviousBranchActive();
  PreprocessFile::IfElseItem &item = m_pp->getStack().emplace_back();
  item.m_macroName = macroName;
  item.m_defined =
      (macroBody != PreprocessFile::MacroNotDefined) && !previousBranchActive;
  item.m_type = PreprocessFile::IfElseItem::ELSIF;
  item.m_previousActiveState = m_inActiveBranch;
  setCurrentBranchActivity(lc.first);

  if (!m_passThrough) {
    appendPreprocBegin();
    m_passThrough = true;
  }
}

void SV3_1aPreprocessorTreeListener::exitElsif_directive(
    SV3_1aPpParser::Elsif_directiveContext *ctx) {
  if (m_inProtectedRegion || m_inMacroDefinitionParsing) return;

  if (!m_passThrough) {
    addVObject(ctx, VObjectType::ppElsif_directive);

    std::string text = ctx->getText();
    std::replace_if(
        text.begin(), text.end(), [](char ch) { return ch != '\n'; }, ' ');
    m_pp->append(text);
  }

  if (m_inActiveBranch) {
    appendPreprocEnd();
    m_passThrough = false;
  }
}

void SV3_1aPreprocessorTreeListener::enterElse_directive(
    SV3_1aPpParser::Else_directiveContext *ctx) {
  if (m_inProtectedRegion || m_inMacroDefinitionParsing) return;

  if (!m_passThrough) {
    appendPreprocBegin();
    m_passThrough = true;
  }
}

void SV3_1aPreprocessorTreeListener::exitElse_directive(
    SV3_1aPpParser::Else_directiveContext *ctx) {
  if (m_inProtectedRegion || m_inMacroDefinitionParsing) return;

  const bool prevInActiveBranch = m_inActiveBranch;
  const bool previousBranchActive = isPreviousBranchActive();
  const LineColumn lc = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  PreprocessFile::IfElseItem &item = m_pp->getStack().emplace_back();
  item.m_defined = !previousBranchActive;
  item.m_type = PreprocessFile::IfElseItem::ELSE;
  item.m_previousActiveState = m_inActiveBranch;
  setCurrentBranchActivity(lc.first);

  if (!m_passThrough) {
    addVObject(ctx, VObjectType::ppElse_directive);

    std::string text = ctx->getText();
    std::replace_if(
        text.begin(), text.end(), [](char ch) { return ch != '\n'; }, ' ');
    m_pp->append(text);
  }

  if (!prevInActiveBranch && m_inActiveBranch) m_passThrough = false;
  if (!m_passThrough) appendPreprocEnd();
}

void SV3_1aPreprocessorTreeListener::enterEndif_directive(
    SV3_1aPpParser::Endif_directiveContext *ctx) {
  if (m_inProtectedRegion || m_inMacroDefinitionParsing) return;

  if (!m_passThrough) {
    appendPreprocBegin();
    m_passThrough = true;
  }
}

void SV3_1aPreprocessorTreeListener::exitEndif_directive(
    SV3_1aPpParser::Endif_directiveContext *ctx) {
  if (m_inProtectedRegion || m_inMacroDefinitionParsing) return;

  PreprocessFile::IfElseStack &stack = m_pp->getStack();
  bool unroll = true;
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

  const LineColumn lc = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  setCurrentBranchActivity(lc.first);

  if (!m_passThrough) {
    std::string text = ctx->getText();
    std::replace_if(
        text.begin(), text.end(), [](char ch) { return ch != '\n'; }, ' ');
    m_pp->append(text);
  }

  if (m_inActiveBranch) m_passThrough = false;

  if (!m_passThrough) {
    addVObject(ctx, VObjectType::ppEndif_directive);
    appendPreprocEnd();
  }
}

void SV3_1aPreprocessorTreeListener::enterInclude_directive(
    SV3_1aPpParser::Include_directiveContext *ctx) {
  if (!m_inActiveBranch || m_inProtectedRegion) return;

  if (!m_passThrough) {
    appendPreprocBegin();
    m_passThrough = true;
  }

  FileSystem *const fileSystem = m_session->getFileSystem();

  LineColumn slc = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  LineColumn elc = ParseUtils::getEndLineColumn(m_pp->getTokenStream(), ctx);

  std::string fileName;
  if (antlr4::tree::TerminalNode *const stringNode = ctx->STRING()) {
    fileName = stringNode->getText();
    slc = ParseUtils::getLineColumn(stringNode);
    elc = ParseUtils::getEndLineColumn(stringNode);
  } else if (SV3_1aPpParser::Macro_instanceContext *const macroInstanceNode =
                 ctx->macro_instance()) {
    slc = ParseUtils::getLineColumn(m_pp->getTokenStream(), macroInstanceNode);
    elc =
        ParseUtils::getEndLineColumn(m_pp->getTokenStream(), macroInstanceNode);
    fileName = m_pp->evaluateMacroInstance(
        macroInstanceNode->getText(), m_pp, slc.first, slc.second,
        PreprocessFile::SpecialInstructions::CheckLoop,
        PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
  } else {
    Location loc(m_pp->getFileId(slc.first), m_pp->getLineNb(slc.first),
                 slc.second);
    logError(ErrorDefinition::PP_INVALID_INCLUDE_FILENAME, loc);
    return;
  }

  fileName = StringUtils::unquoted(StringUtils::trim(fileName));

  SymbolTable *const symbols = m_session->getSymbolTable();

  PathId fileId = fileSystem->locate(
      fileName, m_session->getCommandLineParser()->getIncludePaths(), symbols);
  if (!fileId) {
    // If failed to locate, then assume the same folder as the includer file
    // and let it fail down the stream.
    fileId = fileSystem->getSibling(m_pp->getCompileSourceFile()->getFileId(),
                                    fileName, symbols);
  }

  if (m_session->getCommandLineParser()->verbose()) {
    Location loc(fileId);
    logError(ErrorDefinition::PP_PROCESSING_INCLUDE_FILE, loc, true);
  }

  // Detect include loop
  PreprocessFile *tmp = m_pp;
  while (tmp) {
    if (tmp->getFileId(0) == fileId) {
      Location loc(m_pp->getFileId(slc.first), slc.first, slc.second,
                   (SymbolId)fileId);
      logError(ErrorDefinition::PP_RECURSIVE_INCLUDE_DIRECTIVE, loc, true);
      return;
    }
    tmp = tmp->getIncluder();
  }

  PreprocessFile *pp = new PreprocessFile(
      m_session, fileId, m_pp->getCompileSourceFile(), m_instructions,
      m_pp->getCompilationUnit(), m_pp->getLibrary(), m_pp, slc.first);
  m_pp->getCompileSourceFile()->registerPP(pp);
  pp->preprocess();
}

void SV3_1aPreprocessorTreeListener::exitInclude_directive(
    SV3_1aPpParser::Include_directiveContext *ctx) {
  if (!m_inActiveBranch || m_inProtectedRegion) return;

  if (!m_passThrough) {
    addVObject(ctx, VObjectType::ppInclude_directive);

    std::string text = ctx->getText();
    std::replace_if(
        text.begin(), text.end(), [](char ch) { return ch != '\n'; }, ' ');
    m_pp->append(text);
  }

  if (m_inActiveBranch) {
    appendPreprocEnd();
    m_passThrough = false;
  }
}

void SV3_1aPreprocessorTreeListener::enterLine_directive(
    SV3_1aPpParser::Line_directiveContext *ctx) {
  if (m_inActiveBranch && !m_inProtectedRegion && !m_inMacroDefinitionParsing) {
    appendPreprocBegin();
  }
}

void SV3_1aPreprocessorTreeListener::exitLine_directive(
    SV3_1aPpParser::Line_directiveContext *ctx) {
  if (m_inActiveBranch && !m_inProtectedRegion && !m_inMacroDefinitionParsing) {
    appendPreprocEnd();
  }
}

void SV3_1aPreprocessorTreeListener::enterSv_file_directive(
    SV3_1aPpParser::Sv_file_directiveContext *ctx) {
  if (!m_inActiveBranch || m_inProtectedRegion || m_inMacroDefinitionParsing) {
    return;
  }

  appendPreprocBegin();
  if (m_pp->getMacroInfo() != nullptr) {
    m_pp->append(PreprocessFile::PP__File__Marking);
  } else {
    FileSystem *const fileSystem = m_session->getFileSystem();
    const LineColumn lc =
        ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
    m_pp->append(
        StrCat("\"", fileSystem->toPath(m_pp->getFileId(lc.first)), "\""));
    m_passThrough = true;
  }
}

void SV3_1aPreprocessorTreeListener::exitSv_file_directive(
    SV3_1aPpParser::Sv_file_directiveContext *ctx) {
  if (m_inActiveBranch && !m_inProtectedRegion && !m_inMacroDefinitionParsing) {
    addVObject(ctx, VObjectType::ppSv_file_directive);
    appendPreprocEnd();
    m_passThrough = false;
  }
}

void SV3_1aPreprocessorTreeListener::enterSv_line_directive(
    SV3_1aPpParser::Sv_line_directiveContext *ctx) {
  if (!m_inActiveBranch || m_inProtectedRegion || m_inMacroDefinitionParsing) {
    return;
  }

  appendPreprocBegin();
  if (m_pp->getMacroInfo() != nullptr) {
    m_pp->append(PreprocessFile::PP__Line__Marking);
  } else {
    const LineColumn lc =
        ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
    m_pp->append(std::to_string(m_pp->getLineNb(lc.first)));
    m_passThrough = true;
  }
}

void SV3_1aPreprocessorTreeListener::exitSv_line_directive(
    SV3_1aPpParser::Sv_line_directiveContext *ctx) {
  if (m_inActiveBranch && !m_inProtectedRegion && !m_inMacroDefinitionParsing) {
    addVObject(ctx, VObjectType::ppSv_line_directive);
    appendPreprocEnd();
    m_passThrough = false;
  }
}

void SV3_1aPreprocessorTreeListener::enterMacroInstanceWithArgs(
    SV3_1aPpParser::MacroInstanceWithArgsContext *ctx) {
  if (m_inMacroDefinitionParsing || !m_inActiveBranch || m_inProtectedRegion) {
    return;
  }
  if (m_pp->isPaused()) return;

  if (!m_passThrough) {
    appendPreprocBegin();
    m_passThrough = true;
  }

  std::string macroName;
  if (antlr4::tree::TerminalNode *const identifier = ctx->Macro_identifier()) {
    macroName = identifier->getText();
  } else if (antlr4::tree::TerminalNode *escapedIdentifier =
                 ctx->Macro_Escaped_identifier()) {
    macroName = escapedIdentifier->getText();
    std::string_view svname = macroName;
    svname.remove_prefix(1);
    macroName = StringUtils::rtrim(svname);
  }
  macroName.erase(macroName.begin());

  std::vector<antlr4::tree::ParseTree *> tokens =
      ParseUtils::getTopTokenList(ctx->macro_actual_args());
  std::vector<std::string> actualArgs;
  ParseUtils::tokenizeAtComma(actualArgs, tokens);

  int32_t openingIndex = -1;
  if (!m_pp->isMacroBody()) {
    m_pp->getSourceFile()->m_loopChecker.clear();
  }

  LineColumn slc = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  LineColumn elc = ParseUtils::getEndLineColumn(m_pp->getTokenStream(), ctx);

  PathId fileId = m_pp->getRawFileId();
  if (m_pp->getEmbeddedMacroCallFile()) {
    fileId = m_pp->getEmbeddedMacroCallFile();
    if (slc.first == 1) slc.second += m_pp->getEmbeddedMacroCallColumn() - 1;
    if (elc.first == 1) elc.second += m_pp->getEmbeddedMacroCallColumn() - 1;
    slc.first += m_pp->getEmbeddedMacroCallLine() - 1;
    elc.first += m_pp->getEmbeddedMacroCallLine() - 1;
  }

  std::tuple<bool, std::string, std::vector<LineColumn>, LineColumn> evalResult;
  if (MacroInfo *const macroInfo = m_pp->getMacro(macroName)) {
    if (m_pp == m_pp->getSourceFile()) {
      const LineColumn clc = m_pp->getCurrentPosition();
      openingIndex = m_pp->getSourceFile()->addIncludeFileInfo(
          /* context */ IncludeFileInfo::Context::Macro,
          /* action */ IncludeFileInfo::Action::Push,
          /* macroDefinition */ macroInfo,
          /* sectionFileId */ fileId,
          /* sectionLine */ macroInfo->m_startLine,
          /* sectionColumn */ macroInfo->m_bodyStartColumn,
          /* sourceLine */ clc.first,
          /* sourceColumn */ clc.second,
          /* sectionSymbolId */ BadSymbolId,
          /* symbolLine */ slc.first,
          /* symbolColumn */ slc.second);
    }
    evalResult =
        m_pp->getMacro(macroName, actualArgs, m_pp, slc.first,
                       m_pp->getSourceFile()->m_loopChecker,
                       m_pp->m_instructions, macroInfo->m_fileId,
                       macroInfo->m_startLine, macroInfo->m_bodyStartColumn);
  } else {
    evalResult = m_pp->getMacro(macroName, actualArgs, m_pp, slc.first,
                                m_pp->getSourceFile()->m_loopChecker,
                                m_pp->m_instructions);
  }

  const std::string macroArgs = ctx->macro_actual_args()->getText();
  const size_t nCRinArgs =
      std::count(macroArgs.cbegin(), macroArgs.cend(), '\n');

  std::string &macroBody = std::get<1>(evalResult);
  bool emptyMacroBody = false;
  if (macroBody.empty()) {
    emptyMacroBody = true;
    macroBody.append(nCRinArgs, '\n');
  }

  m_pp->append(macroBody);

  if (openingIndex >= 0) {
    LineColumn clc = m_pp->getCurrentPosition();
    if (emptyMacroBody && (nCRinArgs > 0)) {
      clc.first -= nCRinArgs;
    }
    const LineColumn &rlc = std::get<3>(evalResult);
    m_pp->getSourceFile()->addIncludeFileInfo(
        /* context */ IncludeFileInfo::Context::Macro,
        /* action */ IncludeFileInfo::Action::Pop,
        /* macroDefinition */ nullptr,
        /* sectionFileId */ BadPathId,
        /* sectionLine */ rlc.first,
        /* sectionColumn */ rlc.second,
        /* sourceLine */ clc.first,
        /* sourceColumn */ clc.second,
        /* sectionSymbolId */ BadSymbolId,
        /* symbolLine */ elc.first,
        /* symbolColumn */ elc.second,
        /* indexOpposite */ openingIndex);
  }

  if (m_appendPausedContext == nullptr) {
    m_appendPausedContext = ctx;
    m_pp->pauseAppend();
  }
}

void SV3_1aPreprocessorTreeListener::exitMacroInstanceWithArgs(
    SV3_1aPpParser::MacroInstanceWithArgsContext *ctx) {
  if (m_inMacroDefinitionParsing || !m_inActiveBranch || m_inProtectedRegion) {
    return;
  }

  if (m_appendPausedContext == ctx) {
    m_appendPausedContext = nullptr;
    m_pp->resumeAppend();
  }

  addVObject(ctx, VObjectType::ppMacro_instance);
  appendPreprocEnd();
  m_passThrough = false;
}

void SV3_1aPreprocessorTreeListener::enterMacroInstanceNoArgs(
    SV3_1aPpParser::MacroInstanceNoArgsContext *ctx) {
  if (m_inMacroDefinitionParsing || !m_inActiveBranch || m_inProtectedRegion) {
    return;
  }
  if (m_pp->isPaused()) return;

  if (!m_passThrough) {
    appendPreprocBegin();
    m_passThrough = true;
  }

  std::string macroName;
  if (antlr4::tree::TerminalNode *const macroIdentifierNode =
          ctx->Macro_identifier()) {
    macroName = macroIdentifierNode->getText();
  } else if (antlr4::tree::TerminalNode *const macroEscapedIdentifierNode =
                 ctx->Macro_Escaped_identifier()) {
    macroName = macroEscapedIdentifierNode->getText();
    std::string_view svname = macroName;
    svname.remove_prefix(1);
    macroName = StringUtils::rtrim(svname);
  }
  macroName.erase(macroName.begin());

  if (!m_pp->isMacroBody()) {
    m_pp->getSourceFile()->m_loopChecker.clear();
  }

  LineColumn slc = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  LineColumn elc = ParseUtils::getEndLineColumn(m_pp->getTokenStream(), ctx);

  PathId fileId = m_pp->getRawFileId();
  if (m_pp->getEmbeddedMacroCallFile()) {
    fileId = m_pp->getEmbeddedMacroCallFile();
    if (slc.first == 1) slc.second += m_pp->getEmbeddedMacroCallColumn() - 1;
    if (elc.first == 1) elc.second += m_pp->getEmbeddedMacroCallColumn() - 1;
    slc.first += m_pp->getEmbeddedMacroCallLine() - 1;
    elc.first += m_pp->getEmbeddedMacroCallLine() - 1;
  }

  SymbolTable *const symbols = m_session->getSymbolTable();

  int32_t openingIndex = -1;
  std::vector<std::string> args;
  std::tuple<bool, std::string, std::vector<LineColumn>, LineColumn> evalResult;

  if (MacroInfo *const macroInfo = m_pp->getMacro(macroName)) {
    if (!macroInfo->m_arguments.empty()) {
      Location loc(m_pp->getFileId(slc.first), m_pp->getLineNb(slc.first),
                   slc.second, symbols->getId(macroName));
      Location extraLoc(macroInfo->m_fileId, macroInfo->m_startLine,
                        macroInfo->m_startColumn);
      logError(ErrorDefinition::PP_MACRO_PARENTHESIS_NEEDED, loc, extraLoc);
    }

    if (m_pp == m_pp->getSourceFile()) {
      const LineColumn clc = m_pp->getCurrentPosition();
      openingIndex = m_pp->getSourceFile()->addIncludeFileInfo(
          /* context */ IncludeFileInfo::Context::Macro,
          /* action */ IncludeFileInfo::Action::Push,
          /* macroDefinition */ macroInfo,
          /* sectionFileId */ fileId,
          /* sectionLine */ macroInfo->m_startLine,
          /* sectionColumn */ macroInfo->m_bodyStartColumn,
          /* sourceLine */ clc.first,
          /* sourceColumn */ clc.second,
          /* sectionSymbolId */ BadSymbolId,
          /* symbolLine */ slc.first,
          /* symbolColumn */ slc.second);
    }
    evalResult = m_pp->getMacro(
        macroName, args, m_pp, slc.first, m_pp->getSourceFile()->m_loopChecker,
        m_pp->m_instructions, macroInfo->m_fileId, macroInfo->m_startLine,
        macroInfo->m_bodyStartColumn);
  } else {
    evalResult = m_pp->getMacro(macroName, args, m_pp, slc.first,
                                m_pp->getSourceFile()->m_loopChecker,
                                m_pp->m_instructions);
  }

  std::string &macroBody = std::get<1>(evalResult);
  if (macroBody.empty() && m_instructions.m_mark_empty_macro) {
    macroBody = SymbolTable::getEmptyMacroMarker();
  }

  m_pp->append(macroBody);

  if (openingIndex >= 0) {
    const LineColumn clc = m_pp->getCurrentPosition();
    const LineColumn &rlc = std::get<3>(evalResult);
    m_pp->getSourceFile()->addIncludeFileInfo(
        /* context */ IncludeFileInfo::Context::Macro,
        /* action */ IncludeFileInfo::Action::Pop,
        /* macroDefinition */ nullptr,
        /* sectionFileId */ BadPathId,
        /* sectionLine */ rlc.first,
        /* sectionColumn */ rlc.second,
        /* sourceLine */ clc.first,
        /* sourceColumn */ clc.second,
        /* sectionSymbolId */ BadSymbolId,
        /* symbolLine */ elc.first,
        /* symbolColumn */ elc.second,
        /* indexOpposite */ openingIndex);
  }

  if (m_appendPausedContext == nullptr) {
    m_appendPausedContext = ctx;
    m_pp->pauseAppend();
  }
}

void SV3_1aPreprocessorTreeListener::exitMacroInstanceNoArgs(
    SV3_1aPpParser::MacroInstanceNoArgsContext *ctx) {
  if (m_inMacroDefinitionParsing || !m_inActiveBranch || m_inProtectedRegion) {
    return;
  }

  if (m_appendPausedContext == ctx) {
    m_appendPausedContext = nullptr;
    m_pp->resumeAppend();
  }

  addVObject(ctx, VObjectType::ppMacro_instance);
  appendPreprocEnd();
  m_passThrough = false;
}

void SV3_1aPreprocessorTreeListener::enterMacro_definition(
    SV3_1aPpParser::Macro_definitionContext *ctx) {
  if (!m_inActiveBranch || m_inProtectedRegion) return;

  appendPreprocBegin();

  std::string macroName;
  std::string arguments;
  antlr4::tree::TerminalNode *identifier = nullptr;
  antlr4::ParserRuleContext *body = nullptr;

  if (SV3_1aPpParser::Simple_no_args_macro_definitionContext *const
          simpleNoArgsDefinition = ctx->simple_no_args_macro_definition()) {
    if ((identifier = simpleNoArgsDefinition->Simple_identifier()))
      macroName = identifier->getText();
    else if ((identifier = simpleNoArgsDefinition->ESCAPED_IDENTIFIER())) {
      macroName = identifier->getText();
      std::string_view svname = macroName;
      svname.remove_prefix(1);
      macroName = StringUtils::rtrim(svname);
    }

    body = simpleNoArgsDefinition->simple_macro_definition_body();
  } else if (SV3_1aPpParser::Simple_args_macro_definitionContext *const
                 simpleArgsDefinition = ctx->simple_args_macro_definition()) {
    if ((identifier = simpleArgsDefinition->Simple_identifier()))
      macroName = identifier->getText();
    else if ((identifier = simpleArgsDefinition->ESCAPED_IDENTIFIER())) {
      macroName = identifier->getText();
      std::string_view svname = macroName;
      svname.remove_prefix(1);
      macroName = StringUtils::rtrim(svname);
    }

    arguments = simpleArgsDefinition->macro_arguments()->getText();
    body = simpleArgsDefinition->simple_macro_definition_body();
  } else if (SV3_1aPpParser::Multiline_no_args_macro_definitionContext
                 *const multiNoArgsDefinition =
                     ctx->multiline_no_args_macro_definition()) {
    if ((identifier = multiNoArgsDefinition->Simple_identifier()))
      macroName = identifier->getText();
    else if ((identifier = multiNoArgsDefinition->ESCAPED_IDENTIFIER())) {
      macroName = identifier->getText();
      std::string_view svname = macroName;
      svname.remove_prefix(1);
      macroName = StringUtils::rtrim(svname);
    }

    body = multiNoArgsDefinition->escaped_macro_definition_body();
  } else if (SV3_1aPpParser::Multiline_args_macro_definitionContext *const
                 multiArgsDefinition = ctx->multiline_args_macro_definition()) {
    if ((identifier = multiArgsDefinition->Simple_identifier()))
      macroName = identifier->getText();
    else if ((identifier = multiArgsDefinition->ESCAPED_IDENTIFIER())) {
      macroName = identifier->getText();
      std::string_view svname = macroName;
      svname.remove_prefix(1);
      macroName = StringUtils::rtrim(svname);
    }

    arguments = multiArgsDefinition->macro_arguments()->getText();
    body = multiArgsDefinition->escaped_macro_definition_body();
  } else if (SV3_1aPpParser::Define_directiveContext *const defineDirective =
                 ctx->define_directive()) {
    if ((identifier = defineDirective->Simple_identifier()))
      macroName = identifier->getText();
    else if ((identifier = defineDirective->ESCAPED_IDENTIFIER())) {
      macroName = identifier->getText();
      std::string_view svname = macroName;
      svname.remove_prefix(1);
      macroName = StringUtils::rtrim(svname);
    }
  }

  std::string_view svname = macroName;
  if (macroName[0] == '\\') svname.remove_prefix(1);
  macroName = StringUtils::rtrim(svname);

  const LineColumn slc = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  LineColumn elc = ParseUtils::getEndLineColumn(m_pp->getTokenStream(), ctx);
  const LineColumn nslc = ParseUtils::getLineColumn(identifier);

  LineColumn bslc;
  std::vector<std::string> bodyTokens;
  std::vector<LineColumn> bodyTokenPositions;
  if (body != nullptr) {
    std::vector<antlr4::Token *> tokens = ParseUtils::getFlatTokenList(body);

    std::string suffix;
    while (!tokens.empty()) {
      std::string snippet = tokens.back()->getText();
      if (snippet == "\\\n") {
        suffix.clear();
        break;
      } else {
        while (!snippet.empty() && std::isspace(snippet.back())) {
          suffix.append(1, snippet.back());
          snippet.pop_back();
        }
        if (snippet.empty()) {
          tokens.pop_back();
          suffix.clear();
        } else {
          break;
        }
      }
    }

    bodyTokens.reserve(tokens.size());
    bodyTokenPositions.reserve(tokens.size());
    for (antlr4::Token *token : tokens) {
      bodyTokens.emplace_back(token->getText());
      bodyTokenPositions.emplace_back(ParseUtils::getLineColumn(token));
    }

    bslc = ParseUtils::getLineColumn(m_pp->getTokenStream(), body);
    elc = ParseUtils::getEndLineColumn(tokens.empty() ? body->getStop()
                                                      : tokens.back());
    if (!suffix.empty() && !tokens.empty() && (elc.second >= suffix.length())) {
      elc.second -= suffix.length();
      bodyTokens.back().resize(bodyTokens.back().length() - suffix.length());
    }
  }

  m_pp->defineMacro(macroName, MacroInfo::DefType::Define,
                    m_pp->getLineNb(slc.first), slc.second,
                    m_pp->getLineNb(elc.first), elc.second, nslc.second,
                    bslc.second, arguments, {}, bodyTokens, bodyTokenPositions);
  m_inMacroDefinitionParsing = true;
}

void SV3_1aPreprocessorTreeListener::exitMacro_definition(
    SV3_1aPpParser::Macro_definitionContext *ctx) {
  if (!m_inActiveBranch || m_inProtectedRegion) return;

  adjustMacroDefinitionLocation(
      ctx, addVObject(ctx, VObjectType::ppMacro_definition));

  size_t suffixCRs = 0;
  std::string text = ctx->getText();
  while (!text.empty() && (text.back() == '\n')) {
    text.pop_back();
    ++suffixCRs;
  }

  std::replace_if(
      text.begin(), text.end(), [](char ch) { return ch != '\n'; }, ' ');
  m_pp->append(text);
  appendPreprocEnd();
  if (suffixCRs > 0) m_pp->append(std::string(suffixCRs, '\n'));

  m_inMacroDefinitionParsing = false;
}

void SV3_1aPreprocessorTreeListener::enterUndefineall_directive(
    SV3_1aPpParser::Undefineall_directiveContext *ctx) {
  if (!m_inActiveBranch || m_inProtectedRegion) return;

  if (!m_passThrough) {
    appendPreprocBegin();
    m_passThrough = true;
  }

  const LineColumn slc = ParseUtils::getLineColumn(m_pp->getTokenStream(), ctx);
  const LineColumn elc =
      ParseUtils::getEndLineColumn(m_pp->getTokenStream(), ctx);
  m_pp->undefineAllMacros(m_pp->getLineNb(slc.first), slc.second,
                          m_pp->getLineNb(elc.first), elc.second);
  m_inMacroDefinitionParsing = true;
}

void SV3_1aPreprocessorTreeListener::exitUndefineall_directive(
    SV3_1aPpParser::Undefineall_directiveContext *ctx) {
  if (!m_inActiveBranch || m_inProtectedRegion) return;

  if (!m_passThrough) {
    addVObject(ctx, VObjectType::ppUndefineall_directive);
  }

  if (m_inActiveBranch) {
    appendPreprocEnd();
    m_passThrough = false;
  }
  m_inMacroDefinitionParsing = false;
}

void SV3_1aPreprocessorTreeListener::enterPragma_directive(
    SV3_1aPpParser::Pragma_directiveContext *ctx) {
  if (!m_inActiveBranch || m_inProtectedRegion) return;

  if (antlr4::tree::TerminalNode *const identifier = ctx->Simple_identifier()) {
    if (identifier->getText() == "protect") {
      const std::vector<SV3_1aPpParser::Pragma_expressionContext *> &exprs =
          ctx->pragma_expression();
      for (SV3_1aPpParser::Pragma_expressionContext *expr : exprs) {
        if (antlr4::tree::TerminalNode *const exprIdentifier =
                expr->Simple_identifier()) {
          if (exprIdentifier->getText() == "begin_protected") {
            m_inProtectedRegion = true;
            if (!m_passThrough) {
              appendPreprocBegin();
              m_passThrough = true;
            }
            break;
          }
        }
      }
    }
  }
}

void SV3_1aPreprocessorTreeListener::exitPragma_directive(
    SV3_1aPpParser::Pragma_directiveContext *ctx) {
  if (!m_inActiveBranch || !m_inProtectedRegion) return;

  if (antlr4::tree::TerminalNode *const identifier = ctx->Simple_identifier()) {
    if (identifier->getText() == "protect") {
      const std::vector<SV3_1aPpParser::Pragma_expressionContext *> &exprs =
          ctx->pragma_expression();
      for (SV3_1aPpParser::Pragma_expressionContext *expr : exprs) {
        if (antlr4::tree::TerminalNode *const exprIdentifier =
                expr->Simple_identifier()) {
          if (exprIdentifier->getText() == "end_protected") {
            addVObject(ctx, VObjectType::ppPragma_directive);

            appendPreprocEnd();
            m_passThrough = false;
            m_inProtectedRegion = false;
            break;
          }
        }
      }
    }
  }
}

void SV3_1aPreprocessorTreeListener::enterComment(
    SV3_1aPpParser::CommentContext *ctx) {
  if (!m_inActiveBranch || m_inMacroDefinitionParsing) return;

  if (antlr4::tree::TerminalNode *const commentNode = ctx->One_line_comment()) {
    const std::string text = commentNode->getText();
    if (std::regex_match(text, m_regexTranslateOff)) {
      m_inProtectedRegion = true;
      if (!m_passThrough) {
        appendPreprocBegin();
        m_passThrough = true;
      }
    } else if (!m_passThrough && std::regex_match(text, m_regexTranslateOn)) {
      appendPreprocBegin();
      m_passThrough = true;
    }
  }
}

void SV3_1aPreprocessorTreeListener::exitComment(
    SV3_1aPpParser::CommentContext *ctx) {
  if (!m_inActiveBranch || m_inMacroDefinitionParsing) return;

  // NOTE(HS): Don't check for protected region because a comment to
  // translate_on is possible without having a translate_off.
  // if (!m_inProtectedRegion) return;

  if (antlr4::tree::TerminalNode *const commentNode = ctx->One_line_comment()) {
    const std::string text = commentNode->getText();
    if (std::regex_match(text, m_regexTranslateOn)) {
      addVObject(ctx, VObjectType::ppComment);

      appendPreprocEnd();
      m_passThrough = false;
      m_inProtectedRegion = false;
    } else if (!m_passThrough &&
               std::regex_match(commentNode->getText(), m_regexTranslateOff)) {
      std::string text = ctx->getText();
      std::string suffix;
      while (!text.empty() && (text.back() == '\n')) {
        suffix += text.back();
        text.pop_back();
      }

      const NodeId nodeId = addVObject(ctx, VObjectType::ppComment);
      appendPreprocEnd();

      if (!suffix.empty()) {
        // Adjust the end location of the object, if needed
        VObject *const object = m_fileContent->MutableObject(nodeId);
        object->m_endLine -= suffix.length();
        const std::string::size_type p = text.rfind('\n');
        object->m_endColumn = (p == std::string::npos)
                                  ? object->m_startColumn + text.length()
                                  : text.length() - p;
      }
    }
  }
}

void SV3_1aPreprocessorTreeListener::enterEveryRule(antlr4::ParserRuleContext *ctx) {
}

void SV3_1aPreprocessorTreeListener::exitEveryRule(antlr4::ParserRuleContext *ctx) {
  bool ignore = !m_passThrough && !m_inMacroDefinitionParsing;
  for (const antlr4::tree::ParseTree *child : ctx->children) {
    if (NodeIdFromContext(child)) {
      ignore = false;
      break;
    }
  }

  const size_t ruleIndex = ctx->getRuleIndex();

  // Ignore a few rule nodes so that it doesn't replace
  // the preprcEnd node that we added explicitly in the tree.
  // Also, cleans up the preproc tree quite a bit.
  if (m_passThrough && (ruleIndex == SV3_1aPpParser::RuleSource_text)) {
    appendPreprocEnd();
    m_passThrough = false;
    ignore = true;
  }

  ignore = ignore || (ruleIndex == SV3_1aPpParser::RuleDescription);
  ignore = ignore || NodeIdFromContext(ctx);
  if (ignore) return;

  // clang-format off
  NodeId nodeId;
  switch (ruleIndex) {
<RULE_CASE_STATEMENTS>
    default: break;
   }
  // clang-format on

  if (nodeId && m_inMacroDefinitionParsing) {
    // When parsing a macro, ensure that the tree
    // doesn't include the terminal newline.
    adjustMacroDefinitionLocation(ctx, nodeId);
  }
}

void SV3_1aPreprocessorTreeListener::visitTerminal(
    antlr4::tree::TerminalNode *node) {
  const antlr4::Token *const token = node->getSymbol();
  if (token->getType() == antlr4::Token::EOF) return;

  const size_t tokenType = token->getType();
  bool shouldAddVObject = (m_pp == m_pp->getSourceFile()) &&
                          (m_passThrough || m_inMacroDefinitionParsing);

  if (shouldAddVObject && m_inMacroDefinitionParsing &&
      (token->getType() == SV3_1aPpParser::CR) && (node->parent != nullptr) &&
      !node->parent->children.empty() &&
      (node->parent->children.back() == node)) {
    // When parsing a macro definition, avoid include he terminal newline.
    shouldAddVObject = false;
  }

  if (shouldAddVObject) {
    // clang-format off
  switch (tokenType) {
<VISIT_CASE_STATEMENTS>
    default: break;
  }
    // clang-format on
  }

  if (m_inMacroDefinitionParsing) {
    // Definition needs special handling to avoid adding the
    // terminal newline. Do nothing here!
  } else if (m_passThrough || m_inProtectedRegion) {
    std::string text = token->getText();
    std::replace_if(
        text.begin(), text.end(), [](char ch) { return ch != '\n'; }, ' ');
    m_pp->append(text);
  } else if (m_inActiveBranch) {
    // Strings need a bit of special handling because the grammar is sort
    // of ambiguous. "String as a rule" show up in macro body but "string
    // show up as token" in pragma parameter but as a rule. We handle
    // "string as a rule" but we need to handle "string as a token"
    // as well and the only way distinguish is by checking the parent type.
    bool skipString = true;
    skipString = skipString && (tokenType == SV3_1aPpParser::STRING);
    skipString = skipString && (node->parent->getTreeType() ==
                                antlr4::tree::ParseTreeType::RULE);
    skipString = skipString &&
                 (((antlr4::ParserRuleContext *)node->parent)->getRuleIndex() ==
                  SV3_1aPpParser::RuleString);
    if (((tokenType != SV3_1aPpParser::STRING) || !skipString) &&
        (tokenType != SV3_1aPpParser::TICK_LINE__) &&
        (tokenType != SV3_1aPpParser::TICK_FILE__) &&
        (tokenType != SV3_1aPpParser::ESCAPED_IDENTIFIER)) {
      m_pp->append(token->getText());
    }
  }
}
}  // namespace SURELOG
