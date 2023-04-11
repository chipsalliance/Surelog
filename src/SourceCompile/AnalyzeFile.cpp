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
 * File:   AnalyzeFile.cpp
 * Author: alain
 *
 * Created on July 23, 2017, 11:05 PM
 */

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/FileSystem.h>
#include <Surelog/Design/Design.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/SourceCompile/AnalyzeFile.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/StringUtils.h>

#include <regex>
#include <sstream>

namespace SURELOG {
void AnalyzeFile::checkSLlineDirective_(std::string_view line,
                                        uint32_t lineNb) {
  std::stringstream ss(
      (std::string(line))); /* Storing the whole string into string stream */
  std::string keyword;
  ss >> keyword;
  if (keyword == "SLline") {
    IncludeFileInfo info(IncludeFileInfo::Context::NONE, 0, BadSymbolId,
                         BadPathId, 0, 0, 0, 0, IncludeFileInfo::Action::NONE);
    ss >> info.m_sectionStartLine;
    std::string text;
    ss >> text;
    text = StringUtils::unquoted(text);
    std::vector<std::string_view> parts;
    StringUtils::tokenize(text, "^", parts);
    std::string_view symbol = StringUtils::unquoted(parts[0]);
    std::string_view file = StringUtils::unquoted(parts[1]);
    info.m_sectionSymbolId = m_clp->getSymbolTable()->registerSymbol(symbol);
    info.m_sectionFileId =
        FileSystem::getInstance()->toPathId(file, m_clp->getSymbolTable());
    uint32_t action = 0;
    ss >> action;

    if (static_cast<IncludeFileInfo::Action>(action) ==
        IncludeFileInfo::Action::PUSH) {
      // Push
      info.m_originalStartLine = lineNb;
      info.m_action = IncludeFileInfo::Action::PUSH;
      m_includeFileInfo.push(info);
    } else if (static_cast<IncludeFileInfo::Action>(action) ==
               IncludeFileInfo::Action::POP) {
      // Pop
      if (!m_includeFileInfo.empty()) m_includeFileInfo.pop();
      if (!m_includeFileInfo.empty()) {
        IncludeFileInfo& top = m_includeFileInfo.top();
        top.m_sectionSymbolId = info.m_sectionSymbolId;
        top.m_sectionFileId = info.m_sectionFileId;
        top.m_originalStartLine = lineNb;
        top.m_sectionStartLine = info.m_sectionStartLine - 1;
        top.m_action = IncludeFileInfo::Action::POP;
      }
    }
  }
}

std::string AnalyzeFile::setSLlineDirective_(uint32_t lineNb) {
  std::ostringstream result;
  if (!m_includeFileInfo.empty()) {
    FileSystem* const fileSystem = FileSystem::getInstance();
    const IncludeFileInfo& info = m_includeFileInfo.top();
    uint32_t origFromLine =
        lineNb - info.m_originalStartLine + info.m_sectionStartLine;
    result << "SLline " << origFromLine << " "
           << m_clp->getSymbolTable()->getSymbol(info.m_sectionSymbolId) << "^"
           << fileSystem->toPath(m_includeFileInfo.top().m_sectionFileId)
           << " 1" << std::endl;
  } else {
    result << "";  // BUG or intentional ?
  }
  return result.str();
}

void AnalyzeFile::analyze() {
  FileSystem* const fileSystem = FileSystem::getInstance();
  SymbolTable* const symbolTable = m_clp->getSymbolTable();
  ErrorContainer* const errors = m_clp->getErrorContainer();

  std::vector<std::string> allLines;
  allLines.emplace_back("FILLER LINE");
  if (m_text.empty()) {
    fileSystem->readLines(m_ppFileId, allLines);
  } else {
    std::string line;
    std::stringstream ss(m_text);
    while (std::getline(ss, line)) {
      while (!line.empty() &&
             ((line.back() == '\r') || (line.back() == '\n'))) {
        line.pop_back();
      }
      allLines.emplace_back(line);
    }
  }
  if (allLines.empty()) return;

  uint32_t minNbLineForPartitioning = m_clp->getNbLinesForFileSpliting();
  std::vector<FileChunk> fileChunks;
  bool inPackage = false;
  int32_t inClass = 0;
  int32_t inModule = 0;
  bool inProgram = false;
  int32_t inInterface = 0;
  bool inConfig = false;
  bool inChecker = false;
  bool inPrimitive = false;
  // int32_t  inFunction  = false;
  // int32_t  inTask      = false;
  bool inComment = false;
  bool inString = false;
  uint32_t lineNb = 0;
  uint32_t charNb = 0;
  uint32_t startLine = 0;
  uint32_t startChar = 0;
  uint32_t indexPackage = 0;
  uint32_t indexModule = 0;
  int32_t nbPackage = 0;
  int32_t nbClass = 0;
  int32_t nbModule = 0;
  int32_t nbProgram = 0;
  int32_t nbInterface = 0;
  int32_t nbConfig = 0;
  int32_t nbChecker = 0;
  int32_t nbPrimitive = 0 /*./re   , nbFunction = 0, nbTask = 0*/;
  std::string prev_keyword;
  std::string prev_prev_keyword;
  const std::regex import_regex("import[ ]+[a-zA-Z_0-9:\\*]+[ ]*;");
  std::smatch pieces_match;
  std::string fileLevelImportSection;
  // Parse the file
  for (const auto& line : allLines) {
    bool inLineComment = false;
    lineNb++;
    char c = 0;
    char cp = 0;
    std::string keyword;
    for (uint32_t i = 0; i < line.size(); i++) {
      charNb++;
      c = line[i];
      if (cp == '/' && c == '*') {
        if (!inLineComment) inComment = true;
      } else if (cp == '/' && c == '/') {
        if ((!inComment) && (!inString)) inLineComment = true;
      } else if (cp == '*' && c == '/') {
        inComment = false;
      } else if (cp != '\\' && c == '\"') {
        if ((!inLineComment) && (!inComment)) inString = !inString;
      }
      if ((!inComment) && (!inLineComment) && (!inString)) {
        if ((islower(c) || isupper(c) || c == '_') &&
            (i != (line.size() - 1))) {
          keyword += c;
        } else {
          if ((islower(c) || isupper(c) || c == '_') &&
              (i == (line.size() - 1))) {
            keyword += c;
          }

          if (keyword == "package") {
            std::string packageName;
            if (line[i] == ' ') {
              for (uint32_t j = i + 1; j < line.size(); j++) {
                if (line[j] == ';') break;
                if (line[j] == ':') break;
                if (line[j] != ' ') packageName += line[j];
              }
            }
            if (!packageName.empty()) m_design->addOrderedPackage(packageName);
            inPackage = true;
            startLine = lineNb;
            startChar = charNb;
            fileChunks.emplace_back(DesignElement::ElemType::Package, startLine,
                                    0, startChar, 0);
            indexPackage = fileChunks.size() - 1;
          }
          if (keyword == "endpackage") {
            if (inPackage) {
              fileChunks[indexPackage].m_toLine = lineNb;
              fileChunks[indexPackage].m_endChar = charNb;
              nbPackage++;
            }
            inPackage = false;
            // std::cout << "PACKAGE:" <<
            // allLines[fileChunks[indexPackage].m_fromLine] << " f:" <<
            // fileChunks[indexPackage].m_fromLine
            //        << " t:" << fileChunks[indexPackage].m_toLine <<
            //        std::endl;
          }
          if (keyword == "module") {
            if (inModule == 0) {
              startLine = lineNb;
              startChar = charNb;
              fileChunks.emplace_back(DesignElement::ElemType::Module,
                                      startLine, 0, startChar, 0);
              indexModule = fileChunks.size() - 1;
            }
            inModule++;
          }
          if (keyword == "endmodule") {
            if (inModule == 1) {
              fileChunks[indexModule].m_toLine = lineNb;
              fileChunks[indexModule].m_endChar = charNb;
              nbModule++;
            }
            inModule--;
          }
          /*
          if (keyword == "function" && (prev_keyword != "context") &&
          (prev_prev_keyword != "import"))
            {
              if ((inClass == 0) && (inInterface == 0) && (inModule == 0))
                {
                  if (inFunction == false)
                    {
                      startLine = lineNb;
                      startChar = charNb;
                    }
                  inFunction = true;
                }
            }
          if (keyword == "endfunction")
            {
               if (inFunction == true)
                 {
                   FileChunk chunk (DesignElement::ElemType::Function,
          startLine, lineNb, startChar, charNb); fileChunks.push_back (chunk);
                   nbFunction++;
                 }
              inFunction = false;
            }
          if (keyword == "task")
            {
              if ((inClass == 0) && (inInterface == 0) && (inModule == 0))
                {
                  if (inTask == false)
                    {
                      startLine = lineNb;
                      startChar = charNb;
                    }
                  inTask = true;
                }
            }
          if (keyword == "endtask")
            {
               if (inTask == true)
                 {
                   FileChunk chunk (DesignElement::ElemType::Task, startLine,
          lineNb, startChar, charNb); fileChunks.push_back (chunk); nbTask++;
                 }
              inTask = false;
            }
           */
          if (keyword == "class" && (prev_keyword != "typedef")) {
            if (inClass == 0) {
              startLine = lineNb;
              startChar = charNb;
            }
            inClass++;
          }
          if (keyword == "endclass") {
            if (inClass == 1) {
              fileChunks.emplace_back(DesignElement::ElemType::Class, startLine,
                                      lineNb, startChar, charNb);
              nbClass++;
            }
            inClass--;
          }
          if (keyword == "interface") {
            if (inInterface == 0) {
              startLine = lineNb;
              startChar = charNb;
            }
            inInterface++;
          }
          if (keyword == "endinterface") {
            if (inInterface == 1) {
              fileChunks.emplace_back(DesignElement::ElemType::Interface,
                                      startLine, lineNb, startChar, charNb);
              nbInterface++;
            }
            inInterface--;
          }
          if (keyword == "config") {
            startLine = lineNb;
            startChar = charNb;
            inConfig = true;
          }
          if (keyword == "endconfig") {
            if (inConfig) {
              fileChunks.emplace_back(DesignElement::ElemType::Config,
                                      startLine, lineNb, startChar, charNb);
              nbConfig++;
            }
            inConfig = false;
          }
          if (keyword == "checker") {
            startLine = lineNb;
            startChar = charNb;
            inChecker = true;
          }
          if (keyword == "endchecker") {
            if (inChecker) {
              fileChunks.emplace_back(DesignElement::ElemType::Checker,
                                      startLine, lineNb, startChar, charNb);
              nbChecker++;
            }
            inChecker = false;
          }
          if (keyword == "program") {
            startLine = lineNb;
            startChar = charNb;
            inProgram = true;
          }
          if (keyword == "endprogram") {
            if (inProgram) {
              fileChunks.emplace_back(DesignElement::ElemType::Program,
                                      startLine, lineNb, startChar, charNb);
              nbProgram++;
            }
            inProgram = false;
          }
          if (keyword == "primitive") {
            startLine = lineNb;
            startChar = charNb;
            inPrimitive = true;
          }
          if (keyword == "endprimitive") {
            if (inPrimitive) {
              fileChunks.emplace_back(DesignElement::ElemType::Primitive,
                                      startLine, lineNb, startChar, charNb);
              nbPrimitive++;
            }
            inPrimitive = false;
          }
          if (!keyword.empty()) {
            if (!prev_keyword.empty()) {
              prev_prev_keyword = prev_keyword;
            }
            prev_keyword = keyword;
          }
          keyword.clear();
        }
      }
      cp = c;
    }

    if ((!inPackage) && (!inClass) && (!inModule) && (!inProgram) &&
        (!inInterface) && (!inConfig) && (!inChecker) && (!inPrimitive) &&
        (!inComment) && (!inString)) {
      if (std::regex_search(line, pieces_match, import_regex)) {
        fileLevelImportSection += line;
      }
    }
  }

  uint32_t lineSize = lineNb;

  if (m_clp->getNbMaxProcesses() || (lineSize < minNbLineForPartitioning) ||
      (m_nbChunks < 2)) {
    m_splitFiles.emplace_back(m_ppFileId);
    m_lineOffsets.push_back(0);
    return;
  }

  if (inComment || inString) {
    m_splitFiles.clear();
    m_lineOffsets.clear();
    Location loc(m_fileId);
    Error err(ErrorDefinition::PA_CANNOT_SPLIT_FILE, loc);
    errors->addError(err);
    errors->printMessages();
    return;
  }

  // Split the file

  uint32_t chunkSize = lineSize / m_nbChunks;
  int32_t chunkNb = 0;

  uint32_t fromLine = 1;
  uint32_t toIndex = 0;
  m_includeFileInfo.emplace(IncludeFileInfo::Context::INCLUDE, 1, BadSymbolId,
                            m_fileId, 1, 0, 1, 0,
                            IncludeFileInfo::Action::PUSH);
  uint32_t linesWriten = 0;
  for (uint32_t i = 0; i < fileChunks.size(); i++) {
    DesignElement::ElemType chunkType = fileChunks[i].m_chunkType;

    // The case of a package or a module
    if (chunkType == DesignElement::ElemType::Package ||
        chunkType == DesignElement::ElemType::Module) {
      std::string packageDeclaration;
      std::string importSection;
      uint32_t packagelastLine = fileChunks[i].m_toLine;
      packageDeclaration = allLines[fileChunks[i].m_fromLine];
      for (uint32_t hi = fileChunks[i].m_fromLine; hi < fileChunks[i].m_toLine;
           hi++) {
        std::string header = allLines[hi];
        if (std::regex_search(header, pieces_match, import_regex)) {
          importSection += header;
        }
      }
      // Break up package or module
      if ((fileChunks[i].m_toLine - fileChunks[i].m_fromLine) > chunkSize) {
        bool splitted = false;
        bool endPackageDetected = false;
        std::string sllineInfo;
        // uint32_t baseFromLine = fromLine;
        while (!endPackageDetected) {
          std::string content;
          bool actualContent = false;
          bool finishPackage = false;
          bool hitLimit = true;
          for (uint32_t j = i + 1; j < fileChunks.size(); j++) {
            hitLimit = false;
            if (fileChunks[j].m_fromLine > packagelastLine) {
              finishPackage = true;
              toIndex = j - 1;
              break;
            }

            if ((fileChunks[j].m_toLine - fromLine) >= chunkSize) {
              toIndex = j;
              break;
            }
            if (j == (fileChunks.size() - 1)) {
              toIndex = j;
              break;
            }
            toIndex = j;
          }
          if (hitLimit) {
            toIndex = fileChunks.size() - 1;
          }
          uint32_t toLine = fileChunks[toIndex].m_toLine + 1;
          if (finishPackage) {
            toLine = packagelastLine + 1;
          }
          if (toIndex == fileChunks.size() - 1) {
            toLine = allLines.size();
          }

          if (splitted) {
            StrAppend(&content, sllineInfo, packageDeclaration, "  ",
                      importSection);
            // content += "SLline " + std::to_string(fromLine - baseFromLine +
            // origFromLine + 1) + " \"" + origFile + "\" 1";
          } else {
            sllineInfo = setSLlineDirective_(fromLine);
            content = sllineInfo;
          }

          bool inString = false;
          bool inComment = false;

          m_lineOffsets.push_back(linesWriten);

          // Detect end of package or end of module
          for (uint32_t l = fromLine; l < toLine; l++) {
            const std::string& line = allLines[l];
            checkSLlineDirective_(line, l);

            bool inLineComment = false;
            StrAppend(&content, allLines[l]);
            if (l == fileChunks[i].m_fromLine) {
              StrAppend(&content, "  ", importSection);
            }
            if (l != (toLine - 1)) {
              StrAppend(&content, "\n");
            }
            linesWriten++;

            actualContent = true;
            char cp = 0;
            std::string keyword;
            for (char c : line) {
              if (cp == '/' && c == '*') {
                if (!inLineComment) inComment = true;
              } else if (cp == '/' && c == '/') {
                if (!inComment) inLineComment = true;
              } else if (cp == '*' && c == '/') {
                inComment = false;
              } else if (cp != '\\' && c == '\"') {
                if ((!inLineComment) && (!inComment)) inString = !inString;
              }
              if ((!inComment) && (!inLineComment) && (!inString)) {
                if (std::isalpha(static_cast<unsigned char>(c)) || (c == '_')) {
                  keyword += c;
                }
              }
              cp = c;
            }
            if ((chunkType == DesignElement::Package) &&
                (keyword == "endpackage"))
              endPackageDetected = true;
            if ((chunkType == DesignElement::Module) &&
                (keyword == "endmodule"))
              endPackageDetected = true;
          }

          if (actualContent) {
            splitted = true;
            if ((chunkType == DesignElement::Package) &&
                endPackageDetected == false)
              StrAppend(&content, "  endpackage  ");
            if ((chunkType == DesignElement::Module) &&
                endPackageDetected == false)
              StrAppend(&content, "  endmodule  ");
          } else {
            splitted = false;
          }

          if (chunkNb > 1000) {
            m_splitFiles.clear();
            m_lineOffsets.clear();
            Location loc(m_fileId);
            Error err(ErrorDefinition::PA_CANNOT_SPLIT_FILE, loc);
            errors->addError(err);
            errors->printMessages();
            return;
          }
          StrAppend(&content, "  ", fileLevelImportSection);

          const PathId splitFileId =
              fileSystem->getChunkFile(m_ppFileId, chunkNb, symbolTable);
          fileSystem->writeContent(splitFileId, content);
          m_splitFiles.emplace_back(splitFileId);

          chunkNb++;
          fromLine = fileChunks[toIndex].m_toLine + 1;

          i = toIndex;
          if (finishPackage) {
            fromLine = toLine;
          }
          if (i >= fileChunks.size() - 1) {
            break;
          }
        }
      } else {
        // Split the complete package/module in a file
        std::string content;
        uint32_t packagelastLine = fileChunks[i].m_toLine;
        uint32_t toLine = fileChunks[i].m_toLine + 1;
        if (i == fileChunks.size() - 1) {
          toLine = allLines.size() - 1;
        }
        if ((allLines[toLine].find("/*") != std::string::npos) &&
            (allLines[toLine].find("*/") == std::string::npos)) {
          m_splitFiles.clear();
          m_lineOffsets.clear();
          Location loc(m_fileId);
          Error err(ErrorDefinition::PA_CANNOT_SPLIT_FILE, loc);
          errors->addError(err);
          errors->printMessages();
          return;
        }

        if (i == fileChunks.size() - 1) {
          toLine = allLines.size();
        }
        m_lineOffsets.push_back(linesWriten);

        StrAppend(&content, setSLlineDirective_(fromLine));
        for (uint32_t l = fromLine; l < toLine; l++) {
          checkSLlineDirective_(allLines[l], l);
          StrAppend(&content, allLines[l]);
          if (l != (toLine - 1)) {
            StrAppend(&content, "\n");
          }
          linesWriten++;
        }

        if (chunkNb > 1000) {
          m_splitFiles.clear();
          m_lineOffsets.clear();
          Location loc(m_fileId);
          Error err(ErrorDefinition::PA_CANNOT_SPLIT_FILE, loc);
          errors->addError(err);
          errors->printMessages();
          return;
        }

        PathId splitFileId =
            fileSystem->getChunkFile(m_ppFileId, chunkNb, symbolTable);
        fileSystem->writeContent(splitFileId, content);
        m_splitFiles.emplace_back(splitFileId);

        chunkNb++;
        for (uint32_t j = i; j < fileChunks.size(); j++) {
          if ((fileChunks[j].m_toLine > packagelastLine)) {
            break;
          }
          if (j == (fileChunks.size() - 1)) {
            toIndex = j;
            break;
          }
          toIndex = j;
        }

        fromLine = packagelastLine + 1;
        i = toIndex;
      }
    }
    // The case of classes and other chunks
    else {
      for (uint32_t j = i; j < fileChunks.size(); j++) {
        if (fileChunks[j].m_chunkType == DesignElement::ElemType::Package) {
          break;
        }
        if ((fileChunks[j].m_toLine - fromLine) >= chunkSize) {
          toIndex = j;
          break;
        }
        if (j == (fileChunks.size() - 1)) {
          toIndex = j;
          break;
        }
        toIndex = j;
      }

      std::string content;
      uint32_t toLine = fileChunks[toIndex].m_toLine + 1;
      if (toIndex == fileChunks.size() - 1) {
        toLine = allLines.size();
      }
      m_lineOffsets.push_back(linesWriten);

      StrAppend(&content, setSLlineDirective_(fromLine));
      StrAppend(&content, "  ", fileLevelImportSection);
      for (uint32_t l = fromLine; l < toLine; l++) {
        checkSLlineDirective_(allLines[l], l);
        StrAppend(&content, allLines[l]);
        if (l != (toLine - 1)) {
          StrAppend(&content, "\n");
        }
        linesWriten++;
      }

      if (chunkNb > 1000) {
        m_splitFiles.clear();
        m_lineOffsets.clear();
        Location loc(m_fileId);
        Error err(ErrorDefinition::PA_CANNOT_SPLIT_FILE, loc);
        errors->addError(err);
        errors->printMessages();
        return;
      }

      PathId splitFileId =
          fileSystem->getChunkFile(m_ppFileId, chunkNb, symbolTable);
      fileSystem->writeContent(splitFileId, content);
      m_splitFiles.emplace_back(splitFileId);

      chunkNb++;

      fromLine = fileChunks[toIndex].m_toLine + 1;
      i = toIndex;
    }
  }
}
}  // namespace SURELOG
