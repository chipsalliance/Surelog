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
#include "SourceCompile/AnalyzeFile.h"

#include <ctype.h>
#include <stdio.h>
#include <string.h>

#include <fstream>
#include <iostream>
#include <regex>
#include <sstream>
#include <stack>

#include "Design/Design.h"
#include "Design/DesignElement.h"
#include "Design/TimeInfo.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/ErrorContainer.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/Location.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/IncludeFileInfo.h"
#include "SourceCompile/PreprocessFile.h"
#include "Utils/StringUtils.h"

namespace SURELOG {
namespace fs = std::filesystem;

static void saveContent(const fs::path& fileName, const std::string& content) {
  std::ifstream ifs;
  ifs.open(fileName);
  bool save = true;
  if (ifs.good()) {
    std::string str((std::istreambuf_iterator<char>(ifs)),
                    std::istreambuf_iterator<char>());
    ifs.close();
    if (str == content) save = false;
  }
  if (save) {
    std::ofstream ofs(fileName);
    ofs << content;
    ofs.close();
  }
}

void AnalyzeFile::checkSLlineDirective_(const std::string& line,
                                        unsigned int lineNb) {
  std::stringstream ss(line); /* Storing the whole string into string stream */
  std::string keyword;
  ss >> keyword;
  if (keyword == "SLline") {
    IncludeFileInfo info(0, 0, 0, 0, 0, 0, IncludeFileInfo::NONE);
    ss >> info.m_sectionStartLine;
    std::string file;
    ss >> file;
    file = StringUtils::unquoted(file);
    info.m_sectionFile = m_clp->mutableSymbolTable()->registerSymbol(file);
    unsigned int type = 0;
    ss >> type;

    if (type == IncludeFileInfo::PUSH) {
      // Push
      info.m_originalStartLine = lineNb;
      info.m_type = IncludeFileInfo::PUSH;
      m_includeFileInfo.push(info);
    } else if (type == IncludeFileInfo::POP) {
      // Pop
      if (!m_includeFileInfo.empty()) m_includeFileInfo.pop();
      if (!m_includeFileInfo.empty()) {
        m_includeFileInfo.top().m_sectionFile = info.m_sectionFile;
        m_includeFileInfo.top().m_originalStartLine = lineNb;
        m_includeFileInfo.top().m_sectionStartLine =
            info.m_sectionStartLine - 1;
        m_includeFileInfo.top().m_type = IncludeFileInfo::POP;
      }
    }
  }
}

std::string AnalyzeFile::setSLlineDirective_(unsigned int lineNb,
                                             unsigned int& origFromLine,
                                             fs::path& origFile) {
  std::ostringstream result;
  if (!m_includeFileInfo.empty()) {
    origFile = m_clp->mutableSymbolTable()->getSymbol(
        m_includeFileInfo.top().m_sectionFile);
    const IncludeFileInfo& info = m_includeFileInfo.top();
    origFromLine = lineNb - info.m_originalStartLine + info.m_sectionStartLine;
    result << "SLline " << origFromLine << " \"" << origFile.string() << "\" "
           << 1 << "\n";
  } else {
    result << "";  // BUG or intentional ?
  }
  return result.str();
}

void AnalyzeFile::analyze() {
  std::string line;
  std::vector<std::string> allLines;
  allLines.emplace_back("FILLER LINE");
  if (m_text.empty()) {
    std::ifstream ifs;
    ifs.open(m_ppFileName);
    if (!ifs.good()) {
      return;
    }
    while (std::getline(ifs, line)) {
      allLines.push_back(line);
    }
    ifs.close();
  } else {
    std::stringstream ss(m_text);
    while (std::getline(ss, line)) {
      allLines.push_back(line);
    }
  }
  unsigned int minNbLineForPartitioning = m_clp->getNbLinesForFileSpliting();
  std::vector<FileChunk> fileChunks;
  bool inPackage = false;
  int inClass = 0;
  int inModule = 0;
  bool inProgram = false;
  int inInterface = 0;
  bool inConfig = false;
  bool inChecker = false;
  bool inPrimitive = false;
  // int  inFunction  = false;
  // int  inTask      = false;
  bool inComment = false;
  bool inString = false;
  unsigned int lineNb = 0;
  unsigned int charNb = 0;
  unsigned int startLine = 0;
  unsigned int startChar = 0;
  unsigned int indexPackage = 0;
  unsigned int indexModule = 0;
  int nbPackage = 0, nbClass = 0, nbModule = 0, nbProgram = 0, nbInterface = 0,
      nbConfig = 0, nbChecker = 0,
      nbPrimitive = 0 /*./re   , nbFunction = 0, nbTask = 0*/;
  std::string prev_keyword;
  std::string prev_prev_keyword;
  const std::regex import_regex("import[ ]+[a-zA-Z_0-9:\\*]+[ ]*;");
  std::smatch pieces_match;
  std::string fileLevelImportSection;
  // Parse the file
  for (auto& line : allLines) {
    bool inLineComment = false;
    lineNb++;
    char c = 0;
    char cp = 0;
    std::string keyword;
    for (unsigned int i = 0; i < line.size(); i++) {
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
              for (unsigned int j = i + 1; j < line.size(); j++) {
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
          keyword = "";
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

  unsigned int lineSize = lineNb;

  if (m_clp->getNbMaxProcesses()) {
    m_splitFiles.emplace_back(m_ppFileName);
    m_lineOffsets.push_back(0);
    return;
  }

  if (lineSize < minNbLineForPartitioning) {
    m_splitFiles.emplace_back(m_ppFileName);
    m_lineOffsets.push_back(0);
    return;
  }
  if (m_nbChunks < 2) {
    m_splitFiles.emplace_back(m_ppFileName);
    m_lineOffsets.push_back(0);
    return;
  }

  if (inComment || inString) {
    m_splitFiles.clear();
    m_lineOffsets.clear();
    Location loc(
        0, 0, 0,
        m_clp->mutableSymbolTable()->registerSymbol(m_fileName.string()));
    Error err(ErrorDefinition::PA_CANNOT_SPLIT_FILE, loc);
    m_clp->getErrorContainer()->addError(err);
    m_clp->getErrorContainer()->printMessages();
    return;
  }

  // Split the file

  unsigned int chunkSize = lineSize / m_nbChunks;
  int chunkNb = 0;

  unsigned int fromLine = 1;
  unsigned int toIndex = 0;
  m_includeFileInfo.emplace(
      1, m_clp->mutableSymbolTable()->registerSymbol(m_fileName.string()), 1, 0,
      1, 0, IncludeFileInfo::PUSH);
  unsigned int linesWriten = 0;
  for (unsigned int i = 0; i < fileChunks.size(); i++) {
    DesignElement::ElemType chunkType = fileChunks[i].m_chunkType;

    // The case of a package or a module
    if (chunkType == DesignElement::ElemType::Package ||
        chunkType == DesignElement::ElemType::Module) {
      std::string packageDeclaration;
      std::string importSection;
      unsigned int packagelastLine = fileChunks[i].m_toLine;
      packageDeclaration = allLines[fileChunks[i].m_fromLine];
      for (unsigned hi = fileChunks[i].m_fromLine; hi < fileChunks[i].m_toLine;
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
        unsigned int origFromLine = 0;
        fs::path origFile;
        // unsigned int baseFromLine = fromLine;
        while (!endPackageDetected) {
          std::string content;
          bool actualContent = false;
          bool finishPackage = false;
          bool hitLimit = true;
          for (unsigned int j = i + 1; j < fileChunks.size(); j++) {
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
          unsigned int toLine = fileChunks[toIndex].m_toLine + 1;
          if (finishPackage) {
            toLine = packagelastLine + 1;
          }
          if (toIndex == fileChunks.size() - 1) {
            toLine = allLines.size();
          }

          if (splitted) {
            content += sllineInfo;
            content += packageDeclaration + "  " + importSection;
            // content += "SLline " + std::to_string(fromLine - baseFromLine +
            // origFromLine + 1) + " \"" + origFile + "\" 1";
          } else {
            sllineInfo = setSLlineDirective_(fromLine, origFromLine, origFile);
            content = sllineInfo;
          }

          bool inString = false;
          bool inComment = false;

          m_lineOffsets.push_back(linesWriten);

          // Detect end of package or end of module
          for (unsigned int l = fromLine; l < toLine; l++) {
            const std::string& line = allLines[l];
            checkSLlineDirective_(line, l);

            bool inLineComment = false;
            content += allLines[l];
            if (l == fileChunks[i].m_fromLine) {
              content += "  " + importSection;
            }
            if (l != (toLine - 1)) {
              content += "\n";
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
              content += "  endpackage  ";
            if ((chunkType == DesignElement::Module) &&
                endPackageDetected == false)
              content += "  endmodule  ";
          } else {
            splitted = false;
          }

          fs::path splitFileName =
              m_ppFileName.string() + ".ck" + std::to_string(chunkNb);
          if (chunkNb > 1000) {
            m_splitFiles.clear();
            m_lineOffsets.clear();
            Location loc(0, 0, 0,
                         m_clp->mutableSymbolTable()->registerSymbol(
                             m_fileName.string()));
            Error err(ErrorDefinition::PA_CANNOT_SPLIT_FILE, loc);
            m_clp->getErrorContainer()->addError(err);
            m_clp->getErrorContainer()->printMessages();
            return;
          }
          content += "  " + fileLevelImportSection;
          saveContent(splitFileName, content);

          m_splitFiles.emplace_back(splitFileName);

          // m_lineOffsets.push_back(fromLine - 1);

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
        unsigned int packagelastLine = fileChunks[i].m_toLine;
        unsigned int toLine = fileChunks[i].m_toLine + 1;
        if (i == fileChunks.size() - 1) {
          toLine = allLines.size() - 1;
        }
        const char* temp = allLines[toLine].c_str();
        if (strstr(temp, "/*") && (!strstr(temp, "*/"))) {
          m_splitFiles.clear();
          m_lineOffsets.clear();
          Location loc(
              0, 0, 0,
              m_clp->mutableSymbolTable()->registerSymbol(m_fileName.string()));
          Error err(ErrorDefinition::PA_CANNOT_SPLIT_FILE, loc);
          m_clp->getErrorContainer()->addError(err);
          m_clp->getErrorContainer()->printMessages();
          return;
        }

        if (i == fileChunks.size() - 1) {
          toLine = allLines.size();
        }

        unsigned int origFromLine = 0;
        fs::path origFile;

        m_lineOffsets.push_back(linesWriten);

        content += setSLlineDirective_(fromLine, origFromLine, origFile);
        for (unsigned int l = fromLine; l < toLine; l++) {
          checkSLlineDirective_(allLines[l], l);
          content += allLines[l];
          if (l != (toLine - 1)) {
            content += "\n";
          }
          linesWriten++;
        }

        fs::path splitFileName =
            m_ppFileName.string() + ".ck" + std::to_string(chunkNb);
        if (chunkNb > 1000) {
          m_splitFiles.clear();
          m_lineOffsets.clear();
          Location loc(
              0, 0, 0,
              m_clp->mutableSymbolTable()->registerSymbol(m_fileName.string()));
          Error err(ErrorDefinition::PA_CANNOT_SPLIT_FILE, loc);
          m_clp->getErrorContainer()->addError(err);
          m_clp->getErrorContainer()->printMessages();
          return;
        }
        saveContent(splitFileName, content);

        m_splitFiles.emplace_back(splitFileName);

        // m_lineOffsets.push_back (fromLine-1);

        chunkNb++;
        for (unsigned int j = i; j < fileChunks.size(); j++) {
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
      for (unsigned int j = i; j < fileChunks.size(); j++) {
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
      unsigned int toLine = fileChunks[toIndex].m_toLine + 1;
      if (toIndex == fileChunks.size() - 1) {
        toLine = allLines.size();
      }
      unsigned int origFromLine = 0;
      fs::path origFile;

      m_lineOffsets.push_back(linesWriten);

      content += setSLlineDirective_(fromLine, origFromLine, origFile);
      content += "  " + fileLevelImportSection;
      for (unsigned int l = fromLine; l < toLine; l++) {
        checkSLlineDirective_(allLines[l], l);
        content += allLines[l];
        if (l != (toLine - 1)) {
          content += "\n";
        }
        linesWriten++;
      }

      fs::path splitFileName =
          m_ppFileName.string() + ".ck" + std::to_string(chunkNb);
      if (chunkNb > 1000) {
        m_splitFiles.clear();
        m_lineOffsets.clear();
        Location loc(
            0, 0, 0,
            m_clp->mutableSymbolTable()->registerSymbol(m_fileName.string()));
        Error err(ErrorDefinition::PA_CANNOT_SPLIT_FILE, loc);
        m_clp->getErrorContainer()->addError(err);
        m_clp->getErrorContainer()->printMessages();
        return;
      }
      saveContent(splitFileName, content);

      m_splitFiles.emplace_back(splitFileName);

      chunkNb++;

      fromLine = fileChunks[toIndex].m_toLine + 1;
      i = toIndex;
    }
  }
}
}  // namespace SURELOG
