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
 * File:   AnalyzeFile.h
 * Author: alain
 *
 * Created on July 23, 2017, 11:05 PM
 */

#ifndef SURELOG_ANALYZEFILE_H
#define SURELOG_ANALYZEFILE_H
#pragma once

#include <filesystem>
#include <stack>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Design/Design.h"
#include "Surelog/Design/DesignElement.h"
#include "Surelog/SourceCompile/IncludeFileInfo.h"
#include "Surelog/SourceCompile/SymbolTable.h"

namespace SURELOG {
class Design;

class AnalyzeFile {
 public:
  class FileChunk {
   public:
    FileChunk(DesignElement::ElemType type, unsigned long from,
              unsigned long to, unsigned long startChar, unsigned long endChar)
        : m_chunkType(type),
          m_fromLine(from),
          m_toLine(to),
          m_excludeLineFrom(0),
          m_excludeLineTo(0),
          m_startChar(startChar),
          m_endChar(endChar) {}
    DesignElement::ElemType m_chunkType;
    unsigned long m_fromLine;
    unsigned long m_toLine;
    unsigned long m_excludeLineFrom;
    unsigned long m_excludeLineTo;
    unsigned long m_startChar;
    unsigned long m_endChar;
  };

  AnalyzeFile(CommandLineParser* clp, Design* design,
              const std::filesystem::path& ppFileName,
              const std::filesystem::path& fileName, int nbChunks,
              const std::string& text = "")
      : m_clp(clp),
        m_design(design),
        m_ppFileName(ppFileName),
        m_fileName(fileName),
        m_nbChunks(nbChunks),
        m_text(text) {}

  void analyze();
  std::vector<std::filesystem::path>& getSplitFiles() { return m_splitFiles; }
  std::vector<unsigned int>& getLineOffsets() { return m_lineOffsets; }

  AnalyzeFile(const AnalyzeFile& orig) = delete;
  virtual ~AnalyzeFile() {}

 private:
  void checkSLlineDirective_(const std::string& line, unsigned int lineNb);
  std::string setSLlineDirective_(unsigned int lineNb,
                                  unsigned int& origFromLine,
                                  std::filesystem::path& origFile);
  CommandLineParser* m_clp;
  Design* m_design;
  std::filesystem::path m_ppFileName;
  std::filesystem::path m_fileName;
  std::vector<FileChunk> m_fileChunks;
  std::vector<std::filesystem::path> m_splitFiles;
  std::vector<unsigned int> m_lineOffsets;
  int m_nbChunks;
  std::stack<IncludeFileInfo> m_includeFileInfo;
  std::string m_text;  // unit test
};

};  // namespace SURELOG

#endif /* SURELOG_ANALYZEFILE_H */
