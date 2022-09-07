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

#include <Surelog/Common/PathId.h>
#include <Surelog/Design/DesignElement.h>
#include <Surelog/SourceCompile/IncludeFileInfo.h>

#include <stack>
#include <vector>

namespace SURELOG {

class CommandLineParser;
class Design;
class SymbolTable;

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

  AnalyzeFile(CommandLineParser* clp, Design* design, PathId ppFileId,
              PathId fileId, int nbChunks, const std::string& text = "")
      : m_clp(clp),
        m_design(design),
        m_ppFileId(ppFileId),
        m_fileId(fileId),
        m_nbChunks(nbChunks),
        m_text(text) {}

  void analyze();
  const std::vector<PathId>& getSplitFiles() const { return m_splitFiles; }
  const std::vector<unsigned int>& getLineOffsets() const {
    return m_lineOffsets;
  }

  AnalyzeFile(const AnalyzeFile& orig) = delete;
  virtual ~AnalyzeFile() = default;

 private:
  void checkSLlineDirective_(const std::string& line, unsigned int lineNb);
  std::string setSLlineDirective_(unsigned int lineNb,
                                  unsigned int& origFromLine,
                                  PathId& origFileId);
  CommandLineParser* m_clp;
  Design* m_design;
  PathId m_ppFileId;
  PathId m_fileId;
  std::vector<FileChunk> m_fileChunks;
  std::vector<PathId> m_splitFiles;
  std::vector<unsigned int> m_lineOffsets;
  int m_nbChunks;
  std::stack<IncludeFileInfo> m_includeFileInfo;
  std::string m_text;  // unit test
};

};  // namespace SURELOG

#endif /* SURELOG_ANALYZEFILE_H */
