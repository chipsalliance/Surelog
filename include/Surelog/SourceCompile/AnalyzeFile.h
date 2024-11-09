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
#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

class CommandLineParser;
class Design;
class SymbolTable;

class AnalyzeFile final {
 public:
  class FileChunk final {
   public:
    FileChunk(DesignElement::ElemType type, uint64_t from, uint64_t to,
              uint64_t startChar, uint64_t endChar)
        : m_chunkType(type),
          m_fromLine(from),
          m_toLine(to),
          m_excludeLineFrom(0),
          m_excludeLineTo(0),
          m_startChar(startChar),
          m_endChar(endChar) {}
    DesignElement::ElemType m_chunkType;
    uint64_t m_fromLine;
    uint64_t m_toLine;
    uint64_t m_excludeLineFrom;
    uint64_t m_excludeLineTo;
    uint64_t m_startChar;
    uint64_t m_endChar;
  };

  AnalyzeFile(CommandLineParser* clp, Design* design, PathId ppFileId,
              PathId fileId, int32_t nbChunks, std::string_view text = "")
      : m_clp(clp),
        m_design(design),
        m_ppFileId(ppFileId),
        m_fileId(fileId),
        m_nbChunks(nbChunks),
        m_text(text) {}

  void analyze();
  const std::vector<PathId>& getSplitFiles() const { return m_splitFiles; }
  const std::vector<uint32_t>& getLineOffsets() const { return m_lineOffsets; }

  AnalyzeFile(const AnalyzeFile& orig) = delete;
  ~AnalyzeFile() = default;

 private:
  void checkSLlineDirective_(std::string_view line, uint32_t lineNb);
  std::string setSLlineDirective_(uint32_t lineNb);
  CommandLineParser* const m_clp = nullptr;
  Design* const m_design = nullptr;
  PathId m_ppFileId;
  PathId m_fileId;
  std::vector<FileChunk> m_fileChunks;
  std::vector<PathId> m_splitFiles;
  std::vector<uint32_t> m_lineOffsets;
  int32_t m_nbChunks;
  std::stack<IncludeFileInfo> m_includeFileInfo;
  std::string m_text;  // unit test
};

};  // namespace SURELOG

#endif /* SURELOG_ANALYZEFILE_H */
