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
 * File:   IncludeFileInfo.h
 * Author: alain
 *
 * Created on July 1, 2018, 10:19 AM
 */

#ifndef INCLUDEFILEINFO_H
#define INCLUDEFILEINFO_H

#include "SourceCompile/SymbolTable.h"

namespace SURELOG {

class IncludeFileInfo {
 public:
  typedef enum { NONE = 0, PUSH = 1, POP = 2 } Action;
  IncludeFileInfo()
      : m_sectionStartLine(0),
        m_sectionFile(0),
        m_originalStartLine(0),
        m_originalStartColumn(0),
        m_originalEndLine(0),
        m_originalEndColumn(0),
        m_type(NONE),
        m_indexOpening(-1),
        m_indexClosing(-1) {}
  IncludeFileInfo(unsigned int sectionStartLine, SymbolId sectionFile,
                  unsigned int originalStartLine,
                  unsigned int originalStartColumn,
                  unsigned int originalEndLine, unsigned int originalEndColumn,
                  Action type)
      : m_sectionStartLine(sectionStartLine),
        m_sectionFile(sectionFile),
        m_originalStartLine(originalStartLine),
        m_originalStartColumn(originalStartColumn),
        m_originalEndLine(originalEndLine),
        m_originalEndColumn(originalEndColumn),
        m_type(type),
        m_indexOpening(-1),
        m_indexClosing(-1) {}
  IncludeFileInfo(const IncludeFileInfo& i)
      : m_sectionStartLine(i.m_sectionStartLine),
        m_sectionFile(i.m_sectionFile),
        m_originalStartLine(i.m_originalStartLine),
        m_originalStartColumn(i.m_originalStartColumn),
        m_originalEndLine(i.m_originalEndLine),
        m_originalEndColumn(i.m_originalEndColumn),
        m_type(i.m_type),
        m_indexOpening(i.m_indexOpening),
        m_indexClosing(i.m_indexClosing) {}
  IncludeFileInfo(unsigned int sectionStartLine, SymbolId sectionFile,
                  unsigned int originalStartLine,
                  unsigned int originalStartColumn,
                  unsigned int originalEndLine, unsigned int originalEndColumn,
                  Action type, int indexOpening, int indexClosing)
      : m_sectionStartLine(sectionStartLine),
        m_sectionFile(sectionFile),
        m_originalStartLine(originalStartLine),
        m_originalStartColumn(originalStartColumn),
        m_originalEndLine(originalEndLine),
        m_originalEndColumn(originalEndColumn),
        m_type(type),
        m_indexOpening(indexOpening),
        m_indexClosing(indexClosing) {}

  unsigned int m_sectionStartLine = 0;
  SymbolId m_sectionFile = 0;
  unsigned int m_originalStartLine = 0;
  unsigned int m_originalStartColumn = 0;
  unsigned int m_originalEndLine = 0;
  unsigned int m_originalEndColumn = 0;
  Action m_type = NONE;  // 1 or 2, push or pop
  int m_indexOpening = 0;
  int m_indexClosing = 0;
};

}  // namespace SURELOG

#endif /* INCLUDEFILEINFO_H */
