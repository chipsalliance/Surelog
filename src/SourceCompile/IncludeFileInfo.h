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

namespace SURELOG {

class IncludeFileInfo {
 public:
  IncludeFileInfo()
      : m_sectionStartLine(0),
        m_sectionFile(0),
        m_originalLine(0),
        m_type(0),
        m_indexOpening(-1),
        m_indexClosing(-1) {}
  IncludeFileInfo(unsigned int sectionStartLine, SymbolId sectionFile,
                  unsigned int originalLine, unsigned int type)
      : m_sectionStartLine(sectionStartLine),
        m_sectionFile(sectionFile),
        m_originalLine(originalLine),
        m_type(type),
        m_indexOpening(-1),
        m_indexClosing(-1) {}
  IncludeFileInfo(const IncludeFileInfo& i)
      : m_sectionStartLine(i.m_sectionStartLine),
        m_sectionFile(i.m_sectionFile),
        m_originalLine(i.m_originalLine),
        m_type(i.m_type),
        m_indexOpening(i.m_indexOpening),
        m_indexClosing(i.m_indexClosing) {}
  unsigned int m_sectionStartLine;
  SymbolId m_sectionFile;
  unsigned int m_originalLine;
  unsigned int m_type;  // 1 or 2, push or pop
  int m_indexOpening;
  int m_indexClosing;
};

};  // namespace SURELOG

#endif /* INCLUDEFILEINFO_H */
