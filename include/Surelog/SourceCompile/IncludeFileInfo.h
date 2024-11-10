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

#ifndef SURELOG_INCLUDEFILEINFO_H
#define SURELOG_INCLUDEFILEINFO_H
#pragma once

#include <Surelog/Common/PathId.h>
#include <Surelog/Common/SymbolId.h>

#include <cstdint>

namespace SURELOG {

class IncludeFileInfo {
 public:
  enum class Context : uint32_t { NONE = 0, INCLUDE = 1, MACRO = 2 };
  enum class Action : uint32_t { NONE = 0, PUSH = 1, POP = 2 };

  IncludeFileInfo(Context context, uint32_t sectionStartLine,
                  SymbolId sectionSymbolId, PathId sectionFileId,
                  uint32_t originalStartLine, uint32_t originalStartColumn,
                  uint32_t originalEndLine, uint32_t originalEndColumn,
                  Action action)
      : IncludeFileInfo(context, sectionStartLine, sectionSymbolId,
                        sectionFileId, originalStartLine, originalStartColumn,
                        originalEndLine, originalEndColumn, action, -1, -1) {}
  IncludeFileInfo(const IncludeFileInfo& i)

      = default;
  IncludeFileInfo(Context context, uint32_t sectionStartLine,
                  SymbolId sectionSymbolId, PathId sectionFileId,
                  uint32_t originalStartLine, uint32_t originalStartColumn,
                  uint32_t originalEndLine, uint32_t originalEndColumn,
                  Action action, int32_t indexOpening, int32_t indexClosing)
      : m_context(context),
        m_sectionStartLine(sectionStartLine),
        m_sectionSymbolId(sectionSymbolId),
        m_sectionFileId(sectionFileId),
        m_originalStartLine(originalStartLine),
        m_originalStartColumn(originalStartColumn),
        m_originalEndLine(originalEndLine),
        m_originalEndColumn(originalEndColumn),
        m_action(action),
        m_indexOpening(indexOpening),
        m_indexClosing(indexClosing) {}

  const Context m_context;
  uint32_t m_sectionStartLine = 0;
  SymbolId m_sectionSymbolId;
  PathId m_sectionFileId;
  uint32_t m_originalStartLine = 0;
  uint32_t m_originalStartColumn = 0;
  const uint32_t m_originalEndLine = 0;
  const uint32_t m_originalEndColumn = 0;
  Action m_action = Action::NONE;  // 1 or 2, push or pop
  int32_t m_indexOpening = 0;
  int32_t m_indexClosing = 0;
};

}  // namespace SURELOG

#endif /* SURELOG_INCLUDEFILEINFO_H */
