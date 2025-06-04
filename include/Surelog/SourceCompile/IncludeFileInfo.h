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

#include <Surelog/Common/Containers.h>
#include <Surelog/Common/PathId.h>
#include <Surelog/Common/SymbolId.h>

#include <cstdint>
#include <vector>

namespace SURELOG {

class MacroInfo;

class IncludeFileInfo final {
 public:
  enum class Context : uint16_t { None = 0, Include = 1, Macro = 2, Directive = 3 };
  enum class Action : uint16_t { None = 0, Push = 1, Pop = 2 };

  IncludeFileInfo(Context context, Action action, PathId sectionFileId,
                  uint32_t sectionLine, uint16_t sectionColumn,
                  uint32_t sourceLine, uint16_t sourceColumn, SymbolId symbolId,
                  uint32_t symbolLine, uint32_t symbolColumn)
      : IncludeFileInfo(context, action, nullptr, sectionFileId, sectionLine,
                        sectionColumn, sourceLine, sourceColumn, symbolId,
                        symbolLine, symbolColumn, -1) {}
  IncludeFileInfo(Context context, Action action,
                  const MacroInfo *macroDefinition, PathId sectionFileId,
                  uint32_t sectionLine, uint16_t sectionColumn,
                  uint32_t sourceLine, uint16_t sourceColumn, SymbolId symbolId,
                  uint32_t symbolLine, uint32_t symbolColumn,
                  int32_t indexOpposite)
      : m_context(context),
        m_action(action),
        m_macroDefinition(macroDefinition),
        m_sectionFileId(sectionFileId),
        m_sectionLine(sectionLine),
        m_sourceLine(sourceLine),
        m_sectionColumn(sectionColumn),
        m_sourceColumn(sourceColumn),
        m_symbolId(symbolId),
        m_symbolLine(symbolLine),
        m_symbolColumn(symbolColumn),
        m_indexOpposite(indexOpposite) {}

  const Context m_context = Context::None;
  Action m_action = Action::None;

  const MacroInfo *m_macroDefinition = nullptr;
  PathId m_sectionFileId;

  uint32_t m_sectionLine = 0;
  uint32_t m_sourceLine = 0;

  uint16_t m_sectionColumn = 0;
  uint16_t m_sourceColumn = 0;

  SymbolId m_symbolId;
  uint32_t m_symbolLine = 0;
  uint16_t m_symbolColumn = 0;

  int32_t m_indexOpposite = -1;

  std::vector<MacroInfo *> m_macroDefinitions;
  std::vector<LineColumn> m_tokenPositions;
};

}  // namespace SURELOG

#endif /* SURELOG_INCLUDEFILEINFO_H */
