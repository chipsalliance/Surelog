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
 * File:   MacroInfo.h
 * Author: alain
 *
 * Created on April 5, 2017, 11:46 PM
 */

#ifndef SURELOG_MACROINFO_H
#define SURELOG_MACROINFO_H
#pragma once

#include <Surelog/Common/Containers.h>
#include <Surelog/Common/PathId.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

class MacroInfo final {
 public:
  enum class DefType {
    Define = 0,
    UndefineOne = 1,
    UndefineAll = 2,
  };

  MacroInfo(std::string_view name, DefType defType, PathId fileId,
            uint32_t startLine, uint16_t startColumn, uint32_t endLine,
            uint16_t endColumn, uint16_t nameStartColumn,
            uint16_t bodyStartColumn, const std::vector<std::string>& arguments,
            const std::vector<LineColumn>& argumentPositions,
            const std::vector<std::string>& tokens,
            const std::vector<LineColumn>& tokenPositions);

  const std::string m_name;
  const DefType m_defType;
  const PathId m_fileId;
  const uint32_t m_startLine;
  const uint16_t m_startColumn;
  const uint32_t m_endLine;
  const uint16_t m_endColumn;
  const uint16_t m_nameStartColumn;
  const uint16_t m_bodyStartColumn;
  const std::vector<std::string> m_arguments;
  const std::vector<LineColumn> m_argumentPositions;
  const std::vector<std::string> m_tokens;
  const std::vector<LineColumn> m_tokenPositions;
};

};  // namespace SURELOG

#endif /* SURELOG_MACROINFO_H */
