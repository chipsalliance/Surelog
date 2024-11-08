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
 * File:   MacroInfo.cpp
 * Author: alain
 *
 * Created on April 5, 2017, 11:46 PM
 */

#include "Surelog/SourceCompile/MacroInfo.h"

namespace SURELOG {
MacroInfo::MacroInfo(std::string_view name, int32_t type, PathId fileId,
                     uint32_t startLine, uint16_t startColumn, uint32_t endLine,
                     uint16_t endColumn,
                     const std::vector<std::string>& arguments,
                     const std::vector<std::string>& tokens)
    : m_name(name),
      m_type(type),
      m_fileId(fileId),
      m_startLine(startLine),
      m_startColumn(startColumn),
      m_endLine(endLine),
      m_endColumn(endColumn),
      m_arguments(arguments),
      m_tokens(tokens) {}
}  // namespace SURELOG
