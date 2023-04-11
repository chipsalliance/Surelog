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

#include <Surelog/Common/PathId.h>

#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

class MacroInfo {
 public:
  MacroInfo(std::string_view name, int32_t type, PathId fileId,
            uint32_t startLine, uint16_t startColumn, uint32_t endLine,
            uint16_t endColumn, const std::vector<std::string>& arguments,
            const std::vector<std::string>& tokens);
  enum Type {
    NO_ARGS,
    WITH_ARGS,
  };

  const std::string m_name;
  const int32_t m_type;
  const PathId m_fileId;
  const uint32_t m_startLine;
  const uint16_t m_startColumn;
  const uint32_t m_endLine;
  const uint16_t m_endColumn;
  const std::vector<std::string> m_arguments;
  const std::vector<std::string> m_tokens;
};

};  // namespace SURELOG

#endif /* SURELOG_MACROINFO_H */
