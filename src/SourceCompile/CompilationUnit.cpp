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
 * File:   CompilationUnit.cpp
 * Author: alain
 *
 * Created on April 5, 2017, 9:16 PM
 */
#include "Surelog/SourceCompile/CompilationUnit.h"

#include <cstdint>
#include <string_view>
#include <vector>

#include "Surelog/Common/PathId.h"
#include "Surelog/SourceCompile/MacroInfo.h"
#include "Surelog/SourceCompile/VObjectTypes.h"

namespace SURELOG {

CompilationUnit::CompilationUnit(bool fileUnit)
    : m_fileUnit(fileUnit), m_inDesignElement(false) {}

MacroInfo* CompilationUnit::getMacroInfo(std::string_view macroName) {
  for (MacroStorage::const_reverse_iterator it = m_macros.crbegin(),
                                            end = m_macros.crend();
       it != end; ++it) {
    MacroInfo* mi = *it;
    if (mi->m_defType == MacroInfo::DefType::UndefineAll) {
      return nullptr;
    } else if (mi->m_name == macroName) {
      // NOTE(HS): Keep the previous behavior where the function returns
      // null if the last action on the macro name was to undefine it.
      return (mi->m_defType == MacroInfo::DefType::Define) ? mi : nullptr;
    }
  }
  return nullptr;
}

void CompilationUnit::registerMacroInfo(MacroInfo* macro) {
  m_macros.emplace_back(macro);
}

void CompilationUnit::recordTimeInfo(TimeInfo& info) {
  m_timeInfo.emplace_back(info);
}

TimeInfo& CompilationUnit::getTimeInfo(PathId fileId, uint32_t line) {
  if (m_timeInfo.empty()) {
    return m_noTimeInfo;
  }
  for (int32_t i = (int32_t)m_timeInfo.size() - 1; i >= 0; i--) {
    TimeInfo& info = m_timeInfo[i];
    if (info.m_fileId == fileId) {
      if (line >= info.m_line) {
        return info;
      }
    }
  }
  return m_noTimeInfo;
}

void CompilationUnit::recordDefaultNetType(NetTypeInfo& info) {
  m_defaultNetTypes.emplace_back(info);
}

VObjectType CompilationUnit::getDefaultNetType(PathId fileId, uint32_t line) {
  if (m_defaultNetTypes.empty()) {
    return VObjectType::paNetType_Wire;
  }
  for (int32_t i = (int32_t)m_defaultNetTypes.size() - 1; i >= 0; i--) {
    NetTypeInfo& info = m_defaultNetTypes[i];
    if (info.m_fileId == fileId) {
      if (line >= info.m_line) {
        return info.m_type;
      }
    }
  }
  return VObjectType::paNetType_Wire;
}

void CompilationUnit::setCurrentTimeInfo(PathId fileId) {
  if (m_timeInfo.empty()) {
    return;
  }
  TimeInfo info = m_timeInfo[m_timeInfo.size() - 1];
  info.m_fileId = fileId;
  info.m_line = 1;
  m_timeInfo.emplace_back(info);
}

}  // namespace SURELOG
