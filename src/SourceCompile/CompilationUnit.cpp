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

#include <string_view>
#include <vector>

namespace SURELOG {

CompilationUnit::CompilationUnit(bool fileunit)
    : m_fileunit(fileunit), m_inDesignElement(false) {}

MacroInfo* CompilationUnit::getMacroInfo(std::string_view macroName) {
  MacroStorageRef::iterator itr = m_macros.find(macroName);
  if (itr != m_macros.end()) {
    return itr->second.back();
  }
  return nullptr;
}

void CompilationUnit::registerMacroInfo(std::string_view macroName,
                                        MacroInfo* macro) {
  MacroStorageRef::iterator itr = m_macros.find(macroName);
  if (itr == m_macros.end()) {
    itr = m_macros.emplace(macroName, std::vector<MacroInfo*>{}).first;
  }
  itr->second.push_back(macro);
}

void CompilationUnit::deleteMacro(std::string_view macroName) {
  MacroStorageRef::iterator itr = m_macros.find(macroName);
  if (itr != m_macros.end()) {
    m_macros.erase(itr);
  }
}

void CompilationUnit::recordTimeInfo(TimeInfo& info) {
  m_timeInfo.push_back(info);
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
  m_defaultNetTypes.push_back(info);
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
  m_timeInfo.push_back(info);
}

}  // namespace SURELOG
