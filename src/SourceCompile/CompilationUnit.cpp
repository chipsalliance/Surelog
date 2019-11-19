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
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/CompilationUnit.h"

using namespace SURELOG;

CompilationUnit::CompilationUnit(bool fileunit)
    : m_fileunit(fileunit),
      m_inDesignElement(false),
      m_uniqueIdGenerator(0),
      m_uniqueNodeIdGenerator(0) {}

CompilationUnit::CompilationUnit(const CompilationUnit& orig) {}

CompilationUnit::~CompilationUnit() {}

MacroInfo* CompilationUnit::getMacroInfo(const std::string& macroName) {
  MacroStorageRef::iterator itr = m_macros.find(macroName);
  if (itr != m_macros.end()) {
    return (*itr).second;
  }
  return NULL;
}

void CompilationUnit::registerMacroInfo(const std::string& macroName,
                                        MacroInfo* macro) {
  m_macros.insert(MacroStorageRef::value_type(macroName, macro));
}

void CompilationUnit::deleteMacro(const std::string& macroName) {
  MacroStorageRef::iterator itr = m_macros.find(macroName);
  if (itr != m_macros.end()) {
    m_macros.erase(itr);
  }
}

void CompilationUnit::recordTimeInfo(TimeInfo& info) {
  m_timeInfo.push_back(info);
}

TimeInfo& CompilationUnit::getTimeInfo(SymbolId fileId, unsigned int line) {
  if (!m_timeInfo.size()) {
    return m_noTimeInfo;
  }
  for (int i = (int)m_timeInfo.size() - 1; i >= 0; i--) {
    TimeInfo& info = m_timeInfo[i];
    if (info.m_fileId == fileId) {
      if (line >= info.m_line) {
        return info;
      }
    }
  }
  return m_noTimeInfo;
}

void CompilationUnit::setCurrentTimeInfo(SymbolId fileId) {
  if (!m_timeInfo.size()) {
    return;
  }
  TimeInfo info = m_timeInfo[m_timeInfo.size() - 1];
  info.m_fileId = fileId;
  info.m_line = 1;
  m_timeInfo.push_back(info);
}
