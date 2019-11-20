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
 * File:   CompilationUnit.h
 * Author: alain
 *
 * Created on April 5, 2017, 9:16 PM
 */

#ifndef COMPILATIONUNIT_H
#define COMPILATIONUNIT_H
#include "SourceCompile/MacroInfo.h"
#include "Design/TimeInfo.h"

namespace SURELOG {

class CompilationUnit {
 public:
  CompilationUnit(bool fileunit);
  CompilationUnit(const CompilationUnit& orig);
  virtual ~CompilationUnit();

  void setInDesignElement() { m_inDesignElement = true; }
  void unsetInDesignElement() { m_inDesignElement = false; }
  bool isInDesignElement() { return m_inDesignElement; }
  bool isFileUnit() { return m_fileunit; }

  void registerMacroInfo(const std::string& macroName, MacroInfo* macro);
  MacroInfo* getMacroInfo(const std::string& macroName);

  const MacroStorageRef& getMacros() { return m_macros; }
  void deleteMacro(const std::string& macroName);
  void deleteAllMacros() { m_macros.clear(); }

  /* Following methods deal with `timescale */
  void setCurrentTimeInfo(SymbolId fileId);
  std::vector<TimeInfo>& getTimeInfo() { return m_timeInfo; }
  void recordTimeInfo(TimeInfo& info);
  TimeInfo& getTimeInfo(SymbolId fileId, unsigned int line);

  NodeId generateUniqueDesignElemId() {
    m_uniqueIdGenerator++;
    return m_uniqueIdGenerator;
  }
  NodeId generateUniqueNodeId() {
    m_uniqueNodeIdGenerator++;
    return m_uniqueNodeIdGenerator;
  }

 private:
  bool m_fileunit;
  bool m_inDesignElement;

  MacroStorageRef m_macros;

  std::vector<TimeInfo> m_timeInfo;
  TimeInfo m_noTimeInfo;

  /* Design Info helper data */
  NodeId m_uniqueIdGenerator;
  NodeId m_uniqueNodeIdGenerator;
};

};  // namespace SURELOG

#endif /* COMPILATIONUNIT_H */
