/*
 Copyright 2020 Alain Dargelas

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
 * File:   Parameter.h
 * Author: alain
 *
 * Created on Nov 23, 2020, 8:03 PM
 */

#ifndef PARAM_ASSIGN_H
#define PARAM_ASSIGN_H

#include <string>

#include "Design/FileContent.h"
#include "SourceCompile/SymbolTable.h"

namespace SURELOG {

class ParamAssign {
 public:
  ParamAssign(const FileContent* fC, NodeId paramId, NodeId assignId,
              bool isMultidimensional, bool port_param)
      : m_fileContent(fC),
        m_paramId(paramId),
        m_assignId(assignId),
        m_is_multidimensional(isMultidimensional),
        m_port_param(port_param) {}

  ~ParamAssign();

  const FileContent* getFileContent() const { return m_fileContent; }
  NodeId getParamId() const { return m_paramId; }
  NodeId getAssignId() const { return m_assignId; }
  bool isPortParam() const { return m_port_param; }
  void setUhdmParamAssign(UHDM::param_assign* assign) {
    m_param_assign = assign;
  }
  UHDM::param_assign* getUhdmParamAssign() const { return m_param_assign; }
  bool isMultidimensional() const { return m_is_multidimensional; }

 private:
  const FileContent* const m_fileContent;
  const NodeId m_paramId;
  const NodeId m_assignId;
  const bool m_is_multidimensional;
  const bool m_port_param;

  UHDM::param_assign* m_param_assign = nullptr;
};

}  // namespace SURELOG

#endif /* PARAM_ASSIGN_H */
