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

#ifndef SURELOG_PARAM_ASSIGN_H
#define SURELOG_PARAM_ASSIGN_H
#pragma once

#include <Surelog/Common/NodeId.h>

// UHDM
#include <uhdm/uhdm_forward_decl.h>

namespace SURELOG {

class FileContent;

class ParamAssign {
 public:
  ParamAssign(const FileContent* fC, NodeId paramId, NodeId assignId,
              bool isMultidimensional, bool port_param)
      : m_fileContent(fC),
        m_paramId(paramId),
        m_assignId(assignId),
        m_isMultidimensional(isMultidimensional),
        m_portParam(port_param) {}

  ~ParamAssign() = default;

  const FileContent* getFileContent() const { return m_fileContent; }
  NodeId getParamId() const { return m_paramId; }
  NodeId getAssignId() const { return m_assignId; }
  bool isPortParam() const { return m_portParam; }
  void setUhdmParamAssign(uhdm::ParamAssign* assign) { m_paramAssign = assign; }
  uhdm::ParamAssign* getUhdmParamAssign() const { return m_paramAssign; }
  bool isMultidimensional() const { return m_isMultidimensional; }

 private:
  const FileContent* const m_fileContent;
  const NodeId m_paramId;
  const NodeId m_assignId;
  const bool m_isMultidimensional;
  const bool m_portParam;

  uhdm::ParamAssign* m_paramAssign = nullptr;
};

}  // namespace SURELOG

#endif /* SURELOG_PARAM_ASSIGN_H */
