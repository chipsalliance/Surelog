/*
 Copyright 2021 Alain Dargelas

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
 * File:   BindStmt.h
 * Author: alain
 *
 * Created on April 19, 2021, 10:00 PM
 */

#ifndef BindStmt_H
#define BindStmt_H

#include <map>
#include <string>

#include "Design/FileContent.h"

namespace UHDM {
class typespec;
};
namespace SURELOG {

class FileContent;

class BindStmt {
 public:
  BindStmt(const FileContent* fC, NodeId stmtId, NodeId targetModId,
           NodeId targetInstId, NodeId bindId, NodeId instanceId);
  ~BindStmt();

  const FileContent* getFileContent() const { return m_fC; }
  NodeId getStmtId() const { return m_stmtId; }
  NodeId getTargetModId() const { return m_targetModId; }
  NodeId getTargetInstId() const { return m_targetInstId; }
  NodeId getBindId() const { return m_bindId; }
  NodeId getInstanceId() const { return m_instanceId; }

 private:
  const FileContent* m_fC;
  const NodeId m_stmtId;
  const NodeId m_targetModId;
  const NodeId m_targetInstId;
  const NodeId m_bindId;
  const NodeId m_instanceId;
};

}  // namespace SURELOG

#endif /* BindStmt_H */
