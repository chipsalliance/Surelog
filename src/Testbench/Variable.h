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
 * File:   Variable.h
 * Author: alain
 *
 * Created on May 26, 2019, 10:42 AM
 */

#ifndef VARIABLE_H
#define VARIABLE_H

namespace SURELOG {

class Variable {
 public:
  Variable(const DataType* dataType, const FileContent* fc, NodeId varId,
           NodeId range,
           std::string name)
      : m_dataType(dataType),
        m_fc(fc),
        m_nodeId(varId),
        m_range(range),
        m_name(name) {}
  virtual ~Variable();

  const DataType* getDataType() const { return m_dataType; }
  const std::string& getName() const { return m_name; }
  const FileContent* getFileContent() const { return m_fc; }
  NodeId getNodeId() const { return m_nodeId; }
  NodeId getRange() const { return m_range; }

 private:
  const DataType* m_dataType;
  const FileContent* m_fc;
  NodeId m_nodeId;
  NodeId m_range;
  std::string m_name;
};

};  // namespace SURELOG

#endif /* VARIABLE_H */
