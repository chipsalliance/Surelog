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
 * File:   DefParam.h
 * Author: alain
 *
 * Created on January 7, 2018, 8:54 PM
 */

#ifndef SURELOG_DEFPARAM_H
#define SURELOG_DEFPARAM_H
#pragma once

#include <map>

#include "Surelog/Design/FileContent.h"
#include "Surelog/Expression/Value.h"

namespace SURELOG {

class DefParam final {
 public:
  DefParam(const std::string& name, DefParam* parent = nullptr)
      : m_name(name),
        m_value(nullptr),
        m_used(false),
        m_parent(parent),
        m_fileContent(nullptr),
        m_nodeId(0) {}

  DefParam(const DefParam& orig) = delete;

  Value* getValue() const { return m_value; }
  void setValue(Value* value) { m_value = value; }

  void setChild(std::string name, DefParam* child) {
    m_children.insert(std::make_pair(name, child));
  }
  std::map<std::string, DefParam*>& getChildren() { return m_children; }
  bool isUsed() const { return m_used; }
  void setUsed() { m_used = true; }
  void setLocation(const FileContent* fC, NodeId nodeId) {
    m_fileContent = fC;
    m_nodeId = nodeId;
  }
  const FileContent* getLocation() const { return m_fileContent; }
  NodeId getNodeId() const { return m_nodeId; }
  std::string getFullName() const;
  DefParam* getParent() { return m_parent; }

 private:
  const std::string m_name;
  std::map<std::string, DefParam*> m_children;
  Value* m_value;
  bool m_used;
  DefParam* m_parent;
  const FileContent* m_fileContent;
  NodeId m_nodeId;
};

}  // namespace SURELOG

#endif /* SURELOG_DEFPARAM_H */
