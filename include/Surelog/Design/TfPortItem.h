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
 * File:   TfPortItem.h
 * Author: alain
 *
 * Created on May 12, 2019, 9:06 PM
 */

#ifndef SURELOG_TFPORTITEM_H
#define SURELOG_TFPORTITEM_H
#pragma once

#include <Surelog/Common/NodeId.h>
#include <Surelog/SourceCompile/VObjectTypes.h>
#include <Surelog/Testbench/Variable.h>

#include <string_view>

namespace SURELOG {

class Procedure;
class Value;

class TfPortItem final : public Variable {
 public:
  TfPortItem(Procedure* parent, const FileContent* fc, NodeId id, NodeId range,
             std::string_view name, DataType* type, Value* default_value,
             VObjectType direction)
      : Variable(type, fc, id, range, name),
        m_parent(parent),
        m_default(default_value),
        m_direction(direction) {}
  ~TfPortItem() final = default;

  Procedure* getParent() const { return m_parent; }
  Value* getDefault() const { return m_default; }
  VObjectType getDirection() const { return m_direction; }

 private:
  Procedure* m_parent;
  Value* m_default;
  const VObjectType m_direction;
};

};  // namespace SURELOG

#endif /* SURELOG_TFPORTITEM_H */
