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
 * File:   SimpleType.h
 * Author: alain
 *
 * Created on May 19, 2020, 11:55 AM
 */

#ifndef SURELOG_SIMPLE_TYPE_H
#define SURELOG_SIMPLE_TYPE_H
#pragma once

#include <Surelog/Common/NodeId.h>
#include <Surelog/Common/RTTI.h>
#include <Surelog/Design/DataType.h>

namespace SURELOG {

class FileContent;

class SimpleType final : public DataType {
  SURELOG_IMPLEMENT_RTTI(SimpleType, DataType)
 public:
  SimpleType(const FileContent* fC, NodeId nameId, NodeId structId);
  ~SimpleType() final = default;

  NodeId getNameId() const { return m_nameId; }

 private:
  const NodeId m_nameId;
};

}  // namespace SURELOG

#endif /* SURELOG_SIMPLE_TYPE_H */
