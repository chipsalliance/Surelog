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
 * File:   Parameter.h
 * Author: alain
 *
 * Created on April 15, 2019, 8:03 PM
 */

#ifndef PARAMETER_H
#define PARAMETER_H
#include <string>
#include "../SourceCompile/SymbolTable.h"
#include "../Design/FileContent.h"

namespace SURELOG {

class Parameter : public DataType {
 public:
  Parameter(FileContent* fC, NodeId nodeId, std::string name, NodeId node_type);

  VObjectType getType() { return getFileContent()->Type(m_ntype); }
  virtual ~Parameter();

 private:
  NodeId m_ntype;
};

};  // namespace SURELOG

#endif /* PARAMETER_H */
