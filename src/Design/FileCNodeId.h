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
 * File:   FileCNodeId.h
 * Author: alain
 *
 * Created on May 1, 2018, 9:00 PM
 */

#ifndef FILECNODEID_H
#define FILECNODEID_H

#include "SourceCompile/SymbolTable.h"

namespace SURELOG {
class FileContent;

class FileCNodeId {
 public:
  FileCNodeId(const FileContent* f, NodeId n) : fC(f), nodeId(n) {}

  const FileContent* fC;
  NodeId nodeId;
};

};  // namespace SURELOG

#endif /* FILECNODEID_H */
