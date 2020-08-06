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
 * File:   Task.h
 * Author: alain
 *
 * Created on February 21, 2019, 8:19 PM
 */

#ifndef TASK_H
#define TASK_H
#include <string>
#include "SourceCompile/SymbolTable.h"
#include "Design/FileContent.h"
#include "Design/Function.h"

namespace SURELOG {

class Task : public Procedure {
 public:
  Task(DesignComponent* parent, const FileContent* fC,
       NodeId id, std::string name)
      : Procedure(parent, fC, id, name) {}

  bool compile(CompileHelper& compile_helper);
  ~Task() override;
};

}  // namespace SURELOG

#endif /* TASK_H */
