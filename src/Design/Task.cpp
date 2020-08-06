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
 * File:   Task.cpp
 * Author: alain
 *
 * Created on February 21, 2019, 8:19 PM
 */

#include "Design/Task.h"

using namespace SURELOG;

Task::~Task() {}

bool Task::compile(CompileHelper& compile_helper) {
  bool result = true;
  const FileContent* const fC = m_fileContent;
  NodeId task_declaration = fC->Child(m_nodeId);
  NodeId task_body_declaration = fC->Child(task_declaration);
  NodeId task_name = fC->Child(task_body_declaration);
  NodeId tf_port_list = fC->Sibling(task_name);
  result &= compile_helper.compileTfPortList(this, fC, tf_port_list, m_params);
  return result;
}
