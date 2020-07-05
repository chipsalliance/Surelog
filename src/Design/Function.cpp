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
 * File:   Function.cpp
 * Author: alain
 *
 * Created on February 21, 2019, 8:19 PM
 */

#include "Design/Function.h"

using namespace SURELOG;

Function::~Function() {}

bool Function::compile(CompileHelper& compile_helper) {
  bool result = true;
  const FileContent* const fC = m_fileContent;
  NodeId function_declaration = fC->Child(m_nodeId);
  VObjectType function_type = fC->Type(function_declaration);
  NodeId tf_port_list = 0;
  NodeId function_statement_or_null = 0;
  switch (function_type) {
    case VObjectType::slClass_constructor_declaration: {
      tf_port_list = fC->Sibling(function_declaration);
      if (tf_port_list)
        function_statement_or_null = fC->Sibling(tf_port_list);
      else
        function_statement_or_null = fC->Child(function_declaration);
      break;
    }
    default: {
      NodeId function_body_declaration = fC->Child(function_declaration);
      NodeId function_data_type_or_implicit =
          fC->Child(function_body_declaration);
      NodeId function_name = fC->Sibling(function_data_type_or_implicit);
      tf_port_list = fC->Sibling(function_name);
      function_statement_or_null = tf_port_list;
      break;
    }
  }
  if (fC->Type(tf_port_list) == VObjectType::slTf_port_list) {
    result &=
        compile_helper.compileTfPortList(this, fC, tf_port_list, m_params);
    function_statement_or_null = fC->Sibling(tf_port_list);
  }
  result &= compile_helper.compileScopeBody(this, this, fC,
                                            function_statement_or_null);
  return result;
}
