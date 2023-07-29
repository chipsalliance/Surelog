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
 * File:   CompileFileContent.cpp
 * Author: alain
 *
 * Created on March 28, 2018, 10:16 PM
 */

#include <Surelog/Design/FileContent.h>
#include <Surelog/DesignCompile/CompileFileContent.h>

#include <stack>

namespace SURELOG {

int32_t FunctorCompileFileContent::operator()() const {
  CompileFileContent* instance = new CompileFileContent(
      m_compileDesign, m_fileContent, m_design, m_symbols, m_errors);
  instance->compile();
  delete instance;
  return 0;
}

bool CompileFileContent::compile() { return collectObjects_(); }

bool CompileFileContent::collectObjects_() {
  std::vector<VObjectType> stopPoints = {
      VObjectType::slModule_declaration,
      VObjectType::slInterface_declaration,
      VObjectType::slProgram_declaration,
      VObjectType::slClass_declaration,
      VObjectType::slPrimitive,
      VObjectType::slPackage_declaration,
      VObjectType::slFunction_declaration,
      VObjectType::slInterface_class_declaration};

  FileContent* fC = m_fileContent;
  if (fC->getSize() == 0) return true;
  const VObject& current = fC->Object(NodeId(fC->getSize() - 2));
  NodeId id = current.m_child;
  if (!id) id = current.m_sibling;
  if (!id) return false;
  std::stack<NodeId> stack;
  stack.push(id);
  while (!stack.empty()) {
    id = stack.top();
    stack.pop();
    const VObject& current = fC->Object(id);
    VObjectType type = fC->Type(id);
    switch (type) {
      case VObjectType::slPackage_import_item: {
        m_helper.importPackage(m_fileContent, m_design, fC, id,
                               m_compileDesign);
        m_helper.compileImportDeclaration(m_fileContent, fC, id,
                                          m_compileDesign);
        FileCNodeId fnid(fC, id);
        m_fileContent->addObject(type, fnid);
        break;
      }
      case VObjectType::slFunction_declaration: {
        m_helper.compileFunction(m_fileContent, fC, id, m_compileDesign,
                                 Reduce::No, nullptr, true);
        m_helper.compileFunction(m_fileContent, fC, id, m_compileDesign,
                                 Reduce::No, nullptr, true);
        break;
      }
      case VObjectType::slData_declaration: {
        m_helper.compileDataDeclaration(m_fileContent, fC, id, false,
                                        m_compileDesign, Reduce::Yes, nullptr);
        break;
      }
      case VObjectType::slParameter_declaration: {
        NodeId list_of_type_assignments = fC->Child(id);
        if (fC->Type(list_of_type_assignments) ==
                VObjectType::slList_of_type_assignments ||
            fC->Type(list_of_type_assignments) == VObjectType::slType) {
          // Type param
          m_helper.compileParameterDeclaration(
              m_fileContent, fC, list_of_type_assignments, m_compileDesign,
              Reduce::Yes, false, nullptr, false, false);

        } else {
          m_helper.compileParameterDeclaration(m_fileContent, fC, id,
                                               m_compileDesign, Reduce::Yes,
                                               false, nullptr, false, false);
        }
        break;
      }
      case VObjectType::slLet_declaration: {
        m_helper.compileLetDeclaration(m_fileContent, fC, id, m_compileDesign);
        break;
      }
      case VObjectType::slLocal_parameter_declaration: {
        NodeId list_of_type_assignments = fC->Child(id);
        if (fC->Type(list_of_type_assignments) ==
                VObjectType::slList_of_type_assignments ||
            fC->Type(list_of_type_assignments) == VObjectType::slType) {
          // Type param
          m_helper.compileParameterDeclaration(
              m_fileContent, fC, list_of_type_assignments, m_compileDesign,
              Reduce::Yes, true, nullptr, false, false);

        } else {
          m_helper.compileParameterDeclaration(m_fileContent, fC, id,
                                               m_compileDesign, Reduce::Yes,
                                               true, nullptr, false, false);
        }
        break;
      }
      default:
        break;
    }

    if (current.m_sibling) stack.push(current.m_sibling);
    if (current.m_child) {
      if (!stopPoints.empty()) {
        bool stop = false;
        for (auto t : stopPoints) {
          if (t == current.m_type) {
            stop = true;
            break;
          }
        }
        if (!stop)
          if (current.m_child) stack.push(current.m_child);
      } else {
        if (current.m_child) stack.push(current.m_child);
      }
    }
  }

  return true;
}

}  // namespace SURELOG
