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

int FunctorCompileFileContent::operator()() const {
  CompileFileContent* instance = new CompileFileContent(
      m_compileDesign, m_fileContent, m_design, m_symbols, m_errors);
  instance->compile();
  delete instance;
  return true;
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
  VObject current = fC->Object(fC->getSize() - 2);
  NodeId id = current.m_child;
  if (!id) id = current.m_sibling;
  if (!id) return false;
  std::stack<NodeId> stack;
  stack.push(id);
  while (!stack.empty()) {
    id = stack.top();
    stack.pop();
    current = fC->Object(id);
    VObjectType type = fC->Type(id);
    switch (type) {
      case VObjectType::slPackage_import_item: {
        FileCNodeId fnid(fC, id);
        m_fileContent->addObject(type, fnid);
        break;
      }
      case VObjectType::slFunction_declaration: {
        m_helper.compileFunction(m_fileContent, fC, id, m_compileDesign,
                                 nullptr, true);
        m_helper.compileFunction(m_fileContent, fC, id, m_compileDesign,
                                 nullptr, true);
        break;
      }
      case VObjectType::slData_declaration: {
        NodeId subNode = fC->Child(id);
        VObjectType subType = fC->Type(subNode);
        switch (subType) {
          case VObjectType::slType_declaration: {
            /*
              n<> u<15> t<Data_type> p<17> c<8> s<16> l<13>
              n<fsm_t> u<16> t<StringConst> p<17> l<13>
              n<> u<17> t<Type_declaration> p<18> c<15> l<13>
              n<> u<18> t<Data_declaration> p<19> c<17> l<13>
            */
            m_helper.compileTypeDef(m_fileContent, m_fileContent, id,
                                    m_compileDesign, nullptr, true);
            break;
          }
          default:
            break;
        }
        break;
      }
      case VObjectType::slParameter_declaration: {
        NodeId list_of_type_assignments = fC->Child(id);
        if (fC->Type(list_of_type_assignments) == slList_of_type_assignments ||
            fC->Type(list_of_type_assignments) == slType) {
          // Type param
          m_helper.compileParameterDeclaration(
              m_fileContent, fC, list_of_type_assignments, m_compileDesign,
              false, nullptr, false, true, false);

        } else {
          m_helper.compileParameterDeclaration(m_fileContent, fC, id,
                                               m_compileDesign, false, nullptr,
                                               false, true, false);
        }
        break;
      }
      case VObjectType::slLet_declaration: {
        m_helper.compileLetDeclaration(m_fileContent, fC, id, m_compileDesign);
        break;
      }
      case VObjectType::slLocal_parameter_declaration: {
        NodeId list_of_type_assignments = fC->Child(id);
        if (fC->Type(list_of_type_assignments) == slList_of_type_assignments ||
            fC->Type(list_of_type_assignments) == slType) {
          // Type param
          m_helper.compileParameterDeclaration(
              m_fileContent, fC, list_of_type_assignments, m_compileDesign,
              true, nullptr, false, true, false);

        } else {
          m_helper.compileParameterDeclaration(m_fileContent, fC, id,
                                               m_compileDesign, true, nullptr,
                                               false, true, false);
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
