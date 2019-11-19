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
 * File:   CompileProgram.cpp
 * Author: alain
 *
 * Created on June 6, 2018, 10:43 PM
 */
#include "SourceCompile/VObjectTypes.h"
#include "Design/VObject.h"
#include "Library/Library.h"
#include "Design/Signal.h"
#include "Design/FileContent.h"
#include "Design/ClockingBlock.h"
#include "Testbench/ClassDefinition.h"
#include "SourceCompile/SymbolTable.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/Location.h"
#include "ErrorReporting/Error.h"
#include "CommandLine/CommandLineParser.hpp"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/Compiler.h"
#include "DesignCompile/CompileHelper.h"
#include "DesignCompile/CompileDesign.h"
#include "DesignCompile/CompileProgram.h"

using namespace SURELOG;

CompileProgram::~CompileProgram() {}

int FunctorCompileProgram::operator()() const {
  CompileProgram* instance = new CompileProgram(m_compileDesign, m_program,
                                                m_design, m_symbols, m_errors);
  instance->compile();
  delete instance;
  return true;
}

bool CompileProgram::compile() {
  FileContent* fC = m_program->m_fileContents[0];
  NodeId nodeId = m_program->m_nodeIds[0];

  Location loc(m_symbols->registerSymbol(fC->getFileName(nodeId)),
               fC->Line(nodeId), 0,
               m_symbols->registerSymbol(m_program->getName()));

  Error err1(ErrorDefinition::COMP_COMPILE_PROGRAM, loc);
  ErrorContainer* errors = new ErrorContainer(m_symbols);
  errors->regiterCmdLine(
      m_compileDesign->getCompiler()->getCommandLineParser());
  errors->addError(err1);
  errors->printMessage(
      err1,
      m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());
  delete errors;

  Error err2(ErrorDefinition::COMP_PROGRAM_OBSOLETE_USAGE, loc);
  m_errors->addError(err2);

  std::vector<VObjectType> stopPoints = {
      VObjectType::slClass_declaration,
  };

  if (fC->getSize() == 0) return true;
  VObject current = fC->Object(nodeId);
  NodeId id = current.m_child;
  if (!id) id = current.m_sibling;
  if (!id) return false;

  // Package imports
  std::vector<FileCNodeId> pack_imports;
  // - Local file imports
  for (auto import : fC->getObjects(VObjectType::slPackage_import_item)) {
    pack_imports.push_back(import);
  }

  for (auto pack_import : pack_imports) {
    FileContent* pack_fC = pack_import.fC;
    NodeId pack_id = pack_import.nodeId;
    m_helper.importPackage(m_program, m_design, pack_fC, pack_id);
  }

  std::stack<NodeId> stack;
  stack.push(id);
  while (stack.size()) {
    id = stack.top();
    stack.pop();
    current = fC->Object(id);
    VObjectType type = fC->Type(id);
    switch (type) {
      case VObjectType::slPackage_import_item: {
        m_helper.importPackage(m_program, m_design, fC, id);
        break;
      }
      case VObjectType::slClass_declaration: {
        NodeId nameId = fC->Child(id);
        std::string name = fC->SymName(nameId);
        FileCNodeId fnid(fC, nameId);
        m_program->addObject(type, fnid);

        std::string completeName = m_program->getName() + "::" + name;

        DesignComponent* comp = fC->getComponentDefinition(completeName);

        m_program->addNamedObject(name, fnid, comp);
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
            m_helper.compileTypeDef(m_program, fC, id);
            break;
          }
          default:
            break;
        }
        break;
      }
      case VObjectType::slNet_declaration: {
        /*
          n<C> u<230> t<StringConst> p<234> s<233> l<58>
          n<c> u<231> t<StringConst> p<232> l<58>
          n<> u<232> t<Net_decl_assignment> p<233> c<231> l<58>
          n<> u<233> t<List_of_net_decl_assignments> p<234> c<232> l<58>
          n<> u<234> t<Net_declaration> p<235> c<230> l<58>
         */
        NodeId netTypeId = fC->Child(id);

        std::string dataTypeName = fC->SymName(netTypeId);
        DesignComponent* def = NULL;
        std::pair<FileCNodeId, DesignComponent*>* datatype =
            m_program->getNamedObject(dataTypeName);
        if (datatype) {
          def = datatype->second;
        }
        if (def == NULL) {
          std::string libName = m_program->m_library->getName();
          def = m_design->getClassDefinition(libName + "@" + dataTypeName);
        }
        if (def == NULL) {
          // TODO: import class in design
          Location loc(m_symbols->registerSymbol(fC->getFileName(id)),
                       fC->Line(id), 0,
                       m_symbols->registerSymbol(dataTypeName));
          Error err(ErrorDefinition::COMP_UNDEFINED_CLASS, loc);
          m_errors->addError(err);
        }
        NodeId list_of_net_decl_assignments = fC->Sibling(netTypeId);
        NodeId net_decl_assignment = fC->Child(list_of_net_decl_assignments);
        while (net_decl_assignment) {
          NodeId netId = fC->Child(net_decl_assignment);
          FileCNodeId fnid(fC, netId);
          std::string varname = fC->SymName(netId);
          m_program->addNamedObject(varname, fnid, def);
          net_decl_assignment = fC->Sibling(net_decl_assignment);
        }
        break;
      }
      default:
        break;
    }

    if (current.m_sibling) stack.push(current.m_sibling);
    if (current.m_child) {
      if (stopPoints.size()) {
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
