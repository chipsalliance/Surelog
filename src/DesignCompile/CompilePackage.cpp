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
 * File:   CompilePackage.cpp
 * Author: alain
 *
 * Created on March 22, 2018, 9:57 PM
 */

#include "SourceCompile/VObjectTypes.h"
#include "Design/VObject.h"
#include "Library/Library.h"
#include "Design/FileContent.h"
#include "SourceCompile/SymbolTable.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/Location.h"
#include "ErrorReporting/Error.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/Compiler.h"
#include "Design/Statement.h"
#include "DesignCompile/CompileDesign.h"
#include "DesignCompile/CompileHelper.h"
#include "DesignCompile/CompilePackage.h"

using namespace SURELOG;

int FunctorCompilePackage::operator()() const {
  CompilePackage* instance = new CompilePackage(m_compileDesign, m_package,
                                                m_design, m_symbols, m_errors);
  instance->compile();
  delete instance;
  return true;
}

bool CompilePackage::compile() {
  if (!m_package) return false;
  m_package->m_exprBuilder.seterrorReporting(m_errors, m_symbols);
  m_package->m_exprBuilder.setDesign(
      m_compileDesign->getCompiler()->getDesign());
  const FileContent* fC = m_package->m_fileContents[0];
  NodeId packId = m_package->m_nodeIds[0];

  Location loc(m_symbols->registerSymbol(fC->getFileName(packId)),
               fC->Line(packId), 0, m_symbols->getId(m_package->getName()));
  Error err(ErrorDefinition::COMP_COMPILE_PACKAGE, loc);

  ErrorContainer* errors = new ErrorContainer(m_symbols);
  errors->regiterCmdLine(
      m_compileDesign->getCompiler()->getCommandLineParser());
  errors->addError(err);
  errors->printMessage(
      err,
      m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());
  delete errors;

  collectObjects_();

  do {
    VObject current = fC->Object(packId);
    packId = current.m_child;
  } while (packId && (fC->Type(packId) != VObjectType::slAttribute_instance));
  if (packId) {
    UHDM::VectorOfattribute* attributes =
    m_helper.compileAttributes(m_package, fC, packId, m_compileDesign);
    m_package->Attributes(attributes);
  }

  return true;
}

bool CompilePackage::collectObjects_() {
  std::vector<VObjectType> stopPoints = {
      VObjectType::slClass_declaration,
      VObjectType::slFunction_body_declaration,
      VObjectType::slTask_body_declaration};

  for (unsigned int i = 0; i < m_package->m_fileContents.size(); i++) {
    const FileContent* fC = m_package->m_fileContents[i];
    std::string libName = fC->getLibrary()->getName();
    VObject current = fC->Object(m_package->m_nodeIds[i]);
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
      const FileContent* pack_fC = pack_import.fC;
      NodeId pack_id = pack_import.nodeId;
      m_helper.importPackage(m_package, m_design, pack_fC, pack_id);
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
          m_helper.importPackage(m_package, m_design, fC, id);
          break;
        }
        case VObjectType::slParameter_declaration: {
          NodeId list_of_type_assignments = fC->Child(id);
          if (fC->Type(list_of_type_assignments) ==
              slList_of_type_assignments) {
            // Type param
            m_helper.compileParameterDeclaration(
                m_package, fC, list_of_type_assignments, m_compileDesign, false,
                nullptr, true);

          } else {
            m_helper.compileParameterDeclaration(
                m_package, fC, id, m_compileDesign, false, nullptr, true);
          }
          break;
        }
        case VObjectType::slLocal_parameter_declaration: {
          NodeId list_of_type_assignments = fC->Child(id);
          if (fC->Type(list_of_type_assignments) ==
              slList_of_type_assignments) {
            // Type param
            m_helper.compileParameterDeclaration(
                m_package, fC, list_of_type_assignments, m_compileDesign, true,
                nullptr, true);

          } else {
            m_helper.compileParameterDeclaration(
                m_package, fC, id, m_compileDesign, true, nullptr, true);
          }
          break;
        }
        case VObjectType::slTask_declaration: {
          m_helper.compileTask(m_package, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slFunction_declaration: {
          m_helper.compileFunction(m_package, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slParam_assignment: {
          NodeId ident = fC->Child(id);
          std::string name = fC->SymName(ident);
          NodeId val = fC->Sibling(ident);
          while(fC->Type(val) == slUnpacked_dimension) {
            val = fC->Sibling(val);
          }
          Value* value = m_package->m_exprBuilder.evalExpr(fC, val, m_package, true); // Errors muted
          if (value->isValid()) {   
            m_package->setValue(name, value, m_package->m_exprBuilder);
          } else {
            UHDM::any* expr = m_helper.compileExpression(m_package, fC, val, m_compileDesign, nullptr, nullptr, true);
            if (expr && expr->UhdmType() == UHDM::uhdmconstant) {
              UHDM::constant* c = (UHDM::constant*) expr;
              value = m_package->m_exprBuilder.fromVpiValue(c->VpiValue());
              m_package->setValue(name, value, m_package->m_exprBuilder);
            } else {
              value = m_package->m_exprBuilder.evalExpr(fC, val, m_package); // This call to create an error
              m_package->setValue(name, value, m_package->m_exprBuilder);
            }
          }
          FileCNodeId fnid(fC, id);
          m_package->addObject(type, fnid);
          break;
        }
        case VObjectType::slClass_declaration: {
          NodeId nameId = fC->Child(id);
          if (fC->Type(nameId) == slVirtual) {
             nameId = fC->Sibling(nameId);
          }
          std::string name = fC->SymName(nameId);
          FileCNodeId fnid(fC, nameId);
          m_package->addObject(type, fnid);

          std::string completeName = m_package->getName() + "::" + name;

          DesignComponent* comp = fC->getComponentDefinition(completeName);

          m_package->addNamedObject(name, fnid, comp);
          break;
        }
        case VObjectType::slClass_constructor_declaration: {
          m_helper.compileClassConstructorDeclaration(m_package, fC, id,
                                                      m_compileDesign);
          break;
        }
         case VObjectType::slNet_declaration: {
          // In a package this is certainly a var that the parser mis-interpreted 
          m_helper.compileNetDeclaration(m_package, fC, id, false, m_compileDesign);
          break;
        }
        case VObjectType::slData_declaration: {
          m_helper.compileDataDeclaration(m_package, fC, id, false,
                                          m_compileDesign);
          break;
        }
        case VObjectType::slDpi_import_export: {
          Function* func = m_helper.compileFunctionPrototype(m_package, fC, id, m_compileDesign);
          m_package->insertFunction(func);
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
  }
  return true;
}
