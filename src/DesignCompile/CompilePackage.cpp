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

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/VObject.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/CompilePackage.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/Library/Library.h>
#include <Surelog/Package/Package.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/StringUtils.h>

// UHDM
#include <uhdm/package.h>

#include <stack>

namespace SURELOG {

int32_t FunctorCompilePackage::operator()() const {
  CompilePackage* instance = new CompilePackage(m_compileDesign, m_package,
                                                m_design, m_symbols, m_errors);
  instance->compile(true);
  delete instance;

  instance = new CompilePackage(m_compileDesign, m_package->getUnElabPackage(),
                                m_design, m_symbols, m_errors);
  instance->compile(false);
  delete instance;

  return 0;
}

bool CompilePackage::compile(bool elabMode) {
  if (!m_package) return false;
  UHDM::Serializer& s = m_compileDesign->getSerializer();
  UHDM::package* pack = any_cast<UHDM::package*>(m_package->getUhdmInstance());
  m_helper.setElabMode(elabMode);
  const Reduce reduce = elabMode ? Reduce::Yes : Reduce::No;
  if (pack == nullptr) {
    pack = s.MakePackage();
    pack->VpiName(m_package->getName());
    m_package->setUhdmInstance(pack);
  }
  m_package->m_exprBuilder.seterrorReporting(m_errors, m_symbols);
  m_package->m_exprBuilder.setDesign(
      m_compileDesign->getCompiler()->getDesign());
  const FileContent* fC = m_package->m_fileContents[0];
  NodeId packId = m_package->m_nodeIds[0];
  if (reduce == Reduce::Yes) {
    Location loc(fC->getFileId(packId), fC->Line(packId), fC->Column(packId),
                 m_symbols->getId(m_package->getName()));
    Error err(ErrorDefinition::COMP_COMPILE_PACKAGE, loc);

    ErrorContainer* errors = new ErrorContainer(m_symbols);
    errors->registerCmdLine(
        m_compileDesign->getCompiler()->getCommandLineParser());
    errors->addError(err);
    errors->printMessage(
        err,
        m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());
    delete errors;
  }
  collectObjects_(CollectType::FUNCTION, reduce);
  collectObjects_(CollectType::DEFINITION, reduce);
  m_helper.evalScheduledExprs(m_package, m_compileDesign);
  collectObjects_(CollectType::OTHER, reduce);

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

bool CompilePackage::collectObjects_(CollectType collectType, Reduce reduce) {
  std::vector<VObjectType> stopPoints = {
      VObjectType::slClass_declaration,
      VObjectType::slFunction_body_declaration,
      VObjectType::slTask_body_declaration,
      VObjectType::slInterface_class_declaration};
  m_helper.setDesign(m_compileDesign->getCompiler()->getDesign());
  for (uint32_t i = 0; i < m_package->m_fileContents.size(); i++) {
    const FileContent* fC = m_package->m_fileContents[i];
    VObject current = fC->Object(m_package->m_nodeIds[i]);
    NodeId id = current.m_child;

    if (!id) id = current.m_sibling;
    if (!id) return false;

    if (collectType == CollectType::FUNCTION) {
      // Package imports
      std::vector<FileCNodeId> pack_imports;
      // - Local file imports
      for (auto import : fC->getObjects(VObjectType::slPackage_import_item)) {
        pack_imports.push_back(import);
      }

      for (auto pack_import : pack_imports) {
        const FileContent* pack_fC = pack_import.fC;
        NodeId pack_id = pack_import.nodeId;
        m_helper.importPackage(m_package, m_design, pack_fC, pack_id,
                               m_compileDesign, true);
      }
    }

    std::stack<NodeId> stack;
    stack.push(id);
    while (!stack.empty()) {
      id = stack.top();
      stack.pop();
      current = fC->Object(id);
      VObjectType type = fC->Type(id);
      switch (type) {
        case VObjectType::slPackage_import_item: {
          if (collectType != CollectType::FUNCTION) break;
          m_helper.importPackage(m_package, m_design, fC, id, m_compileDesign,
                                 true);
          m_helper.compileImportDeclaration(m_package, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slParameter_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          NodeId list_of_type_assignments = fC->Child(id);
          if (fC->Type(list_of_type_assignments) ==
                  VObjectType::slList_of_type_assignments ||
              fC->Type(list_of_type_assignments) == VObjectType::slType) {
            // Type param
            m_helper.compileParameterDeclaration(
                m_package, fC, list_of_type_assignments, m_compileDesign,
                reduce, false, nullptr, false, false);

          } else {
            m_helper.compileParameterDeclaration(m_package, fC, id,
                                                 m_compileDesign, reduce, false,
                                                 nullptr, false, false);
          }
          break;
        }
        case VObjectType::slLocal_parameter_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          NodeId list_of_type_assignments = fC->Child(id);
          if (fC->Type(list_of_type_assignments) ==
                  VObjectType::slList_of_type_assignments ||
              fC->Type(list_of_type_assignments) == VObjectType::slType) {
            // Type param
            m_helper.compileParameterDeclaration(
                m_package, fC, list_of_type_assignments, m_compileDesign,
                reduce, true, nullptr, false, false);

          } else {
            m_helper.compileParameterDeclaration(m_package, fC, id,
                                                 m_compileDesign, reduce, true,
                                                 nullptr, false, false);
          }
          break;
        }
        case VObjectType::slTask_declaration: {
          // Called twice, placeholder first, then definition
          if (collectType == CollectType::OTHER) break;
          m_helper.compileTask(m_package, fC, id, m_compileDesign, Reduce::Yes,
                               nullptr, false);
          break;
        }
        case VObjectType::slFunction_declaration: {
          // Called twice, placeholder first, then definition
          if (collectType == CollectType::OTHER) break;
          m_helper.compileFunction(m_package, fC, id, m_compileDesign,
                                   Reduce::Yes, nullptr, false);
          break;
        }
        case VObjectType::slLet_declaration: {
          if (collectType != CollectType::FUNCTION) break;
          m_helper.compileLetDeclaration(m_package, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slParam_assignment: {
          if (collectType != CollectType::DEFINITION) break;
          FileCNodeId fnid(fC, id);
          m_package->addObject(type, fnid);
          break;
        }
        case VObjectType::slClass_declaration: {
          if (collectType != CollectType::OTHER) break;
          NodeId nameId = fC->Child(id);
          if (fC->Type(nameId) == VObjectType::slVirtual) {
            nameId = fC->Sibling(nameId);
          }
          const std::string_view name = fC->SymName(nameId);
          FileCNodeId fnid(fC, nameId);
          m_package->addObject(type, fnid);

          std::string completeName = StrCat(m_package->getName(), "::", name);

          DesignComponent* comp = fC->getComponentDefinition(completeName);

          m_package->addNamedObject(name, fnid, comp);
          break;
        }
        case VObjectType::slClass_constructor_declaration: {
          if (collectType != CollectType::OTHER) break;
          m_helper.compileClassConstructorDeclaration(m_package, fC, id,
                                                      m_compileDesign);
          break;
        }
        case VObjectType::slNet_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          m_helper.compileNetDeclaration(m_package, fC, id, false,
                                         m_compileDesign);
          m_attributes = nullptr;
          break;
        }
        case VObjectType::slData_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          m_helper.compileDataDeclaration(
              m_package, fC, id, false, m_compileDesign, reduce, m_attributes);
          m_attributes = nullptr;
          break;
        }
        case VObjectType::slAttribute_instance: {
          if (collectType != CollectType::DEFINITION) break;
          m_attributes =
              m_helper.compileAttributes(m_package, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slDpi_import_export: {
          if (collectType != CollectType::FUNCTION) break;
          NodeId Import = fC->Child(id);
          NodeId StringLiteral = fC->Sibling(Import);
          NodeId Context_keyword = fC->Sibling(StringLiteral);
          NodeId Task_prototype;
          if (fC->Type(Context_keyword) == VObjectType::slContext_keyword)
            Task_prototype = fC->Sibling(Context_keyword);
          else
            Task_prototype = Context_keyword;
          if (fC->Type(Task_prototype) == VObjectType::slTask_prototype) {
            Task* task = m_helper.compileTaskPrototype(m_package, fC, id,
                                                       m_compileDesign);
            m_package->insertTask(task);
          } else {
            Function* func = m_helper.compileFunctionPrototype(
                m_package, fC, id, m_compileDesign);
            m_package->insertFunction(func);
          }
          break;
        }
        case VObjectType::slStringConst: {
          if (collectType != CollectType::DEFINITION) break;
          NodeId sibling = fC->Sibling(id);
          if (!sibling) {
            if (fC->Type(fC->Parent(id)) != VObjectType::slPackage_declaration)
              break;
            const std::string_view endLabel = fC->SymName(id);
            std::string_view moduleName =
                StringUtils::ltrim_until(m_package->getName(), '@');
            if (endLabel != moduleName) {
              Location loc(fC->getFileId(m_package->getNodeIds()[0]),
                           fC->Line(m_package->getNodeIds()[0]),
                           fC->Column(m_package->getNodeIds()[0]),
                           m_compileDesign->getCompiler()
                               ->getSymbolTable()
                               ->registerSymbol(moduleName));
              Location loc2(fC->getFileId(id), fC->Line(id), fC->Column(id),
                            m_compileDesign->getCompiler()
                                ->getSymbolTable()
                                ->registerSymbol(endLabel));
              Error err(ErrorDefinition::COMP_UNMATCHED_LABEL, loc, loc2);
              m_compileDesign->getCompiler()->getErrorContainer()->addError(
                  err);
            }
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
  }
  return true;
}

}  // namespace SURELOG
