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
 * File:   ResolveSymbols.cpp
 * Author: alain
 *
 * Created on July 1, 2017, 12:38 PM
 */

#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/ModuleDefinition.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/ResolveSymbols.h>
#include <Surelog/Library/Library.h>
#include <Surelog/Package/Package.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Testbench/ClassDefinition.h>
#include <Surelog/Testbench/Program.h>
#include <Surelog/Utils/StringUtils.h>

// UHDM
#include <uhdm/package.h>

namespace SURELOG {

int32_t FunctorCreateLookup::operator()() const {
  ResolveSymbols* instance = new ResolveSymbols(
      m_compileDesign, m_fileData, m_symbolTable, m_errorContainer);
  instance->createFastLookup();
  delete instance;
  return 0;
}

int32_t FunctorResolve::operator()() const {
  ResolveSymbols* instance = new ResolveSymbols(
      m_compileDesign, m_fileData, m_symbolTable, m_errorContainer);
  instance->resolve();
  delete instance;
  return 0;
}

std::string_view ResolveSymbols::SymName(NodeId index) const {
  return m_fileData->getSymbolTable()->getSymbol(Name(index));
}

void ResolveSymbols::createFastLookup() {
  UHDM::Serializer& s = m_compileDesign->getSerializer();
  Library* lib = m_fileData->getLibrary();
  const std::string_view libName = lib->getName();

  // std::string fileName =  "FILE: " + m_fileData->getFileName() + " " +
  // m_fileData->getChunkFileName () + "\n"; std::cout << fileName;

  VObjectTypeUnorderedSet types = {
      VObjectType::slModule_declaration,    VObjectType::slPackage_declaration,
      VObjectType::slConfig_declaration,    VObjectType::slUdp_declaration,
      VObjectType::slInterface_declaration, VObjectType::slProgram_declaration,
      VObjectType::slClass_declaration};

  VObjectTypeUnorderedSet stopPoints = {
      VObjectType::slModule_declaration, VObjectType::slPackage_declaration,
      VObjectType::slProgram_declaration, VObjectType::slClass_declaration};

  std::vector<NodeId> objects =
      m_fileData->sl_collect_all(m_fileData->getRootNode(), types, stopPoints);

  for (auto object : objects) {
    VObjectType type = m_fileData->Type(object);
    NodeId stId = m_fileData->sl_collect(object, VObjectType::slStringConst,
                                         VObjectType::slAttr_spec);
    if (stId) {
      const std::string_view name = SymName(stId);
      m_fileData->insertObjectLookup(name, object, m_errorContainer);
      const std::string fullName = StrCat(libName, "@", name);

      switch (type) {
        case VObjectType::slPackage_declaration: {
          // Package names are not prefixed by Library names!
          const std::string_view pkgname = name;
          Package* pdef = new Package(pkgname, lib, m_fileData, object);
          UHDM::package* pack = s.MakePackage();
          pack->VpiName(pdef->getName());
          pdef->setUhdmInstance(pack);

          m_fileData->addPackageDefinition(pkgname, pdef);

          VObjectTypeUnorderedSet subtypes = {VObjectType::slClass_declaration};
          std::vector<NodeId> subobjects =
              m_fileData->sl_collect_all(object, subtypes, subtypes);
          for (auto subobject : subobjects) {
            NodeId stId =
                m_fileData->sl_collect(subobject, VObjectType::slStringConst,
                                       VObjectType::slAttr_spec);
            if (stId) {
              const std::string_view name = SymName(stId);
              const std::string fullSubName = StrCat(pkgname, "::", name);
              m_fileData->insertObjectLookup(fullSubName, subobject,
                                             m_errorContainer);

              ClassDefinition* def =
                  new ClassDefinition(name, lib, pdef, m_fileData, subobject,
                                      nullptr, s.MakeClass_defn());
              m_fileData->addClassDefinition(fullSubName, def);
              pdef->getUnElabPackage()->addClassDefinition(name, def);
            }
          }
          break;
        }
        case VObjectType::slProgram_declaration: {
          Program* mdef = new Program(fullName, lib, m_fileData, object);
          m_fileData->addProgramDefinition(fullName, mdef);

          VObjectTypeUnorderedSet subtypes = {VObjectType::slClass_declaration};
          std::vector<NodeId> subobjects =
              m_fileData->sl_collect_all(object, subtypes, subtypes);
          for (auto subobject : subobjects) {
            NodeId stId =
                m_fileData->sl_collect(subobject, VObjectType::slStringConst,
                                       VObjectType::slAttr_spec);
            if (stId) {
              const std::string_view name = SymName(stId);
              const std::string fullSubName = StrCat(fullName, "::", name);
              m_fileData->insertObjectLookup(fullSubName, subobject,
                                             m_errorContainer);
              ClassDefinition* def =
                  new ClassDefinition(name, lib, mdef, m_fileData, subobject,
                                      nullptr, s.MakeClass_defn());
              m_fileData->addClassDefinition(fullSubName, def);
              mdef->addClassDefinition(name, def);
            }
          }
          break;
        }
        case VObjectType::slClass_declaration: {
          ClassDefinition* def =
              new ClassDefinition(fullName, lib, nullptr, m_fileData, object,
                                  nullptr, s.MakeClass_defn());
          m_fileData->addClassDefinition(fullName, def);
          break;
        }
        case VObjectType::slModule_declaration: {
          ModuleDefinition* mdef =
              new ModuleDefinition(m_fileData, object, fullName);
          m_fileData->addModuleDefinition(fullName, mdef);

          VObjectTypeUnorderedSet subtypes = {
              VObjectType::slClass_declaration,
              VObjectType::slModule_declaration};
          std::vector<NodeId> subobjects =
              m_fileData->sl_collect_all(object, subtypes, subtypes);
          for (auto subobject : subobjects) {
            NodeId stId =
                m_fileData->sl_collect(subobject, VObjectType::slStringConst,
                                       VObjectType::slAttr_spec);
            if (stId) {
              const std::string_view name = SymName(stId);
              const std::string fullSubName = StrCat(fullName, "::", name);
              m_fileData->insertObjectLookup(fullSubName, subobject,
                                             m_errorContainer);

              if (m_fileData->Type(subobject) ==
                  VObjectType::slClass_declaration) {
                ClassDefinition* def =
                    new ClassDefinition(name, lib, mdef, m_fileData, subobject,
                                        nullptr, s.MakeClass_defn());
                m_fileData->addClassDefinition(fullSubName, def);
                mdef->getUnelabMmodule()->addClassDefinition(name, def);
              } else {
                ModuleDefinition* def =
                    new ModuleDefinition(m_fileData, subobject, fullSubName);
                m_fileData->addModuleDefinition(fullSubName, def);
              }
            }
          }

          break;
        }
        case VObjectType::slConfig_declaration:
        case VObjectType::slUdp_declaration:
        case VObjectType::slInterface_declaration:
        default: {
          ModuleDefinition* def =
              new ModuleDefinition(m_fileData, object, fullName);
          m_fileData->addModuleDefinition(fullName, def);
          break;
        }
      }
    }
  }
}

VObject ResolveSymbols::Object(NodeId index) const {
  return m_fileData->Object(index);
}

VObject* ResolveSymbols::MutableObject(NodeId index) {
  return m_fileData->MutableObject(index);
}

NodeId ResolveSymbols::UniqueId(NodeId index) const {
  return m_fileData->UniqueId(index);
}

SymbolId ResolveSymbols::Name(NodeId index) const {
  return m_fileData->Name(index);
}

NodeId ResolveSymbols::Child(NodeId index) const {
  return m_fileData->Child(index);
}

NodeId ResolveSymbols::Sibling(NodeId index) const {
  return m_fileData->Sibling(index);
}

NodeId ResolveSymbols::Definition(NodeId index) const {
  return m_fileData->Definition(index);
}

bool ResolveSymbols::SetDefinition(NodeId index, NodeId def) {
  if (!index) return false;
  MutableObject(index)->m_definition = def;
  return true;
}

NodeId ResolveSymbols::Parent(NodeId index) const {
  return m_fileData->Parent(index);
}

VObjectType ResolveSymbols::Type(NodeId index) const {
  return m_fileData->Type(index);
}

bool ResolveSymbols::SetType(NodeId index, VObjectType type) {
  if (!index) return false;
  MutableObject(index)->m_type = type;
  return true;
}

uint32_t ResolveSymbols::Line(NodeId index) const {
  return m_fileData->Line(index);
}

std::string_view ResolveSymbols::Symbol(SymbolId id) const {
  return m_fileData->getSymbolTable()->getSymbol(id);
}

NodeId ResolveSymbols::sl_get(NodeId parent, VObjectType type) const {
  return m_fileData->sl_get(parent, type);
}

NodeId ResolveSymbols::sl_parent(NodeId parent, VObjectType type) const {
  return m_fileData->sl_parent(parent, type);
}

NodeId ResolveSymbols::sl_parent(NodeId parent,
                                 const VObjectTypeUnorderedSet& types,
                                 VObjectType& actualType) const {
  return m_fileData->sl_parent(parent, types, actualType);
}

std::vector<NodeId> ResolveSymbols::sl_get_all(NodeId parent,
                                               VObjectType type) const {
  return m_fileData->sl_get_all(parent, type);
}

NodeId ResolveSymbols::sl_collect(NodeId parent, VObjectType type) const {
  return m_fileData->sl_collect(parent, type);
}

std::vector<NodeId> ResolveSymbols::sl_collect_all(NodeId parent,
                                                   VObjectType type) const {
  return m_fileData->sl_collect_all(parent, type);
}

bool ResolveSymbols::bindDefinition_(NodeId objIndex,
                                     const VObjectTypeUnorderedSet& bindTypes) {
  const std::string_view modName =
      SymName(sl_collect(objIndex, VObjectType::slStringConst));
  Design::FileIdDesignContentMap& all_files =
      this->m_compileDesign->getCompiler()->getDesign()->getAllFileContents();

  bool found = false;
  for (const auto& file : all_files) {
    PathId fileId = file.first;
    FileContent* fcontent = file.second;

    auto itr = fcontent->getObjectLookup().find(modName);
    if (itr != fcontent->getObjectLookup().end()) {
      VObjectType actualType;
      NodeId index = (*itr).second;
      NodeId mod = fcontent->sl_parent(index, bindTypes, actualType);
      if (mod) {
        SetDefinition(objIndex, mod);
        if (!m_fileData->isLibraryCellFile())
          fcontent->getReferencedObjects().emplace(modName);
        m_fileData->SetDefinitionFile(objIndex, fileId);
        switch (actualType) {
          case VObjectType::slUdp_declaration:
            SetType(objIndex, VObjectType::slUdp_instantiation);
            break;
          case VObjectType::slModule_declaration:
            SetType(objIndex, VObjectType::slModule_instantiation);
            break;
          case VObjectType::slInterface_declaration:
            SetType(objIndex, VObjectType::slInterface_instantiation);
            break;
          case VObjectType::slProgram_declaration:
            SetType(objIndex, VObjectType::slProgram_instantiation);
            break;
          default:
            break;
        }
        found = true;
        // std::cout << "FOUND MODEL FOR " << modName << " " << instName <<
        // std::endl; std::cout << m_fileData->printSubTree (objIndex) <<
        // std::endl;
        break;
      }
    }
  }
  return found;
}

bool ResolveSymbols::resolve() {
  uint32_t size = m_fileData->getVObjects().size();
  for (NodeId objIndex(0); objIndex < size; ++objIndex) {
    // ErrorDefinition::ErrorType errorType;
    bool bind = false;
    if (Type(objIndex) == VObjectType::slUdp_instantiation) {
      bind = true;
      // errorType = ErrorDefinition::ELAB_NO_UDP_DEFINITION;
    } else if (Type(objIndex) == VObjectType::slModule_instantiation) {
      bind = true;
      // errorType = ErrorDefinition::ELAB_NO_MODULE_DEFINITION;
    } else if (Type(objIndex) == VObjectType::slInterface_instantiation) {
      bind = true;
      // errorType = ErrorDefinition::ELAB_NO_INTERFACE_DEFINITION;
    } else if (Type(objIndex) == VObjectType::slProgram_instantiation) {
      bind = true;
      // errorType = ErrorDefinition::ELAB_NO_PROGRAM_DEFINITION;
    }
    if (bind) {
      /*bool found = */
      bindDefinition_(objIndex, {VObjectType::slUdp_declaration,
                                 VObjectType::slModule_declaration,
                                 VObjectType::slInterface_declaration,
                                 VObjectType::slProgram_declaration});
      /*
       * This warning is now treated in the elaboration to give the library
      information if (!found)
        {
          std::string modName = SymName (sl_collect (objIndex, slStringConst));
          Location loc (m_fileData->getFileId (), Line (objIndex), 0,
      m_symbolTable->registerSymbol (modName)); Error err (errorType, loc);
          m_errorContainer->addError (err, false, false);
        }
      */
    }
  }

  return true;
}

Compiler* ResolveSymbols::getCompiler() const {
  return m_compileDesign->getCompiler();
}

}  // namespace SURELOG
