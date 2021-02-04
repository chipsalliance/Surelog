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
#include "SourceCompile/VObjectTypes.h"
#include "Design/VObject.h"
#include "Library/Library.h"
#include "Design/FileContent.h"
#include "SourceCompile/SymbolTable.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/Location.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/Compiler.h"
#include "Testbench/Program.h"
#include "Testbench/ClassDefinition.h"
#include "DesignCompile/CompileDesign.h"
#include "DesignCompile/ResolveSymbols.h"
#include "headers/uhdm.h"

using namespace SURELOG;

ResolveSymbols::~ResolveSymbols() {}

int FunctorCreateLookup::operator()() const {
  ResolveSymbols* instance = new ResolveSymbols(
      m_compileDesign, m_fileData, m_symbolTable, m_errorContainer);
  instance->createFastLookup();
  delete instance;
  return true;
}

int FunctorResolve::operator()() const {
  ResolveSymbols* instance = new ResolveSymbols(
      m_compileDesign, m_fileData, m_symbolTable, m_errorContainer);
  instance->resolve();
  delete instance;
  return true;
}

std::string ResolveSymbols::SymName(NodeId index) {
  return m_fileData->getSymbolTable()->getSymbol(Name(index));
}

void ResolveSymbols::createFastLookup() {
  UHDM::Serializer& s = m_compileDesign->getSerializer();
  Library* lib = m_fileData->getLibrary();
  std::string libName = lib->getName();

  // std::string fileName =  "FILE: " + m_fileData->getFileName() + " " +
  // m_fileData->getChunkFileName () + "\n"; std::cout << fileName;

  std::vector<VObjectType> types = {
      VObjectType::slModule_declaration,    VObjectType::slPackage_declaration,
      VObjectType::slConfig_declaration,    VObjectType::slUdp_declaration,
      VObjectType::slInterface_declaration, VObjectType::slProgram_declaration,
      VObjectType::slClass_declaration};

  std::vector<VObjectType> stopPoints = {
      VObjectType::slModule_declaration, VObjectType::slPackage_declaration,
      VObjectType::slProgram_declaration, VObjectType::slClass_declaration};

  std::vector<NodeId> objects =
      m_fileData->sl_collect_all(m_fileData->getRootNode(), types, stopPoints);

  for (auto object : objects) {
    VObjectType type = m_fileData->Type(object);
    NodeId stId = m_fileData->sl_collect(object, VObjectType::slStringConst,
                                         VObjectType::slAttr_spec);
    if (stId != InvalidNodeId) {
      std::string name = SymName(stId);
      m_fileData->insertObjectLookup(name, object, m_errorContainer);
      std::string fullName = libName + "@" + name;

      switch (type) {
        case VObjectType::slPackage_declaration: {
          // Package names are not prefixed by Library names!
          std::string pkgname = name;
          Package* pdef = new Package(pkgname, lib, m_fileData, object);
          UHDM::package* pack = s.MakePackage();
          pack->VpiName(pdef->getName());
          pdef->setUhdmInstance(pack);

          m_fileData->addPackageDefinition(pkgname, pdef);

          std::vector<VObjectType> subtypes = {
              VObjectType::slClass_declaration};
          std::vector<NodeId> subobjects =
              m_fileData->sl_collect_all(object, subtypes, subtypes);
          for (auto subobject : subobjects) {
            NodeId stId =
                m_fileData->sl_collect(subobject, VObjectType::slStringConst,
                                       VObjectType::slAttr_spec);
            if (stId != InvalidNodeId) {
              std::string name = SymName(stId);
              std::string fullSubName = pkgname + "::" + name;
              m_fileData->insertObjectLookup(fullSubName, subobject,
                                             m_errorContainer);

              ClassDefinition* def = new ClassDefinition(
                  name, lib, pdef, m_fileData, subobject, NULL, s.MakeClass_defn());
              m_fileData->addClassDefinition(fullSubName, def);
              pdef->addClassDefinition(name, def);
            }
          }
          break;
        }
        case VObjectType::slProgram_declaration: {
          Program* mdef = new Program(fullName, lib, m_fileData, object);
          m_fileData->addProgramDefinition(fullName, mdef);

          std::vector<VObjectType> subtypes = {
              VObjectType::slClass_declaration};
          std::vector<NodeId> subobjects =
              m_fileData->sl_collect_all(object, subtypes, subtypes);
          for (auto subobject : subobjects) {
            NodeId stId =
                m_fileData->sl_collect(subobject, VObjectType::slStringConst,
                                       VObjectType::slAttr_spec);
            if (stId != InvalidNodeId) {
              std::string name = SymName(stId);
              std::string fullSubName = fullName + "::" + name;
              m_fileData->insertObjectLookup(fullSubName, subobject,
                                             m_errorContainer);
              ClassDefinition* def = new ClassDefinition(
                  name, lib, mdef, m_fileData, subobject, NULL, s.MakeClass_defn());
              m_fileData->addClassDefinition(fullSubName, def);
              mdef->addClassDefinition(name, def);
            }
          }
          break;
        }
        case VObjectType::slClass_declaration: {
          ClassDefinition* def = new ClassDefinition(fullName, lib, NULL,
                                                     m_fileData, object, NULL, s.MakeClass_defn());
          m_fileData->addClassDefinition(fullName, def);
          break;
        }
        case VObjectType::slModule_declaration: {
          ModuleDefinition* mdef =
              new ModuleDefinition(m_fileData, object, fullName);
          m_fileData->addModuleDefinition(fullName, mdef);

          std::vector<VObjectType> subtypes = {
              VObjectType::slClass_declaration,
              VObjectType::slModule_declaration};
          std::vector<NodeId> subobjects =
              m_fileData->sl_collect_all(object, subtypes, subtypes);
          for (auto subobject : subobjects) {
            NodeId stId =
                m_fileData->sl_collect(subobject, VObjectType::slStringConst,
                                       VObjectType::slAttr_spec);
            if (stId != InvalidNodeId) {
              std::string name = SymName(stId);
              std::string fullSubName = fullName + "::" + name;
              m_fileData->insertObjectLookup(fullSubName, subobject,
                                             m_errorContainer);

              if (m_fileData->Type(subobject) ==
                  VObjectType::slClass_declaration) {
                ClassDefinition* def = new ClassDefinition(
                    name, lib, mdef, m_fileData, subobject, NULL, s.MakeClass_defn());
                m_fileData->addClassDefinition(fullSubName, def);
                mdef->addClassDefinition(name, def);
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
        default:
          ModuleDefinition* def =
              new ModuleDefinition(m_fileData, object, fullName);
          m_fileData->addModuleDefinition(fullName, def);
          break;
      }
    }
  }
}

const VObject ResolveSymbols::Object(NodeId index) const {
  if (index == InvalidNodeId) return m_fileData->Object(0);
  return m_fileData->Object(index);
}

VObject* ResolveSymbols::MutableObject(NodeId index) {
  if (index == InvalidNodeId) return m_fileData->MutableObject(0);
  return m_fileData->MutableObject(index);
}

NodeId ResolveSymbols::UniqueId(NodeId index) { return index; }

SymbolId ResolveSymbols::Name(NodeId index) {
  if (index == InvalidNodeId) return 0;
  return Object(index).m_name;
}

NodeId ResolveSymbols::Child(NodeId index) {
  if (index == InvalidNodeId) return 0;
  return Object(index).m_child;
}

NodeId ResolveSymbols::Sibling(NodeId index) {
  if (index == InvalidNodeId) return 0;
  return Object(index).m_sibling;
}

NodeId ResolveSymbols::Definition(NodeId index) const {
  return (index == InvalidNodeId) ? 0 : Object(index).m_definition;
}

bool ResolveSymbols::SetDefinition(NodeId index, NodeId def) {
  if (index == InvalidNodeId) return false;
  MutableObject(index)->m_definition = def;
  return true;
}

NodeId ResolveSymbols::Parent(NodeId index) {
  if (index == InvalidNodeId) return 0;
  return Object(index).m_parent;
}

unsigned short ResolveSymbols::Type(NodeId index) const {
  return (index == InvalidNodeId) ? 0 : Object(index).m_type;
}

bool ResolveSymbols::SetType(NodeId index, unsigned short type) {
  if (index == InvalidNodeId) return false;
  MutableObject(index)->m_type = type;
  return true;
}

unsigned int ResolveSymbols::Line(NodeId index) {
  if (index == InvalidNodeId) return 0;
  return Object(index).m_line;
}

std::string ResolveSymbols::Symbol(SymbolId id) {
  return m_fileData->getSymbolTable()->getSymbol(id);
}

NodeId ResolveSymbols::sl_get(NodeId parent, VObjectType type) {
  return m_fileData->sl_get(parent, type);
}

NodeId ResolveSymbols::sl_parent(NodeId parent, VObjectType type) {
  return m_fileData->sl_parent(parent, type);
}

NodeId ResolveSymbols::sl_parent(NodeId parent, std::vector<VObjectType> types,
                                 VObjectType& actualType) {
  return m_fileData->sl_parent(parent, types, actualType);
}

std::vector<NodeId> ResolveSymbols::sl_get_all(NodeId parent,
                                               VObjectType type) {
  return m_fileData->sl_get_all(parent, type);
}

NodeId ResolveSymbols::sl_collect(NodeId parent, VObjectType type) {
  return m_fileData->sl_collect(parent, type);
}

std::vector<NodeId> ResolveSymbols::sl_collect_all(NodeId parent,
                                                   VObjectType type) {
  return m_fileData->sl_collect_all(parent, type);
}

bool ResolveSymbols::bindDefinition_(unsigned int objIndex,
                                     std::vector<VObjectType> bindTypes) {
  std::string modName =
      SymName(sl_collect(objIndex, VObjectType::slStringConst));
  std::string instName =
      SymName(Child(sl_collect(objIndex, slName_of_instance)));
  Design::FileIdDesignContentMap& all_files =
      this->m_compileDesign->getCompiler()->getDesign()->getAllFileContents();

  bool found = false;
  for (auto file : all_files) {
    SymbolId fileId = file.first;
    FileContent* fcontent = file.second;

    auto itr = fcontent->getObjectLookup().find(modName);
    if (itr != fcontent->getObjectLookup().end()) {
      VObjectType actualType;
      NodeId index = (*itr).second;
      NodeId mod = fcontent->sl_parent(index, bindTypes, actualType);
      if (mod != InvalidNodeId) {
        SetDefinition(objIndex, mod);
        fcontent->getReferencedObjects().insert(modName);
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
  unsigned int size = m_fileData->getVObjects().size();
  for (unsigned int objIndex = 0; objIndex < size; objIndex++) {
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
      bindDefinition_(objIndex,
                      {slUdp_declaration, slModule_declaration,
                       slInterface_declaration, slProgram_declaration});
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
