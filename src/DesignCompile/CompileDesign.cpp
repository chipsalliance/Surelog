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
 * File:   CompileDesign.cpp
 * Author: alain
 *
 * Created on July 1, 2017, 1:11 PM
 */

#include "Surelog/DesignCompile/CompileDesign.h"

#include <uhdm/ElaboratorListener.h>
#include <uhdm/clone_tree.h>
#include <uhdm/uhdm.h>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/Containers.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/SymbolId.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Netlist.h"
#include "Surelog/Design/ValuedComponentI.h"
#include "Surelog/DesignCompile/Builtin.h"
#include "Surelog/DesignCompile/CompileClass.h"
#include "Surelog/DesignCompile/CompileFileContent.h"
#include "Surelog/DesignCompile/CompileModule.h"
#include "Surelog/DesignCompile/CompilePackage.h"
#include "Surelog/DesignCompile/CompileProgram.h"
#include "Surelog/DesignCompile/DesignElaboration.h"
#include "Surelog/DesignCompile/NetlistElaboration.h"
#include "Surelog/DesignCompile/PackageAndRootElaboration.h"
#include "Surelog/DesignCompile/ResolveSymbols.h"
#include "Surelog/DesignCompile/UVMElaboration.h"
#include "Surelog/DesignCompile/UhdmWriter.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Expression/Value.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/IncludeFileInfo.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Testbench/Program.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/Serializer.h>
#include <uhdm/include_file_info.h>
#include <uhdm/param_assign.h>
#include <uhdm/uhdm_types.h>
#include <uhdm/vpi_user.h>
#include <uhdm/vpi_visitor.h>

#include <algorithm>
#include <climits>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <string_view>
#include <thread>
#include <vector>

#ifdef USETBB
#include <tbb/task.h>
#include <tbb/task_group.h>
#include <tbb/task_scheduler_init.h>
#endif

namespace SURELOG {
CompileDesign::CompileDesign(Compiler* compiler) : m_compiler(compiler) {}
CompileDesign::~CompileDesign() {
  // TODO: ownership not clear.
  // delete m_compiler;
  m_serializer.Purge();
}

bool CompileDesign::compile() {
  // Register UHDM Error callbacks
  UHDM::ErrorHandler errHandler =
      [=](UHDM::ErrorType errType, std::string_view msg,
          const UHDM::any* object1, const UHDM::any* object2) {
        FileSystem* const fileSystem = FileSystem::getInstance();
        ErrorContainer* errors = m_compiler->getErrorContainer();
        SymbolTable* symbols = m_compiler->getSymbolTable();
        if (object1) {
          Location loc1(fileSystem->toPathId(object1->VpiFile(), symbols),
                        object1->VpiLineNo(), object1->VpiColumnNo(),
                        symbols->registerSymbol(msg));
          if (object2) {
            Location loc2(fileSystem->toPathId(object2->VpiFile(), symbols),
                          object2->VpiLineNo(), object2->VpiColumnNo());
            Error err((ErrorDefinition::ErrorType)errType, loc1, loc2);
            errors->addError(err);
          } else {
            Error err((ErrorDefinition::ErrorType)errType, loc1);
            errors->addError(err);
          }
        } else {
          Location loc(symbols->registerSymbol(msg));
          Error err((ErrorDefinition::ErrorType)errType, loc);
          errors->addError(err);
        }
      };
  m_serializer.SetErrorHandler(errHandler);

  Location loc(BadSymbolId);
  Error err1(ErrorDefinition::COMP_COMPILE, loc);
  ErrorContainer* errors =
      new ErrorContainer(getCompiler()->getSymbolTable(),
                         getCompiler()->getErrorContainer()->getLogListener());
  errors->registerCmdLine(getCompiler()->getCommandLineParser());
  errors->addError(err1);
  errors->printMessage(err1,
                       getCompiler()->getCommandLineParser()->muteStdout());
  delete errors;
  return (compilation_());
}

template <class ObjectType, class ObjectMapType, typename FunctorType>
void CompileDesign::compileMT_(ObjectMapType& objects, int32_t maxThreadCount) {
  if (maxThreadCount == 0) {
    for (const auto& itr : objects) {
      FunctorType funct(this, itr.second, m_compiler->getDesign(),
                        m_symbolTables[0], m_errorContainers[0]);
      funct.operator()();
    }
  } else {
    // Optimize the load balance, try to even out the work in each thread by the
    // number of VObjects
    std::vector<uint64_t> jobSize(maxThreadCount, 0);
    std::vector<std::vector<ObjectType*>> jobArray(maxThreadCount);
    for (const auto& mod : objects) {
      uint32_t size = mod.second->getSize();
      if (size == 0) size = 100;
      uint32_t newJobIndex = 0;
      uint64_t minJobQueue = ULLONG_MAX;
      for (int32_t ii = 0; ii < maxThreadCount; ii++) {
        if (jobSize[ii] < minJobQueue) {
          newJobIndex = ii;
          minJobQueue = jobSize[ii];
        }
      }
      jobSize[newJobIndex] += size;
      jobArray[newJobIndex].push_back(mod.second);
    }

    if (getCompiler()->getCommandLineParser()->profile()) {
      std::cout << "Compilation Task\n";
      for (int32_t i = 0; i < maxThreadCount; i++) {
        std::cout << "Thread " << i << " : \n";
        for (uint32_t j = 0; j < jobArray[i].size(); j++) {
          std::cout << jobArray[i][j]->getName() << "\n";
        }
      }
    }

    // Create the threads with their respective workloads
    std::vector<std::thread*> threads;
    for (int32_t i = 0; i < maxThreadCount; i++) {
      std::thread* th = new std::thread([=] {
        for (uint32_t j = 0; j < jobArray[i].size(); j++) {
          FunctorType funct(this, jobArray[i][j], m_compiler->getDesign(),
                            m_symbolTables[i], m_errorContainers[i]);
          funct.operator()();
        }
      });
      threads.push_back(th);
    }
    for (auto* thread : threads) {  // sync
      thread->join();
    }
    for (auto* thread : threads) {  // delete
      delete thread;
    }
  }
}

void CompileDesign::collectObjects_(Design::FileIdDesignContentMap& all_files,
                                    Design* design, bool finalCollection) {
  typedef std::map<std::string, std::vector<Package*>> FileNamePackageMap;
  FileNamePackageMap fileNamePackageMap;
  SymbolTable* symbols = m_compiler->getSymbolTable();
  ErrorContainer* errors = m_compiler->getErrorContainer();
  // Collect all packages and module definitions
  for (const auto& file : all_files) {
    const FileContent* fC = file.second;
    Library* lib = fC->getLibrary();
    for (const auto& mod : fC->getModuleDefinitions()) {
      ModuleDefinition* existing = design->getModuleDefinition(mod.first);
      if (existing) {
        const FileContent* oldFC = existing->getFileContents()[0];
        const FileContent* oldParentFile = oldFC->getParent();

        ModuleDefinition* newM = mod.second;
        const FileContent* newFC = newM->getFileContents()[0];
        const FileContent* newParentFile = newFC->getParent();

        if (oldParentFile && (oldParentFile == newParentFile)) {
          // Recombine splitted module
          existing->addFileContent(mod.second->getFileContents()[0],
                                   mod.second->getNodeIds()[0]);
          for (auto classdef : mod.second->getClassDefinitions()) {
            existing->addClassDefinition(classdef.first, classdef.second);
            classdef.second->setContainer(existing);
          }
        } else {
          design->addModuleDefinition(mod.first, mod.second);
          if (finalCollection) lib->addModuleDefinition(mod.second);
        }
      } else {
        design->addModuleDefinition(mod.first, mod.second);
        if (finalCollection) lib->addModuleDefinition(mod.second);
      }
    }
    for (const auto& prog : fC->getProgramDefinitions()) {
      design->addProgramDefinition(prog.first, prog.second);
    }
    for (auto pack : fC->getPackageDefinitions()) {
      Package* existing = design->getPackage(pack.first);
      if (existing) {
        const FileContent* oldFC = existing->getFileContents()[0];
        const FileContent* oldParentFile = oldFC->getParent();
        Package* newP = pack.second;
        const FileContent* newFC = newP->getFileContents()[0];
        const FileContent* newParentFile = newFC->getParent();
        NodeId newNodeId = newP->getNodeIds()[0];
        if (!finalCollection &&
            ((oldParentFile != newParentFile) ||
             ((oldParentFile == nullptr) && (newParentFile == nullptr)))) {
          NodeId oldNodeId = existing->getNodeIds()[0];
          uint32_t oldLine = oldFC->Line(oldNodeId);
          uint32_t newLine = newFC->Line(newNodeId);
          if ((oldFC->getFileId() != newFC->getFileId()) ||
              (oldLine != newLine)) {
            Location loc1(oldFC->getFileId(), oldLine, oldFC->Column(oldNodeId),
                          symbols->registerSymbol(pack.first));
            Location loc2(newFC->getFileId(), newLine, newFC->Column(newNodeId),
                          symbols->registerSymbol(pack.first));
            Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_PACKAGE, loc1,
                      loc2);
            errors->addError(err);
          }
        }
        if (oldParentFile && (oldParentFile == newParentFile)) {
          // Recombine split package
          existing->addFileContent(newFC, newNodeId);
          for (auto classdef : pack.second->getClassDefinitions()) {
            existing->addClassDefinition(classdef.first, classdef.second);
            classdef.second->setContainer(existing);
          }
        } else {
          design->addPackageDefinition(pack.first, pack.second);
        }
      } else {
        design->addPackageDefinition(pack.first, pack.second);
      }
    }
    for (const auto& def : fC->getClassDefinitions()) {
      design->addClassDefinition(def.first, def.second);
      for (const auto& def1 : def.second->getClassMap()) {
        design->addClassDefinition(def1.first, def1.second);
      }
    }
  }
}

void CompileDesign::bindPendingClassMethodCalls() {
  Design* design = m_compiler->getDesign();
  UHDM::Serializer& s = m_serializer;
  for (PendingClassMethodCall& p : m_pendingClassCalls) {
    ClassDefinition* cls = design->getClassDefinition(p.className);
    if (cls == nullptr)
      cls = design->getClassDefinition(StrCat("work@", p.className));
    if (cls == nullptr) continue;
    UHDM::class_defn* cd = cls->getUhdmDefinition();
    // The methods are on the ClassDefinition (UhdmWriter copies them onto
    // the class_defn only when it writes the design).
    if (cd == nullptr || cls->getTask_funcs() == nullptr) continue;
    UHDM::task_func* tf = nullptr;
    for (UHDM::task_func* t : *cls->getTask_funcs()) {
      if (t->VpiName() == p.methodName) {
        tf = t;
        break;
      }
    }
    if (tf == nullptr) continue;
    // A PARAMETERIZED class: the call gets its own copy of the method
    // carrying one param_assign per class parameter -- the call's override,
    // else the class default -- so a consumer sizes `logic [W-1:0]` for THIS
    // specialization.  The class keeps its own function.
    // The class's param_assigns, like its methods, live on the
    // ClassDefinition until UhdmWriter copies them onto the class_defn.
    UHDM::VectorOfparam_assign* class_pas = cls->getParam_assigns();
    if (class_pas && !class_pas->empty()) {
      UHDM::ElaboratorContext elaboratorContext(&s, false, true);
      UHDM::task_func* spec =
          any_cast<UHDM::task_func*>(UHDM::clone_tree(tf, &elaboratorContext));
      if (spec != nullptr) {
        UHDM::VectorOfparam_assign* pas = s.MakeParam_assignVec();
        size_t k = 0;
        for (UHDM::param_assign* cpa : *class_pas) {
          UHDM::any* lhs = cpa->Lhs();
          UHDM::any* rhs = cpa->Rhs();
          std::string pname = lhs ? std::string(lhs->VpiName()) : "";
          if (k < p.positional.size() && p.positional[k]) rhs = p.positional[k];
          auto nit = p.named.find(pname);
          if (nit != p.named.end() && nit->second) rhs = nit->second;
          UHDM::param_assign* pa = s.MakeParam_assign();
          pa->Lhs(lhs);
          pa->Rhs(rhs);
          pa->VpiParent(spec);
          pas->push_back(pa);
          k++;
        }
        spec->Param_assigns(pas);
        spec->VpiParent(p.call);
        tf = spec;
      }
    }
    if (UHDM::func_call* fc = any_cast<UHDM::func_call*>(p.call)) {
      if (tf->UhdmType() == UHDM::uhdmfunction)
        fc->Function(any_cast<UHDM::function*>(tf));
    }
  }
  m_pendingClassCalls.clear();
}

bool CompileDesign::elaborate() {
  Location loc(BadSymbolId);
  Error err2(ErrorDefinition::ELAB_ELABORATING_DESIGN, loc);
  ErrorContainer* errors =
      new ErrorContainer(getCompiler()->getSymbolTable(),
                         getCompiler()->getErrorContainer()->getLogListener());
  errors->registerCmdLine(getCompiler()->getCommandLineParser());
  errors->addError(err2);
  errors->printMessage(err2,
                       getCompiler()->getCommandLineParser()->muteStdout());
  delete errors;
  return (elaboration_());
}

// ---------------------------------------------------------------------------
// Package import / export rules (IEEE 1800-2023 26.3 and 26.6), checked on
// the parse trees of the whole design: Surelog implements an import by
// copying the package's content into the importing scope, and an export by
// copying everything imported, so none of these rules survive into the
// compiled model.
namespace {
using NameSet = std::set<std::string, std::less<>>;

struct ImportItem {
  std::string pkg;   // empty for `export *::*`
  std::string name;  // empty for a wildcard
  NodeId node;
};

struct Occurrence {
  NodeId node;
  bool ref = false;      // an unqualified use of the name
  bool topDecl = false;  // declared directly in the scope
};

struct ScopeInfo {
  const FileContent* fC = nullptr;
  NodeId root;
  bool isPackage = false;
  std::string name;
  NameSet declared;   // declared directly in the scope (packages only)
  NameSet mentioned;  // every identifier of the body
  std::vector<ImportItem> imports;
  std::vector<ImportItem> exports;
  std::map<std::string, std::vector<Occurrence>, std::less<>> occurrences;
};

bool isScopeRoot(VObjectType t) {
  return t == VObjectType::paPackage_declaration ||
         t == VObjectType::paModule_declaration ||
         t == VObjectType::paInterface_declaration ||
         t == VObjectType::paProgram_declaration;
}

// A node between a declaration and its scope that opens a nested scope.
bool isNestedScope(VObjectType t) {
  switch (t) {
    case VObjectType::paFunction_declaration:
    case VObjectType::paTask_declaration:
    case VObjectType::paFunction_body_declaration:
    case VObjectType::paTask_body_declaration:
    case VObjectType::paClass_declaration:
    case VObjectType::paInterface_class_declaration:
    case VObjectType::paClass_constructor_declaration:
    case VObjectType::paCovergroup_declaration:
    case VObjectType::paProperty_declaration:
    case VObjectType::paSequence_declaration:
    case VObjectType::paLet_declaration:
    case VObjectType::paChecker_declaration:
    case VObjectType::paClocking_declaration:
    case VObjectType::paSeq_block:
    case VObjectType::paPar_block:
    case VObjectType::paStatement:
    case VObjectType::paGenerate_region:
    case VObjectType::paGenerate_begin_end_block:
    case VObjectType::paGenerate_module_block:
    case VObjectType::paGenerate_module_named_block:
    case VObjectType::paGenerate_interface_block:
    case VObjectType::paGenerate_interface_named_block:
    case VObjectType::paLoop_generate_construct:
    case VObjectType::paIf_generate_construct:
    case VObjectType::paCase_generate_construct:
    case VObjectType::paDpi_import_export:
      return true;
    default:
      return false;
  }
}

bool atScopeTop(const FileContent* fC, NodeId id, NodeId root) {
  for (NodeId p = fC->Parent(id); p && p != root; p = fC->Parent(p)) {
    if (isNestedScope(fC->Type(p))) return false;
  }
  return true;
}

// `id` is a StringConst: does it name a declaration of its parent?
bool isDeclarationName(const FileContent* fC, NodeId id) {
  const NodeId parent = fC->Parent(id);
  const VObjectType pt = fC->Type(parent);
  const bool first = fC->Child(parent) == id;
  switch (pt) {
    case VObjectType::paVariable_decl_assignment:
    case VObjectType::paNet_decl_assignment:
    case VObjectType::paParam_assignment:
    case VObjectType::paSpecparam_assignment:
    case VObjectType::paEnum_name_declaration:
      return first;
    case VObjectType::paType_declaration:
      return true;
    case VObjectType::paList_of_type_assignments:
      return true;
    case VObjectType::paInterface_identifier:
      return fC->Type(fC->Parent(parent)) ==
             VObjectType::paList_of_interface_identifiers;
    default:
      return false;
  }
}

// A declaration a package makes that is not a data object.
bool isPackageItemName(const FileContent* fC, NodeId id) {
  const NodeId parent = fC->Parent(id);
  switch (fC->Type(parent)) {
    case VObjectType::paFunction_body_declaration:
    case VObjectType::paTask_body_declaration:
    case VObjectType::paFunction_prototype:
    case VObjectType::paTask_prototype: {
      // The first StringConst child; a return type is a Function_data_type.
      for (NodeId c = fC->Child(parent); c; c = fC->Sibling(c)) {
        if (fC->Type(c) == VObjectType::slStringConst) return c == id;
      }
      return false;
    }
    case VObjectType::paClass_declaration:
    case VObjectType::paInterface_class_declaration:
    case VObjectType::paCovergroup_declaration:
    case VObjectType::paProperty_declaration:
    case VObjectType::paSequence_declaration:
    case VObjectType::paLet_declaration:
    case VObjectType::paNet_type_declaration: {
      for (NodeId c = fC->Child(parent); c; c = fC->Sibling(c)) {
        if (fC->Type(c) == VObjectType::slStringConst) return c == id;
      }
      return false;
    }
    default:
      return false;
  }
}

// `id` is a StringConst: is it an unqualified USE of a name?
bool isReferenceName(const FileContent* fC, NodeId id) {
  const NodeId parent = fC->Parent(id);
  if (fC->Child(parent) != id) return false;
  switch (fC->Type(parent)) {
    case VObjectType::paPrimary_literal:
    case VObjectType::paPs_or_hierarchical_identifier:
    case VObjectType::paHierarchical_identifier:
    case VObjectType::paSubroutine_call:
    case VObjectType::paComplex_func_call:
    case VObjectType::paData_type:
    case VObjectType::paNet_declaration:
    case VObjectType::paInterface_port_declaration:
      return true;
    default:
      return false;
  }
}

ImportItem importItem(const FileContent* fC, NodeId item) {
  ImportItem res;
  res.node = item;
  NodeId c = fC->Child(item);
  if (c && fC->Type(c) == VObjectType::slStringConst) {
    res.pkg = fC->SymName(c);
    NodeId n = fC->Sibling(c);
    if (n && fC->Type(n) == VObjectType::slStringConst)
      res.name = fC->SymName(n);
  }
  return res;
}

void collectScope(ScopeInfo& scope) {
  const FileContent* fC = scope.fC;
  // The scope's own name.
  NodeId nameNode;
  if (scope.isPackage) {
    for (NodeId c = fC->Child(scope.root); c; c = fC->Sibling(c)) {
      if (fC->Type(c) == VObjectType::slStringConst) {
        nameNode = c;
        break;
      }
    }
    if (nameNode) scope.name = fC->SymName(nameNode);
  }
  std::vector<NodeId> stack;
  for (NodeId c = fC->Child(scope.root); c; c = fC->Sibling(c))
    stack.push_back(c);
  while (!stack.empty()) {
    NodeId id = stack.back();
    stack.pop_back();
    const VObjectType t = fC->Type(id);
    if (isScopeRoot(t)) continue;
    if (t == VObjectType::paPackage_export_declaration) {
      NodeId item = fC->Child(id);
      if (!item) scope.exports.push_back({"", "", id});
      for (; item; item = fC->Sibling(item)) {
        if (fC->Type(item) == VObjectType::paPackage_import_item)
          scope.exports.push_back(importItem(fC, item));
      }
      continue;
    }
    if (t == VObjectType::paPackage_import_item) {
      if (atScopeTop(fC, id, scope.root))
        scope.imports.push_back(importItem(fC, id));
      continue;
    }
    if (t == VObjectType::slStringConst && id != nameNode) {
      const std::string name(fC->SymName(id));
      scope.mentioned.insert(name);
      Occurrence occ;
      occ.node = id;
      occ.ref = isReferenceName(fC, id);
      const bool top = atScopeTop(fC, id, scope.root);
      occ.topDecl = top && isDeclarationName(fC, id);
      scope.occurrences[name].push_back(occ);
      if (scope.isPackage) {
        if (occ.topDecl) {
          scope.declared.insert(name);
        } else if (isPackageItemName(fC, id)) {
          // The name is a child of the construct it declares.
          NodeId decl = fC->Parent(id);
          const NodeId up = fC->Parent(decl);
          if (up && (fC->Type(up) == VObjectType::paFunction_declaration ||
                     fC->Type(up) == VObjectType::paTask_declaration))
            decl = up;
          if (atScopeTop(fC, decl, scope.root)) scope.declared.insert(name);
        }
      }
    }
    for (NodeId c = fC->Child(id); c; c = fC->Sibling(c)) stack.push_back(c);
  }
  // The walk is depth-first from the back: restore source order.
  for (auto& [name, occs] : scope.occurrences) {
    std::sort(occs.begin(), occs.end(),
              [fC](const Occurrence& a, const Occurrence& b) {
                if (fC->Line(a.node) != fC->Line(b.node))
                  return fC->Line(a.node) < fC->Line(b.node);
                return fC->Column(a.node) < fC->Column(b.node);
              });
  }
}

bool before(const FileContent* fC, NodeId a, NodeId b) {
  if (fC->Line(a) != fC->Line(b)) return fC->Line(a) < fC->Line(b);
  return fC->Column(a) < fC->Column(b);
}
}  // namespace

void CompileDesign::checkPackageImportsExports_() {
  Design* design = m_compiler->getDesign();
  ErrorContainer* errors = m_compiler->getErrorContainer();
  SymbolTable* symbols = m_compiler->getSymbolTable();
  auto report = [&](ErrorDefinition::ErrorType type, const FileContent* fC,
                    NodeId id, std::string_view text) {
    Location loc(fC->getFileId(id), fC->Line(id), fC->Column(id),
                 symbols->registerSymbol(text));
    Error err(type, loc);
    errors->addError(err);
  };

  std::vector<ScopeInfo> scopes;
  // Wildcard imports made at file level ($unit), per file.
  std::map<const FileContent*, std::vector<ImportItem>> unitImports;
  for (const auto& [fileId, fC] : design->getAllFileContents()) {
    if (fC == nullptr || fC->getSize() == 0) continue;
    std::vector<NodeId> stack{fC->getRootNode()};
    while (!stack.empty()) {
      NodeId id = stack.back();
      stack.pop_back();
      const VObjectType t = fC->Type(id);
      if (isScopeRoot(t)) {
        ScopeInfo scope;
        scope.fC = fC;
        scope.root = id;
        scope.isPackage = t == VObjectType::paPackage_declaration;
        collectScope(scope);
        scopes.push_back(std::move(scope));
        continue;
      }
      if (t == VObjectType::paPackage_import_item) {
        unitImports[fC].push_back(importItem(fC, id));
        continue;
      }
      for (NodeId c = fC->Child(id); c; c = fC->Sibling(c)) stack.push_back(c);
    }
  }

  std::map<std::string, std::vector<const ScopeInfo*>, std::less<>> packages;
  for (const ScopeInfo& s : scopes) {
    if (s.isPackage && !s.name.empty()) packages[s.name].push_back(&s);
  }
  // Whether `import pkg::name` can find `name`: declared in, mentioned by
  // (a referenced wildcard import), explicitly imported by, or exported by
  // the package.  Deliberately generous; only a name the package never
  // spells is rejected.
  auto provides = [&](std::string_view pkg, std::string_view name) {
    auto it = packages.find(pkg);
    if (it == packages.end()) return true;  // unknown package: not ours
    for (const ScopeInfo* p : it->second) {
      if (p->mentioned.count(name)) return true;
      for (const ImportItem& i : p->imports)
        if (i.name == name) return true;
      for (const ImportItem& e : p->exports)
        if (e.name == name) return true;
    }
    return false;
  };
  auto declares = [&](std::string_view pkg, std::string_view name) {
    auto it = packages.find(pkg);
    if (it == packages.end()) return false;
    return std::any_of(
        it->second.begin(), it->second.end(),
        [name](const ScopeInfo* p) { return p->declared.count(name) != 0; });
  };

  for (const ScopeInfo& s : scopes) {
    const FileContent* fC = s.fC;
    // `import P::x` / `export P::x`: P must make `x` available.
    for (const ImportItem& i : s.imports) {
      if (i.name.empty() || i.pkg.empty()) continue;
      if (!provides(i.pkg, i.name))
        report(ErrorDefinition::COMP_PACKAGE_MEMBER_NOT_VISIBLE, fC, i.node,
               StrCat(i.pkg, "::", i.name));
    }
    for (const ImportItem& e : s.exports) {
      if (e.name.empty() || e.pkg.empty()) continue;
      if (!provides(e.pkg, e.name)) {
        report(ErrorDefinition::COMP_PACKAGE_MEMBER_NOT_VISIBLE, fC, e.node,
               StrCat(e.pkg, "::", e.name));
        continue;
      }
      bool imported = false;
      for (const ImportItem& i : s.imports) {
        if (i.pkg == e.pkg && (i.name.empty() || i.name == e.name))
          imported = true;
      }
      if (!imported) {
        report(ErrorDefinition::COMP_EXPORT_NOT_IMPORTED, fC, e.node,
               StrCat(e.pkg, "::", e.name));
      } else if (s.declared.count(e.name)) {
        report(ErrorDefinition::COMP_EXPORT_CONFLICTS_WITH_DECLARATION, fC,
               e.node, StrCat(e.pkg, "::", e.name));
      }
    }

    // Wildcard imports in effect in this scope.
    std::vector<ImportItem> wildcards;
    auto unit = unitImports.find(fC);
    if (unit != unitImports.end()) {
      for (const ImportItem& i : unit->second)
        if (i.name.empty() && before(fC, i.node, s.root))
          wildcards.push_back(i);
    }
    for (const ImportItem& i : s.imports)
      if (i.name.empty()) wildcards.push_back(i);
    if (wildcards.empty()) continue;
    NameSet explicitImports;
    for (const ImportItem& i : s.imports)
      if (!i.name.empty()) explicitImports.insert(i.name);

    for (const auto& [name, occs] : s.occurrences) {
      if (explicitImports.count(name)) continue;
      // The packages a wildcard import makes `name` visible from.
      std::vector<const ImportItem*> providers;
      NameSet seen;
      for (const ImportItem& w : wildcards) {
        if (declares(w.pkg, name) && seen.insert(w.pkg).second)
          providers.push_back(&w);
      }
      if (providers.empty()) continue;
      bool allRefs = true;
      const Occurrence* firstRef = nullptr;
      const Occurrence* ambiguousRef = nullptr;
      const Occurrence* topDecl = nullptr;
      bool otherDecl = false;
      for (const Occurrence& o : occs) {
        if (o.ref) {
          if (firstRef == nullptr) firstRef = &o;
          // Only the wildcard imports ABOVE the first reference compete for
          // it (LRM 26.3, the `import p2::*` after `x = f()` example); that
          // reference imports the name for the rest of the scope.
          if (firstRef == &o) {
            uint32_t n = 0;
            for (const ImportItem* w : providers)
              if (before(fC, w->node, o.node)) n++;
            if (n > 1) ambiguousRef = &o;
          }
        } else {
          allRefs = false;
          if (o.topDecl) {
            if (topDecl == nullptr) topDecl = &o;
          } else {
            otherDecl = true;
          }
        }
      }
      if (firstRef == nullptr) continue;
      // LRM 26.3: a name two wildcard imports make visible may not be used
      // unless the scope declares it.
      if (allRefs && ambiguousRef != nullptr) {
        report(ErrorDefinition::COMP_AMBIGUOUS_WILDCARD_IMPORT, fC,
               ambiguousRef->node, name);
        continue;
      }
      // LRM 26.3: once a wildcard-imported name is used, the scope may not
      // declare it.
      if (topDecl != nullptr && !otherDecl &&
          before(fC, firstRef->node, topDecl->node) &&
          before(fC, providers.front()->node, firstRef->node)) {
        report(ErrorDefinition::COMP_WILDCARD_IMPORT_REDECLARED, fC,
               topDecl->node, name);
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Enum declaration rules (IEEE 1800-2023 6.19), checked on the parse tree:
// the compiled enum_const keeps only a folded value, which has already lost
// its x/z bits and been truncated to the base type.  Only LITERAL values are
// judged; a value built from parameters is left to the elaborated model.
namespace {
struct EnumBase {
  bool known = false;    // width/signedness known
  bool twoState = true;  // no base type means int
  bool isSigned = true;
  uint64_t width = 32;
};

bool literalHasXZ(std::string_view text) {
  const size_t tick = text.find('\'');
  if (tick == std::string_view::npos) return false;
  const std::string_view digits = text.substr(tick + 1);
  return std::any_of(digits.begin(), digits.end(), [](char c) {
    return c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?';
  });
}

// True when the subtree spells an x/z bit.
bool hasXZ(const FileContent* fC, NodeId id) {
  std::vector<NodeId> stack{id};
  while (!stack.empty()) {
    NodeId n = stack.back();
    stack.pop_back();
    switch (fC->Type(n)) {
      case VObjectType::paNumber_1Tickbx:
      case VObjectType::paNumber_1TickbX:
      case VObjectType::paNumber_1TickBx:
      case VObjectType::paNumber_1TickBX:
        return true;
      case VObjectType::slIntConst:
        if (literalHasXZ(fC->SymName(n))) return true;
        break;
      default:
        break;
    }
    for (NodeId c = fC->Child(n); c; c = fC->Sibling(c)) stack.push_back(c);
  }
  return false;
}

// A non-constant system function (`$time`) in the subtree.
NodeId nonConstantSysCall(const FileContent* fC, NodeId id) {
  std::vector<NodeId> stack{id};
  while (!stack.empty()) {
    NodeId n = stack.back();
    stack.pop_back();
    if (fC->Type(n) == VObjectType::paSystem_task_names) {
      if (NodeId nm = fC->Child(n)) {
        const std::string_view name = fC->SymName(nm);
        if (name == "$time" || name == "$stime" || name == "$realtime" ||
            name == "$random" || name == "$urandom" || name == "$urandom_range")
          return n;
      }
    }
    for (NodeId c = fC->Child(n); c; c = fC->Sibling(c)) stack.push_back(c);
  }
  return InvalidNodeId;
}

// The value of an UNSIZED integer literal (`100`, `'d7`, `'h3f`), optionally
// negated, spelled as the whole of a constant expression.
bool unsizedLiteralValue(const FileContent* fC, NodeId expr, bool& negative,
                         uint64_t& value) {
  negative = false;
  NodeId n = expr;
  if (fC->Type(n) == VObjectType::paConstant_expression) {
    NodeId c = fC->Child(n);
    if (fC->Type(c) == VObjectType::paUnary_Minus) {
      negative = true;
      c = fC->Sibling(c);
      if (fC->Sibling(c)) return false;
    } else if (fC->Sibling(c)) {
      return false;
    }
    n = c;
  }
  while (fC->Type(n) == VObjectType::paConstant_primary ||
         fC->Type(n) == VObjectType::paPrimary_literal ||
         fC->Type(n) == VObjectType::paConstant_expression) {
    NodeId c = fC->Child(n);
    if (!c || fC->Sibling(c)) return false;
    n = c;
  }
  if (fC->Type(n) != VObjectType::slIntConst) return false;
  std::string text;
  for (char ch : fC->SymName(n))
    if (ch != '_') text.push_back(ch);
  int base = 10;
  const size_t tick = text.find('\'');
  if (tick != std::string::npos) {
    if (tick != 0) return false;  // sized: the size rule owns it
    size_t i = 1;
    if (i < text.size() && (text[i] == 's' || text[i] == 'S')) i++;
    if (i >= text.size()) return false;
    switch (text[i]) {
      case 'd':
      case 'D':
        base = 10;
        break;
      case 'h':
      case 'H':
        base = 16;
        break;
      case 'o':
      case 'O':
        base = 8;
        break;
      case 'b':
      case 'B':
        base = 2;
        break;
      default:
        return false;
    }
    text = text.substr(i + 1);
  }
  if (text.empty() || text.size() > 18) return false;
  char* end = nullptr;
  value = std::strtoull(text.c_str(), &end, base);
  return end && *end == '\0';
}

bool literalInt(const FileContent* fC, NodeId expr, int64_t& v,
                bool* based = nullptr) {
  bool neg = false;
  uint64_t u = 0;
  if (!unsizedLiteralValue(fC, expr, neg, u)) return false;
  if (based) {
    *based = false;
    for (NodeId n = expr; n; n = fC->Child(n)) {
      if (fC->Type(n) == VObjectType::slIntConst) {
        *based = fC->SymName(n).find('\'') != std::string_view::npos;
        break;
      }
      if (fC->Type(n) == VObjectType::paUnary_Minus) n = fC->Sibling(n);
    }
  }
  v = neg ? -static_cast<int64_t>(u) : static_cast<int64_t>(u);
  return true;
}

// The NAME of a typedef declared anywhere in the file whose data type is an
// integer atom (`typedef int T;`); a name also declared otherwise is unknown.
bool typedefIsIntegerAtom(const FileContent* fC, std::string_view name) {
  bool atom = false;
  std::vector<NodeId> stack{fC->getRootNode()};
  while (!stack.empty()) {
    NodeId n = stack.back();
    stack.pop_back();
    if (fC->Type(n) == VObjectType::paType_declaration) {
      NodeId dt = fC->Child(n);
      if (fC->Type(dt) == VObjectType::paData_type) {
        NodeId nm = fC->Sibling(dt);
        if (nm && fC->Type(nm) == VObjectType::slStringConst &&
            fC->SymName(nm) == name) {
          const VObjectType bt = fC->Type(fC->Child(dt));
          if (bt == VObjectType::paIntegerAtomType_Int ||
              bt == VObjectType::paIntegerAtomType_Integer ||
              bt == VObjectType::paIntegerAtomType_Byte ||
              bt == VObjectType::paIntegerAtomType_Shortint ||
              bt == VObjectType::paIntegerAtomType_LongInt ||
              bt == VObjectType::paIntegerAtomType_Time) {
            if (fC->Sibling(fC->Child(dt))) return false;
            atom = true;
          } else {
            return false;
          }
        }
      }
    }
    for (NodeId c = fC->Child(n); c; c = fC->Sibling(c)) stack.push_back(c);
  }
  return atom;
}
}  // namespace

void CompileDesign::checkEnumDeclarations_() {
  Design* design = m_compiler->getDesign();
  ErrorContainer* errors = m_compiler->getErrorContainer();
  SymbolTable* symbols = m_compiler->getSymbolTable();
  auto report = [&](ErrorDefinition::ErrorType type, const FileContent* fC,
                    NodeId id, std::string_view text) {
    Location loc(fC->getFileId(id), fC->Line(id), fC->Column(id),
                 symbols->registerSymbol(text));
    Error err(type, loc);
    errors->addError(err);
  };
  for (const auto& [fileId, fC] : design->getAllFileContents()) {
    if (fC == nullptr || fC->getSize() == 0) continue;
    std::vector<NodeId> stack{fC->getRootNode()};
    while (!stack.empty()) {
      NodeId id = stack.back();
      stack.pop_back();
      for (NodeId c = fC->Child(id); c; c = fC->Sibling(c)) stack.push_back(c);
      if (fC->Type(id) != VObjectType::paData_type) continue;
      NodeId first = fC->Child(id);
      if (fC->Type(first) != VObjectType::paEnum_base_type &&
          fC->Type(first) != VObjectType::paEnum_name_declaration)
        continue;

      EnumBase base;
      base.known = true;  // no base type: int
      NodeId member = first;
      if (fC->Type(first) == VObjectType::paEnum_base_type) {
        member = fC->Sibling(first);
        base = EnumBase();
        NodeId bt = fC->Child(first);
        NodeId dim = fC->Sibling(bt);
        bool explicitSign = false, signedKw = false;
        if (dim && (fC->Type(dim) == VObjectType::paSigning_Signed ||
                    fC->Type(dim) == VObjectType::paSigning_Unsigned)) {
          explicitSign = true;
          signedKw = fC->Type(dim) == VObjectType::paSigning_Signed;
          dim = fC->Sibling(dim);
        }
        switch (fC->Type(bt)) {
          case VObjectType::paIntegerAtomType_Int:
            base = {true, true, true, 32};
            break;
          case VObjectType::paIntegerAtomType_Integer:
            base = {true, false, true, 32};
            break;
          case VObjectType::paIntegerAtomType_Shortint:
            base = {true, true, true, 16};
            break;
          case VObjectType::paIntegerAtomType_Byte:
            base = {true, true, true, 8};
            break;
          case VObjectType::paIntegerAtomType_LongInt:
            base = {true, true, true, 64};
            break;
          case VObjectType::paIntegerAtomType_Time:
            base = {true, false, false, 64};
            break;
          case VObjectType::paIntVec_TypeBit:
          case VObjectType::paIntVec_TypeLogic:
          case VObjectType::paIntVec_TypeReg: {
            base.twoState = fC->Type(bt) == VObjectType::paIntVec_TypeBit;
            base.isSigned = false;
            base.width = 1;
            base.known = true;
            if (dim && fC->Type(dim) == VObjectType::paPacked_dimension) {
              base.known = false;
              NodeId range = fC->Child(dim);
              if (fC->Type(range) == VObjectType::paConstant_range) {
                NodeId l = fC->Child(range);
                NodeId r = l ? fC->Sibling(l) : InvalidNodeId;
                int64_t lv = 0, rv = 0;
                if (l && r && literalInt(fC, l, lv) && literalInt(fC, r, rv)) {
                  base.width = static_cast<uint64_t>(std::llabs(lv - rv)) + 1;
                  base.known = base.width <= 63;
                }
              }
            }
            break;
          }
          case VObjectType::slStringConst: {
            base.known = false;
            base.twoState = false;  // unknown: never judge x/z
            const std::string_view tname = fC->SymName(bt);
            // `typedef enum T {...} T;`: the enum is its own base type.
            NodeId decl = fC->Parent(id);
            if (decl && fC->Type(decl) == VObjectType::paType_declaration) {
              NodeId nm = fC->Sibling(id);
              if (nm && fC->Type(nm) == VObjectType::slStringConst &&
                  fC->SymName(nm) == tname) {
                report(ErrorDefinition::COMP_ENUM_INVALID_BASE_TYPE, fC, bt,
                       tname);
                continue;
              }
            }
            // LRM 6.19: a type_identifier naming an integer ATOM type takes
            // no packed dimension.
            if (dim && fC->Type(dim) == VObjectType::paPacked_dimension &&
                typedefIsIntegerAtom(fC, tname)) {
              report(ErrorDefinition::COMP_ENUM_INVALID_BASE_TYPE, fC, bt,
                     tname);
              continue;
            }
            break;
          }
          default:
            base.known = false;
            base.twoState = false;
            break;
        }
        if (explicitSign) base.isSigned = signedKw;
      }

      int64_t maxV = 0, minV = 0;
      if (base.known) {
        if (base.isSigned) {
          maxV = base.width >= 64 ? INT64_MAX
                                  : (int64_t(1) << (base.width - 1)) - 1;
          minV =
              base.width >= 64 ? INT64_MIN : -(int64_t(1) << (base.width - 1));
        } else {
          maxV = base.width >= 63 ? INT64_MAX : (int64_t(1) << base.width) - 1;
          minV = 0;
        }
      }
      int64_t curMax = maxV;  // a based literal widens it to the bit width
      bool nextKnown = true;  // the implicit next value is known
      int64_t next = 0;
      bool afterXZ = false;
      for (; member && fC->Type(member) == VObjectType::paEnum_name_declaration;
           member = fC->Sibling(member)) {
        NodeId nameId = fC->Child(member);
        const std::string_view name = fC->SymName(nameId);
        NodeId valueId = fC->Sibling(nameId);
        std::vector<int64_t> bounds;
        while (valueId && fC->Type(valueId) == VObjectType::slIntConst) {
          int64_t b = 0;
          std::string_view t = fC->SymName(valueId);
          b = std::strtoll(std::string(t).c_str(), nullptr, 10);
          bounds.push_back(b);
          valueId = fC->Sibling(valueId);
        }
        uint64_t count = 1;
        if (bounds.size() == 1) count = bounds[0] > 0 ? bounds[0] : 1;
        if (bounds.size() == 2)
          count = static_cast<uint64_t>(std::llabs(bounds[0] - bounds[1])) + 1;

        if (valueId) {
          afterXZ = false;
          if (nonConstantSysCall(fC, valueId)) {
            report(ErrorDefinition::COMP_ENUM_VALUE_NOT_CONSTANT, fC, nameId,
                   name);
            nextKnown = false;
            continue;
          }
          if (hasXZ(fC, valueId)) {
            if (base.known && base.twoState) {
              report(ErrorDefinition::COMP_ENUM_XZ_IN_TWO_STATE, fC, nameId,
                     name);
            }
            afterXZ = true;
            nextKnown = false;
            continue;
          }
          int64_t v = 0;
          bool based = false;
          nextKnown = literalInt(fC, valueId, v, &based);
          if (!nextKnown) continue;
          next = v;
          // A based literal is a bit pattern: `'hFFFF_FFFF` fits an int.
          const int64_t hi = (based && base.isSigned && base.width < 63)
                                 ? (int64_t(1) << base.width) - 1
                                 : maxV;
          curMax = hi;
          if (base.known && (v < minV || v > hi)) {
            report(ErrorDefinition::COMP_ENUM_VALUE_OUT_OF_RANGE, fC, nameId,
                   name);
            nextKnown = false;
            continue;
          }
        } else if (afterXZ) {
          report(ErrorDefinition::COMP_ENUM_UNASSIGNED_AFTER_XZ, fC, nameId,
                 name);
          afterXZ = false;
          continue;
        } else if (nextKnown && base.known && next > curMax) {
          // The implicit increment overflowed the base type.
          report(ErrorDefinition::COMP_ENUM_VALUE_OUT_OF_RANGE, fC, nameId,
                 name);
          nextKnown = false;
          continue;
        }
        if (!nextKnown) continue;
        const int64_t last = next + static_cast<int64_t>(count) - 1;
        if (base.known && last > curMax) {
          report(ErrorDefinition::COMP_ENUM_VALUE_OUT_OF_RANGE, fC, nameId,
                 name);
          nextKnown = false;
          continue;
        }
        next = last + 1;
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Structural rules the parser accepts but the LRM forbids, checked on the
// parse trees: a module
// instantiated in a program (24.3; the parser reads it as a checker
// instance), a zero replication outside a concatenation (11.4.12.1), and a
// default value on an inout ANSI port (23.2.2.4).
namespace {
// Skips the single-child wrapper nodes above an operand.
NodeId operandParent(const FileContent* fC, NodeId id) {
  NodeId p = fC->Parent(id);
  while (p) {
    const VObjectType t = fC->Type(p);
    if (t != VObjectType::paPrimary && t != VObjectType::paConstant_primary &&
        t != VObjectType::paExpression &&
        t != VObjectType::paConstant_expression)
      break;
    if (fC->Child(p) != id || fC->Sibling(id)) break;
    id = p;
    p = fC->Parent(p);
  }
  return p;
}

bool isZeroLiteral(const FileContent* fC, NodeId expr) {
  NodeId n = expr;
  while (n && (fC->Type(n) == VObjectType::paConstant_expression ||
               fC->Type(n) == VObjectType::paExpression ||
               fC->Type(n) == VObjectType::paConstant_primary ||
               fC->Type(n) == VObjectType::paPrimary ||
               fC->Type(n) == VObjectType::paPrimary_literal)) {
    NodeId c = fC->Child(n);
    if (!c || fC->Sibling(c)) return false;
    n = c;
  }
  if (!n || fC->Type(n) != VObjectType::slIntConst) return false;
  const std::string_view text = fC->SymName(n);
  const size_t tick = text.find('\'');
  std::string_view digits =
      tick == std::string_view::npos ? text : text.substr(tick + 2);
  if (digits.empty()) return false;
  return std::all_of(digits.begin(), digits.end(),
                     [](char c) { return c == '0' || c == '_'; });
}

std::string_view declarationName(const FileContent* fC, NodeId decl) {
  NodeId header = fC->Child(decl);
  for (NodeId c = header ? fC->Child(header) : InvalidNodeId; c;
       c = fC->Sibling(c)) {
    if (fC->Type(c) == VObjectType::slStringConst) return fC->SymName(c);
  }
  return {};
}
}  // namespace

void CompileDesign::checkStructuralRules_() {
  Design* design = m_compiler->getDesign();
  ErrorContainer* errors = m_compiler->getErrorContainer();
  SymbolTable* symbols = m_compiler->getSymbolTable();
  auto report = [&](ErrorDefinition::ErrorType type, const FileContent* fC,
                    NodeId id, std::string_view text) {
    Location loc(fC->getFileId(id), fC->Line(id), fC->Column(id),
                 symbols->registerSymbol(text));
    Error err(type, loc);
    errors->addError(err);
  };
  std::set<std::string, std::less<>> designUnits, checkers;
  for (const auto& [fileId, fC] : design->getAllFileContents()) {
    if (fC == nullptr || fC->getSize() == 0) continue;
    std::vector<NodeId> stack{fC->getRootNode()};
    while (!stack.empty()) {
      NodeId id = stack.back();
      stack.pop_back();
      const VObjectType t = fC->Type(id);
      if (t == VObjectType::paModule_declaration ||
          t == VObjectType::paInterface_declaration ||
          t == VObjectType::paProgram_declaration) {
        designUnits.emplace(declarationName(fC, id));
      } else if (t == VObjectType::paChecker_declaration) {
        for (NodeId c = fC->Child(id); c; c = fC->Sibling(c))
          if (fC->Type(c) == VObjectType::slStringConst) {
            checkers.emplace(fC->SymName(c));
            break;
          }
      }
      for (NodeId c = fC->Child(id); c; c = fC->Sibling(c)) stack.push_back(c);
    }
  }
  for (const auto& [fileId, fC] : design->getAllFileContents()) {
    if (fC == nullptr || fC->getSize() == 0) continue;
    // (node, inside a program)
    std::vector<std::pair<NodeId, bool>> stack{{fC->getRootNode(), false}};
    while (!stack.empty()) {
      auto [id, inProgram] = stack.back();
      stack.pop_back();
      const VObjectType t = fC->Type(id);
      if (t == VObjectType::paProgram_declaration) {
        inProgram = true;
      } else if (t == VObjectType::paModule_declaration ||
                 t == VObjectType::paInterface_declaration) {
        inProgram = false;
      } else if (t == VObjectType::paChecker_instantiation && inProgram) {
        NodeId ps = fC->Child(id);
        NodeId nm = ps ? fC->Child(ps) : InvalidNodeId;
        if (nm && fC->Type(nm) == VObjectType::slStringConst &&
            !fC->Sibling(nm)) {
          const std::string_view name = fC->SymName(nm);
          if (designUnits.count(name) && !checkers.count(name))
            report(ErrorDefinition::COMP_INSTANCE_IN_PROGRAM, fC, nm, name);
        }
      } else if (t == VObjectType::paMultiple_concatenation ||
                 t == VObjectType::paConstant_multiple_concatenation) {
        if (isZeroLiteral(fC, fC->Child(id))) {
          NodeId p = operandParent(fC, id);
          // A concatenation of nothing but zero replications is the
          // empty-concatenation rule's (UH0745) to report.
          const bool inConcat =
              p && (fC->Type(p) == VObjectType::paConcatenation ||
                    fC->Type(p) == VObjectType::paConstant_concatenation);
          if (!inConcat)
            report(ErrorDefinition::COMP_ZERO_REPLICATION, fC, id, "0");
        }
      } else if (t == VObjectType::paList_of_port_declarations) {
        bool inout = false;
        for (NodeId port = fC->Child(id); port; port = fC->Sibling(port)) {
          if (fC->Type(port) != VObjectType::paAnsi_port_declaration) continue;
          NodeId header = fC->Child(port);
          NodeId name = header;
          if (header && fC->Type(header) == VObjectType::slStringConst) {
            // bare name: inherits the previous direction
          } else if (header &&
                     (fC->Type(header) == VObjectType::paNet_port_header ||
                      fC->Type(header) ==
                          VObjectType::paVariable_port_header)) {
            NodeId dir = fC->Child(header);
            if (dir && (fC->Type(dir) == VObjectType::paPortDir_Inp ||
                        fC->Type(dir) == VObjectType::paPortDir_Out ||
                        fC->Type(dir) == VObjectType::paPortDir_Inout ||
                        fC->Type(dir) == VObjectType::paPortDir_Ref))
              inout = fC->Type(dir) == VObjectType::paPortDir_Inout;
          } else {
            inout = false;  // interface port
            continue;
          }
          if (fC->Type(header) != VObjectType::slStringConst)
            name = fC->Sibling(header);
          if (!name || fC->Type(name) != VObjectType::slStringConst) continue;
          NodeId after = fC->Sibling(name);
          while (after &&
                 (fC->Type(after) == VObjectType::paUnpacked_dimension ||
                  fC->Type(after) == VObjectType::paVariable_dimension))
            after = fC->Sibling(after);
          if (inout && after &&
              (fC->Type(after) == VObjectType::paConstant_expression ||
               fC->Type(after) == VObjectType::paExpression))
            report(ErrorDefinition::COMP_INOUT_PORT_DEFAULT, fC, name,
                   fC->SymName(name));
        }
      }
      for (NodeId c = fC->Child(id); c; c = fC->Sibling(c))
        stack.emplace_back(c, inProgram);
    }
  }
}

// ---------------------------------------------------------------------------
// Declaration rules checked on the parse trees: class methods are always
// automatic (8.6), a net's data type is 4-state integral or an unpacked
// array / struct of such (6.7.1), an automatic variable cannot appear in a
// procedural continuous assignment nor be the target of a nonblocking one
// (6.21), and an attribute value is a constant expression (5.12).
namespace {
bool isNetKeyword(VObjectType t) {
  switch (t) {
    case VObjectType::paNetType_Supply0:
    case VObjectType::paNetType_Supply1:
    case VObjectType::paNetType_Tri:
    case VObjectType::paNetType_Tri0:
    case VObjectType::paNetType_Tri1:
    case VObjectType::paNetType_TriAnd:
    case VObjectType::paNetType_TriOr:
    case VObjectType::paNetType_TriReg:
    case VObjectType::paNetType_Uwire:
    case VObjectType::paNetType_Wand:
    case VObjectType::paNetType_Wire:
    case VObjectType::paNetType_Wor:
      return true;
    default:
      return false;
  }
}

bool subtreeHas(const FileContent* fC, NodeId id, VObjectType type) {
  std::vector<NodeId> stack{id};
  while (!stack.empty()) {
    NodeId n = stack.back();
    stack.pop_back();
    if (fC->Type(n) == type) return true;
    for (NodeId c = fC->Child(n); c; c = fC->Sibling(c)) stack.push_back(c);
  }
  return false;
}

// The first identifier of the subtree that is in `names`.
NodeId findName(const FileContent* fC, NodeId id,
                const std::set<std::string, std::less<>>& names) {
  std::vector<NodeId> stack{id};
  while (!stack.empty()) {
    NodeId n = stack.back();
    stack.pop_back();
    if (fC->Type(n) == VObjectType::slStringConst &&
        names.count(fC->SymName(n)))
      return n;
    for (NodeId c = fC->Child(n); c; c = fC->Sibling(c)) stack.push_back(c);
  }
  return InvalidNodeId;
}

// Names a task / function body declares as automatic local variables (every
// local that is not declared `static`).  Formals are left out: an `assign`
// to an output formal has a clear meaning and is synthesized.
void collectAutomaticLocals(const FileContent* fC, NodeId body,
                            std::set<std::string, std::less<>>& names) {
  std::vector<NodeId> stack{body};
  while (!stack.empty()) {
    NodeId n = stack.back();
    stack.pop_back();
    const VObjectType t = fC->Type(n);
    if (t == VObjectType::paData_declaration &&
        fC->Type(fC->Child(n)) == VObjectType::paLifetime_Static)
      continue;
    if (t == VObjectType::paTf_port_list ||
        t == VObjectType::paTf_port_declaration)
      continue;
    if (t == VObjectType::paVariable_decl_assignment) {
      NodeId c = fC->Child(n);
      if (c && fC->Type(c) == VObjectType::slStringConst)
        names.emplace(fC->SymName(c));
    }
    for (NodeId c = fC->Child(n); c; c = fC->Sibling(c)) stack.push_back(c);
  }
}
}  // namespace

void CompileDesign::checkDeclarationRules_() {
  Design* design = m_compiler->getDesign();
  ErrorContainer* errors = m_compiler->getErrorContainer();
  SymbolTable* symbols = m_compiler->getSymbolTable();
  auto report = [&](ErrorDefinition::ErrorType type, const FileContent* fC,
                    NodeId id, std::string_view text) {
    Location loc(fC->getFileId(id), fC->Line(id), fC->Column(id),
                 symbols->registerSymbol(text));
    Error err(type, loc);
    errors->addError(err);
  };
  using Names = std::set<std::string, std::less<>>;
  Names classes;
  for (const auto& [fileId, fC] : design->getAllFileContents()) {
    if (fC == nullptr || fC->getSize() == 0) continue;
    std::vector<NodeId> stack{fC->getRootNode()};
    while (!stack.empty()) {
      NodeId id = stack.back();
      stack.pop_back();
      if (fC->Type(id) == VObjectType::paClass_declaration) {
        for (NodeId c = fC->Child(id); c; c = fC->Sibling(c))
          if (fC->Type(c) == VObjectType::slStringConst) {
            classes.emplace(fC->SymName(c));
            break;
          }
      }
      for (NodeId c = fC->Child(id); c; c = fC->Sibling(c)) stack.push_back(c);
    }
  }
  for (const auto& [fileId, fC] : design->getAllFileContents()) {
    if (fC == nullptr || fC->getSize() == 0) continue;
    std::vector<NodeId> stack{fC->getRootNode()};
    while (!stack.empty()) {
      NodeId id = stack.back();
      stack.pop_back();
      for (NodeId c = fC->Child(id); c; c = fC->Sibling(c)) stack.push_back(c);
      const VObjectType t = fC->Type(id);
      if (t == VObjectType::paClass_method) {
        NodeId decl = fC->Child(id);
        while (decl && fC->Type(decl) != VObjectType::paTask_declaration &&
               fC->Type(decl) != VObjectType::paFunction_declaration)
          decl = fC->Sibling(decl);
        if (decl && fC->Type(fC->Child(decl)) == VObjectType::paLifetime_Static)
          report(ErrorDefinition::COMP_STATIC_CLASS_METHOD, fC, fC->Child(decl),
                 "static");
      } else if (t == VObjectType::paNet_declaration &&
                 isNetKeyword(fC->Type(fC->Child(id)))) {
        // Without a net keyword, `T x [$];` is a variable of a user type
        // that the grammar reads as a user-defined nettype declaration.
        bool bad = false;
        std::string_view what;
        for (NodeId c = fC->Child(id); c && !bad; c = fC->Sibling(c)) {
          if (fC->Type(c) == VObjectType::paData_type_or_implicit ||
              fC->Type(c) == VObjectType::paData_type) {
            NodeId dt =
                fC->Type(c) == VObjectType::paData_type ? c : fC->Child(c);
            if (dt && fC->Type(dt) == VObjectType::paData_type) {
              NodeId k = fC->Child(dt);
              const VObjectType kt = fC->Type(k);
              if (kt == VObjectType::paString_type ||
                  kt == VObjectType::paChandle_type ||
                  kt == VObjectType::paEvent_type) {
                bad = true;
                what = kt == VObjectType::paString_type    ? "string"
                       : kt == VObjectType::paChandle_type ? "chandle"
                                                           : "event";
              } else if (kt == VObjectType::slStringConst && !fC->Sibling(k) &&
                         classes.count(fC->SymName(k))) {
                bad = true;
                what = fC->SymName(k);
              }
            }
          } else if (fC->Type(c) ==
                     VObjectType::paList_of_net_decl_assignments) {
            for (NodeId a = fC->Child(c); a && !bad; a = fC->Sibling(a)) {
              for (NodeId d = fC->Child(a); d; d = fC->Sibling(d)) {
                const VObjectType dt = fC->Type(d);
                if ((dt == VObjectType::paUnpacked_dimension &&
                     subtreeHas(fC, d, VObjectType::paDollar_keyword)) ||
                    dt == VObjectType::paUnsized_dimension ||
                    dt == VObjectType::paAssociative_dimension ||
                    dt == VObjectType::paQueue_dimension) {
                  bad = true;
                  what = fC->SymName(fC->Child(a));
                  break;
                }
              }
            }
          }
        }
        if (bad) report(ErrorDefinition::COMP_INVALID_NET_TYPE, fC, id, what);
      } else if (t == VObjectType::paTask_declaration ||
                 t == VObjectType::paFunction_declaration) {
        NodeId first = fC->Child(id);
        const bool inClass =
            fC->Type(fC->Parent(id)) == VObjectType::paClass_method;
        const bool automatic =
            fC->Type(first) == VObjectType::paLifetime_Automatic ||
            (inClass && fC->Type(first) != VObjectType::paLifetime_Static);
        if (!automatic) continue;
        Names locals;
        collectAutomaticLocals(fC, id, locals);
        if (locals.empty()) continue;
        std::vector<NodeId> st{id};
        while (!st.empty()) {
          NodeId n = st.back();
          st.pop_back();
          const VObjectType nt = fC->Type(n);
          if (nt == VObjectType::paProcedural_continuous_assignment) {
            // Only a local that DRIVES the assignment outlives its call; a
            // local target behaves as a blocking write and is synthesized.
            NodeId target = fC->Child(n);
            while (target &&
                   fC->Type(target) != VObjectType::paVariable_assignment &&
                   fC->Type(target) != VObjectType::paNet_assignment)
              target = fC->Sibling(target);
            NodeId rhs = InvalidNodeId;
            if (target) {
              NodeId lv = fC->Child(target);
              rhs = lv ? fC->Sibling(lv) : InvalidNodeId;
            }
            if (NodeId hit = rhs ? findName(fC, rhs, locals) : InvalidNodeId)
              report(ErrorDefinition::COMP_AUTOMATIC_VAR_MISUSE, fC, hit,
                     fC->SymName(hit));
            continue;
          }
          if (nt == VObjectType::paNonblocking_assignment) {
            NodeId lv = fC->Child(n);
            NodeId ps = lv ? fC->Child(lv) : InvalidNodeId;
            NodeId nm = ps ? fC->Child(ps) : InvalidNodeId;
            if (nm && fC->Type(nm) == VObjectType::slStringConst &&
                !fC->Sibling(nm) && locals.count(fC->SymName(nm)))
              report(ErrorDefinition::COMP_AUTOMATIC_VAR_MISUSE, fC, nm,
                     fC->SymName(nm));
            continue;
          }
          // A nested task / function has its own locals.
          if (n != id && (nt == VObjectType::paTask_declaration ||
                          nt == VObjectType::paFunction_declaration))
            continue;
          for (NodeId c = fC->Child(n); c; c = fC->Sibling(c)) st.push_back(c);
        }
      } else if (t == VObjectType::paModule_declaration) {
        // Attribute values naming a variable or net of the module.
        Names params, signals;
        std::vector<NodeId> attrs;
        std::vector<NodeId> st{id};
        while (!st.empty()) {
          NodeId n = st.back();
          st.pop_back();
          const VObjectType nt = fC->Type(n);
          if (nt == VObjectType::paParam_assignment ||
              nt == VObjectType::paVariable_decl_assignment ||
              nt == VObjectType::paNet_decl_assignment) {
            NodeId nm = fC->Child(n);
            if (nm && fC->Type(nm) == VObjectType::slStringConst)
              (nt == VObjectType::paParam_assignment ? params : signals)
                  .emplace(fC->SymName(nm));
          } else if (nt == VObjectType::paGenvar_declaration ||
                     nt == VObjectType::paType_declaration) {
            std::vector<NodeId> s2{n};
            while (!s2.empty()) {
              NodeId m = s2.back();
              s2.pop_back();
              if (fC->Type(m) == VObjectType::slStringConst)
                params.emplace(fC->SymName(m));
              for (NodeId c = fC->Child(m); c; c = fC->Sibling(c))
                s2.push_back(c);
            }
          } else if (nt == VObjectType::paAttr_spec) {
            attrs.push_back(n);
          }
          if (n != id && (nt == VObjectType::paModule_declaration ||
                          nt == VObjectType::paTask_declaration ||
                          nt == VObjectType::paFunction_declaration))
            continue;
          for (NodeId c = fC->Child(n); c; c = fC->Sibling(c)) st.push_back(c);
        }
        for (const std::string& p : params) signals.erase(p);
        for (NodeId a : attrs) {
          NodeId value = fC->Sibling(fC->Child(a));
          if (!value) continue;
          if (NodeId hit = findName(fC, value, signals))
            report(ErrorDefinition::COMP_NON_CONSTANT_ATTRIBUTE, fC, hit,
                   fC->SymName(hit));
        }
      }
    }
  }
}

bool CompileDesign::compilation_() {
  Design* design = m_compiler->getDesign();

  auto& all_files = design->getAllFileContents();

#if 0
  int32_t maxThreadCount = m_compiler->getCommandLineParser()->getNbMaxTreads();
#else
  // The Actual Module... Compilation is not Multithread safe anymore due to
  // the UHDM model creation
  int32_t maxThreadCount = 0;
#endif

  int32_t index = 0;
  do {
    SymbolTable* symbols =
        m_compiler->getCommandLineParser()->getSymbolTable()->CreateSnapshot();
    m_symbolTables.push_back(symbols);
    ErrorContainer* errors = new ErrorContainer(
        symbols, m_compiler->getErrorContainer()->getLogListener());
    errors->registerCmdLine(m_compiler->getCommandLineParser());
    m_errorContainers.push_back(errors);
    index++;
  } while (index < maxThreadCount);

  for (auto file : all_files) {
    if (m_compiler->isLibraryFile(file.first)) {
      file.second->setLibraryCellFile();
    }
  }

  compileMT_<FileContent, Design::FileIdDesignContentMap, FunctorCreateLookup>(
      all_files, maxThreadCount);

  compileMT_<FileContent, Design::FileIdDesignContentMap, FunctorResolve>(
      all_files, maxThreadCount);

  compileMT_<FileContent, Design::FileIdDesignContentMap,
             FunctorCompileFileContentDecl>(all_files, maxThreadCount);

  collectObjects_(all_files, design, false);
  m_compiler->getDesign()->orderPackages();

  // Compile packages in strict order
  for (auto itr : m_compiler->getDesign()->getOrderedPackageDefinitions()) {
    FunctorCompilePackage funct(this, itr, m_compiler->getDesign(),
                                m_symbolTables[0], m_errorContainers[0]);
    funct.operator()();
  }

  compileMT_<FileContent, Design::FileIdDesignContentMap,
             FunctorCompileFileContent>(all_files, maxThreadCount);

  // Compile modules
  compileMT_<ModuleDefinition, ModuleNameModuleDefinitionMap,
             FunctorCompileModule>(
      m_compiler->getDesign()->getModuleDefinitions(), maxThreadCount);

  // Compile programs
  compileMT_<Program, ProgramNameProgramDefinitionMap, FunctorCompileProgram>(
      m_compiler->getDesign()->getProgramDefinitions(), maxThreadCount);

  if (m_compiler->getCommandLineParser()->parseBuiltIn()) {
    Builtin* builtin = new Builtin(this, design);
    builtin->addBuiltinClasses();
  }

  // Compile Include file info
  FileSystem* const fileSystem = FileSystem::getInstance();
  m_fileInfo = m_serializer.MakeInclude_file_infoVec();
  for (const CompileSourceFile* sourceFile :
       getCompiler()->getCompileSourceFiles()) {
    const PreprocessFile* const pf = sourceFile->getPreprocessor();
    for (const IncludeFileInfo& ifi : pf->getIncludeFileInfo()) {
      if ((ifi.m_context == IncludeFileInfo::Context::INCLUDE) &&
          (ifi.m_action == IncludeFileInfo::Action::PUSH)) {
        UHDM::include_file_info* const pifi =
            m_serializer.MakeInclude_file_info();
        pifi->VpiFile(fileSystem->toPath(pf->getRawFileId()));
        pifi->VpiIncludedFile(fileSystem->toPath(ifi.m_sectionFileId));
        pifi->VpiLineNo(ifi.m_originalStartLine);
        pifi->VpiColumnNo(ifi.m_originalStartColumn);
        pifi->VpiEndLineNo(ifi.m_originalEndLine);
        pifi->VpiEndColumnNo(ifi.m_originalEndColumn);
        m_fileInfo->push_back(pifi);
      }
    }
  }

  // Compile classes
  compileMT_<ClassDefinition, ClassNameClassDefinitionMultiMap,
             FunctorCompileClass>(
      m_compiler->getDesign()->getClassDefinitions(), maxThreadCount);
  bindPendingClassMethodCalls();
  checkPackageImportsExports_();
  checkEnumDeclarations_();
  checkStructuralRules_();
  checkDeclarationRules_();
  design->clearContainers();
  collectObjects_(all_files, design, true);

  if (m_compiler->getCommandLineParser()->parseBuiltIn()) {
    Builtin* builtin = new Builtin(this, design);
    builtin->addBuiltinTypes();
  }

  m_compiler->getDesign()->orderPackages();

  uint32_t size = m_symbolTables.size();
  for (uint32_t i = 0; i < size; i++) {
    m_compiler->getErrorContainer()->appendErrors(*m_errorContainers[i]);
    delete m_symbolTables[i];
    delete m_errorContainers[i];
  }
  return true;
}

bool CompileDesign::elaboration_() {
  PackageAndRootElaboration* packEl = new PackageAndRootElaboration(this);
  packEl->elaborate();
  delete packEl;
  NetlistElaboration* netlistEl = new NetlistElaboration(this);
  netlistEl->elaboratePackages();
  delete netlistEl;
  DesignElaboration* designEl = new DesignElaboration(this);
  designEl->elaborate();
  delete designEl;
  UVMElaboration* uvmEl = new UVMElaboration(this);
  uvmEl->elaborate();
  delete uvmEl;
  return true;
}

void CompileDesign::purgeParsers() { m_compiler->purgeParsers(); }

vpiHandle CompileDesign::writeUHDM(PathId fileId) {
  UhdmWriter* uhdmwriter = new UhdmWriter(this, m_compiler->getDesign());
  vpiHandle h = uhdmwriter->write(fileId);
  delete uhdmwriter;
  return h;
}

void decompile(ValuedComponentI* instance) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  if (instance) {
    ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(instance);
    if (inst) {
      DesignComponent* component = inst->getDefinition();
      while (inst) {
        std::cout << "Instance:" << inst->getFullPathName() << " "
                  << fileSystem->toPath(inst->getFileId()) << "\n";
        std::cout << "Mod: " << inst->getModuleName() << " "
                  << fileSystem->toPath(
                         component->getFileContents()[0]->getFileId())
                  << "\n";

        for (const auto& ps : inst->getMappedValues()) {
          const std::string& name = ps.first;
          Value* val = ps.second.first;
          std::cout << std::string("    " + name + " = " + val->uhdmValue() +
                                   "\n");
        }
        for (const auto& ps : inst->getComplexValues()) {
          const std::string& name = ps.first;
          std::cout << std::string("    " + name + " =  complex\n");
        }
        if (inst->getNetlist() && inst->getNetlist()->param_assigns()) {
          for (auto ps : *inst->getNetlist()->param_assigns()) {
            std::cout << ps->Lhs()->VpiName() << " = "
                      << "\n";
            decompile((UHDM::any*)ps->Rhs());
          }
        }
        inst = inst->getParent();
      }
    }
  }
}
}  // namespace SURELOG
