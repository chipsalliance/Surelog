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
    for (const ScopeInfo* p : it->second)
      if (p->declared.count(name)) return true;
    return false;
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
          // Only the wildcard imports ABOVE a reference compete for it
          // (LRM 26.3, the `import p2::*` after `x = f()` example).
          if (ambiguousRef == nullptr) {
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
