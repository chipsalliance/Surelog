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

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/Containers.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/Session.h"
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
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/IncludeFileInfo.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Testbench/Program.h"

// UHDM
#include <uhdm/param_assign.h>
#include <uhdm/uhdm_types.h>
#include <uhdm/vpi_visitor.h>

#include <climits>
#include <cstdint>
#include <iostream>
#include <map>
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
CompileDesign::CompileDesign(Session* session, Compiler* compiler)
    : m_session(session), m_compiler(compiler) {}

CompileDesign::~CompileDesign() {
  // TODO: ownership not clear.
  // delete m_compiler;
}

uhdm::Serializer& CompileDesign::getSerializer() {
  return m_compiler->getSerializer();
}

void CompileDesign::lockSerializer() { m_compiler->lockSerializer(); }

void CompileDesign::unlockSerializer() { m_compiler->unlockSerializer(); }

bool CompileDesign::compile() {
  // Register UHDM Error callbacks
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errors = m_session->getErrorContainer();
  SymbolTable* const symbols = m_session->getSymbolTable();
  uhdm::ErrorHandler errHandler =
      [=](uhdm::ErrorType errType, std::string_view msg,
          const uhdm::Any* object1, const uhdm::Any* object2) {
        if (object1) {
          Location loc1(fileSystem->toPathId(object1->getFile(), symbols),
                        object1->getStartLine(), object1->getStartColumn(),
                        symbols->registerSymbol(msg));
          if (object2) {
            Location loc2(fileSystem->toPathId(object2->getFile(), symbols),
                          object2->getStartLine(), object2->getStartColumn());
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

  uhdm::Serializer& serializer = m_compiler->getSerializer();
  serializer.setErrorHandler(errHandler);

  if (ErrorContainer* errors2 = new ErrorContainer(m_session)) {
    Location loc(BadSymbolId);
    Error err1(ErrorDefinition::COMP_COMPILE, loc);
    errors2->addError(err1);
    errors2->printMessage(err1,
                          m_session->getCommandLineParser()->muteStdout());
    delete errors2;
  }
  return (compilation_());
}

template <class ObjectType, class ObjectMapType, typename FunctorType>
void CompileDesign::compileMT_(ObjectMapType& objects, int32_t maxThreadCount) {
  CommandLineParser* const clp = m_session->getCommandLineParser();
  if (maxThreadCount == 0) {
    for (const auto& itr : objects) {
      FunctorType funct(m_session, this, itr.second, m_compiler->getDesign());
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

    if (clp->profile()) {
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
          FunctorType funct(m_sessions[i], this, jobArray[i][j],
                            m_compiler->getDesign());
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
  SymbolTable* const symbols = m_session->getSymbolTable();
  ErrorContainer* const errors = m_session->getErrorContainer();
  // Collect all packages and module definitions
  for (const auto& file : all_files) {
    const FileContent* fC = file.second;
    Library* lib = fC->getLibrary();
    for (const auto& mod : fC->getModuleDefinitions()) {
      if (ModuleDefinition* existing = design->getModuleDefinition(mod.first)) {
        const FileContent* oldFC = existing->getFileContents()[0];
        const FileContent* oldParentFile = oldFC->getParent();

        ModuleDefinition* newM = mod.second;
        const FileContent* newFC = newM->getFileContents()[0];
        const FileContent* newParentFile = newFC->getParent();

        if (oldParentFile && (oldParentFile == newParentFile)) {
          // Recombine splitted module
          existing->addFileContent(mod.second->getFileContents()[0],
                                   mod.second->getNodeIds()[0]);
          for (auto& classdef : mod.second->getClassDefinitions()) {
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
    for (auto& pack : fC->getPackageDefinitions()) {
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
          for (auto& classdef : pack.second->getClassDefinitions()) {
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

bool CompileDesign::elaborate() {
  if (ErrorContainer* errors = new ErrorContainer(m_session)) {
    Error err(ErrorDefinition::ELAB_ELABORATING_DESIGN, Location(BadSymbolId));
    errors->addError(err);
    errors->printMessage(err, m_session->getCommandLineParser()->muteStdout());
    delete errors;
  }
  return (elaboration_());
}

bool CompileDesign::compilation_() {
  CommandLineParser* const clp = m_session->getCommandLineParser();
  Design* const design = m_compiler->getDesign();

  auto& all_files = design->getAllFileContents();

#if 0
  int32_t maxThreadCount = m_session->getCommandLineParser()->getMaxTreads();
#else
  // The Actual Module... Compilation is not Multithread safe anymore due to
  // the UHDM model creation
  int32_t maxThreadCount = 0;
#endif

  for (int32_t i = 0; i < maxThreadCount; ++i) {
    SymbolTable* const symbols = m_session->getSymbolTable()->CreateSnapshot();
    m_sessions.emplace_back(new Session(m_session->getFileSystem(), symbols,
                                        m_session->getLogListener(), nullptr,
                                        m_session->getCommandLineParser(),
                                        m_session->getPrecompiled()));
  }

  for (auto& file : all_files) {
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
    FunctorCompilePackage funct(m_session, this, itr, m_compiler->getDesign());
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

  if (clp->parseBuiltIn()) {
    Builtin builtin(m_session, this, design);
    builtin.addBuiltinTypes();
    builtin.addBuiltinClasses();
  }

  // Compile classes
  compileMT_<ClassDefinition, ClassNameClassDefinitionMultiMap,
             FunctorCompileClass>(
      m_compiler->getDesign()->getClassDefinitions(), maxThreadCount);
  design->clearContainers();

  collectObjects_(all_files, design, true);

  m_compiler->getDesign()->orderPackages();

  ErrorContainer* const errors = m_session->getErrorContainer();
  for (Session* session : m_sessions) {
    errors->appendErrors(*session->getErrorContainer());
    delete session;
  }
  m_sessions.clear();
  return true;
}

bool CompileDesign::elaboration_() {
  if (PackageAndRootElaboration* packEl =
          new PackageAndRootElaboration(m_session, this)) {
    packEl->elaborate();
    delete packEl;
  }
  if (NetlistElaboration* netlistEl = new NetlistElaboration(m_session, this)) {
    netlistEl->elaboratePackages();
    delete netlistEl;
  }
  if (DesignElaboration* designEl = new DesignElaboration(m_session, this)) {
    designEl->elaborate();
    delete designEl;
  }
  if (UVMElaboration* uvmEl = new UVMElaboration(m_session, this)) {
    uvmEl->elaborate();
    delete uvmEl;
  }
  return true;
}

void CompileDesign::purgeParsers() { m_compiler->purgeParsers(); }

bool CompileDesign::writeUHDM(PathId fileId) {
  bool result = false;
  if (UhdmWriter* uhdmwriter =
          new UhdmWriter(m_session, this, m_compiler->getDesign())) {
    result = uhdmwriter->write(fileId);
    delete uhdmwriter;
  }
  return result;
}

void decompile(Session* session, ValuedComponentI* instance) {
  FileSystem* const fileSystem = session->getFileSystem();
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
            std::cout << ps->getLhs()->getName() << " = \n";
            decompile((uhdm::Any*)ps->getRhs());
          }
        }
        inst = inst->getParent();
      }
    }
  }
}
}  // namespace SURELOG
