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

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/ModuleDefinition.h>
#include <Surelog/Design/ModuleInstance.h>
#include <Surelog/Design/Netlist.h>
#include <Surelog/DesignCompile/Builtin.h>
#include <Surelog/DesignCompile/CompileClass.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/CompileFileContent.h>
#include <Surelog/DesignCompile/CompileModule.h>
#include <Surelog/DesignCompile/CompilePackage.h>
#include <Surelog/DesignCompile/CompileProgram.h>
#include <Surelog/DesignCompile/DesignElaboration.h>
#include <Surelog/DesignCompile/NetlistElaboration.h>
#include <Surelog/DesignCompile/PackageAndRootElaboration.h>
#include <Surelog/DesignCompile/ResolveSymbols.h>
#include <Surelog/DesignCompile/UVMElaboration.h>
#include <Surelog/DesignCompile/UhdmWriter.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/Library/Library.h>
#include <Surelog/Package/Package.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Testbench/ClassDefinition.h>
#include <Surelog/Testbench/Program.h>

// UHDM
#include <uhdm/param_assign.h>
#include <uhdm/vpi_visitor.h>

#include <climits>
#include <thread>

#ifdef USETBB
#include <tbb/task.h>
#include <tbb/task_group.h>
#include <tbb/task_scheduler_init.h>
#endif

namespace SURELOG {

namespace fs = std::filesystem;

CompileDesign::CompileDesign(Compiler* compiler) : m_compiler(compiler) {}
CompileDesign::~CompileDesign() {
  // TODO: ownership not clear.
  // delete m_compiler;
}

bool CompileDesign::compile() {
  // Register UHDM Error callbacks
  UHDM::ErrorHandler errHandler =
      [=](UHDM::ErrorType errType, const std::string& msg,
          const UHDM::any* object1, const UHDM::any* object2) {
        ErrorContainer* errors = m_compiler->getErrorContainer();
        SymbolTable* symbols = m_compiler->getSymbolTable();
        if (object1) {
          Location loc1(symbols->registerSymbol(object1->VpiFile().string()),
                        object1->VpiLineNo(), object1->VpiColumnNo(),
                        symbols->registerSymbol(msg));
          if (object2) {
            Location loc2(symbols->registerSymbol(object2->VpiFile().string()),
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
  ErrorContainer* errors = new ErrorContainer(getCompiler()->getSymbolTable());
  errors->registerCmdLine(getCompiler()->getCommandLineParser());
  errors->addError(err1);
  errors->printMessage(err1,
                       getCompiler()->getCommandLineParser()->muteStdout());
  delete errors;
  return (compilation_());
}

template <class ObjectType, class ObjectMapType, typename FunctorType>
void CompileDesign::compileMT_(ObjectMapType& objects, int maxThreadCount) {
  if (maxThreadCount == 0) {
    for (const auto& itr : objects) {
      FunctorType funct(this, itr.second, m_compiler->getDesign(),
                        m_symbolTables[0], m_errorContainers[0]);
      funct.operator()();
    }
  } else {
    // Optimize the load balance, try to even out the work in each thread by the
    // number of VObjects
    std::vector<unsigned long> jobSize(maxThreadCount);
    for (int i = 0; i < maxThreadCount; i++) {
      jobSize[i] = 0;
    }
    std::vector<std::vector<ObjectType*>> jobArray(maxThreadCount);
    for (const auto& mod : objects) {
      unsigned int size = mod.second->getSize();
      if (size == 0) size = 100;
      unsigned int newJobIndex = 0;
      unsigned long long minJobQueue = ULLONG_MAX;
      for (int ii = 0; ii < maxThreadCount; ii++) {
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
      for (int i = 0; i < maxThreadCount; i++) {
        std::cout << "Thread " << i << " : \n";
        for (unsigned int j = 0; j < jobArray[i].size(); j++) {
          std::cout << jobArray[i][j]->getName() << "\n";
        }
      }
    }

    // Create the threads with their respective workloads
    std::vector<std::thread*> threads;
    for (int i = 0; i < maxThreadCount; i++) {
      std::thread* th = new std::thread([=] {
        for (unsigned int j = 0; j < jobArray[i].size(); j++) {
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
    const fs::path fileName = fC->getFileName();
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
        NodeId oldNodeId = existing->getNodeIds()[0];
        fs::path oldFileName = oldFC->getFileName();
        unsigned int oldLine = oldFC->Line(oldNodeId);
        Package* newP = pack.second;
        const FileContent* newFC = newP->getFileContents()[0];
        const FileContent* newParentFile = newFC->getParent();
        NodeId newNodeId = newP->getNodeIds()[0];
        fs::path newFileName = newFC->getFileName();
        unsigned int newLine = newFC->Line(newNodeId);
        if (!finalCollection) {
          if (((oldParentFile != newParentFile) ||
               (oldParentFile == nullptr && newParentFile == nullptr)) &&
              ((oldFileName != newFileName) || (oldLine != newLine))) {
            Location loc1(symbols->registerSymbol(oldFileName.string()),
                          oldLine, oldFC->Column(oldNodeId),
                          symbols->registerSymbol(pack.first));
            Location loc2(symbols->registerSymbol(newFileName.string()),
                          newLine, newFC->Column(newNodeId),
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

bool CompileDesign::elaborate() {
  Location loc(BadSymbolId);
  Error err2(ErrorDefinition::ELAB_ELABORATING_DESIGN, loc);
  ErrorContainer* errors = new ErrorContainer(getCompiler()->getSymbolTable());
  errors->registerCmdLine(getCompiler()->getCommandLineParser());
  errors->addError(err2);
  errors->printMessage(err2,
                       getCompiler()->getCommandLineParser()->muteStdout());
  delete errors;
  return (elaboration_());
}

bool CompileDesign::compilation_() {
  Design* design = m_compiler->getDesign();

  auto& all_files = design->getAllFileContents();

#if 0
  int maxThreadCount = m_compiler->getCommandLineParser()->getNbMaxTreads();
#else
  // The Actual Module... Compilation is not Multithread safe anymore due to
  // the UHDM model creation
  int maxThreadCount = 0;
#endif

  int index = 0;
  do {
    SymbolTable* symbols =
        m_compiler->getCommandLineParser()->getSymbolTable().CreateSnapshot();
    m_symbolTables.push_back(symbols);
    ErrorContainer* errors = new ErrorContainer(symbols);
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
             FunctorCompileFileContent>(all_files, maxThreadCount);
  collectObjects_(all_files, design, false);
  m_compiler->getDesign()->orderPackages();

  // Compile packages in strict order
  for (auto itr : m_compiler->getDesign()->getOrderedPackageDefinitions()) {
    FunctorCompilePackage funct(this, itr, m_compiler->getDesign(),
                                m_symbolTables[0], m_errorContainers[0]);
    funct.operator()();
  }

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

  // Compile classes
  compileMT_<ClassDefinition, ClassNameClassDefinitionMultiMap,
             FunctorCompileClass>(
      m_compiler->getDesign()->getClassDefinitions(), maxThreadCount);
  design->clearContainers();
  collectObjects_(all_files, design, true);

  if (m_compiler->getCommandLineParser()->parseBuiltIn()) {
    Builtin* builtin = new Builtin(this, design);
    builtin->addBuiltinTypes();
  }

  m_compiler->getDesign()->orderPackages();

  unsigned int size = m_symbolTables.size();
  for (unsigned int i = 0; i < size; i++) {
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

vpiHandle CompileDesign::writeUHDM(const std::string& fileName) {
  UhdmWriter* uhdmwriter = new UhdmWriter(this, m_compiler->getDesign());
  vpiHandle h = uhdmwriter->write(fileName);
  delete uhdmwriter;
  return h;
}

void decompile(ValuedComponentI* instance) {
  if (instance) {
    ModuleInstance* inst = valuedcomponenti_cast<ModuleInstance*>(instance);
    if (inst) {
      DesignComponent* component = inst->getDefinition();
      while (inst) {
        std::cout << "Instance:" << inst->getFullPathName() << " "
                  << inst->getFileName() << "\n";
        std::cout << "Mod: " << inst->getModuleName() << " "
                  << component->getFileContents()[0]->getFileName() << "\n";

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
