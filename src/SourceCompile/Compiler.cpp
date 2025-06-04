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
 * File:   Compiler.cpp
 * Author: alain
 *
 * Created on March 4, 2017, 5:16 PM
 */

#include "Surelog/SourceCompile/Compiler.h"

#include <uhdm/design.h>
#include <uhdm/preproc_macro_definition.h>
#include <uhdm/preproc_macro_instance.h>
#include <uhdm/source_file.h>

#include <climits>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <nlohmann/json.hpp>
#include <string>
#include <string_view>
#include <thread>
#include <vector>

#include "Surelog/API/PythonAPI.h"
#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/Containers.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Common/SymbolId.h"
#include "Surelog/Config/ConfigSet.h"
#include "Surelog/Design/Design.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/DesignCompile/Builtin.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Library/LibrarySet.h"
#include "Surelog/Library/ParseLibraryDef.h"
#include "Surelog/Package/Precompiled.h"
#include "Surelog/SourceCompile/AnalyzeFile.h"
#include "Surelog/SourceCompile/CheckCompile.h"
#include "Surelog/SourceCompile/CompilationUnit.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"
#include "Surelog/SourceCompile/ParseFile.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Utils/StringUtils.h"
#include "Surelog/Utils/Timer.h"

#if defined(_MSC_VER)
#include <direct.h>
#else
#include <unistd.h>
#endif

namespace SURELOG {

#if defined(_WIN32)
const std::string_view kSystemCommandSeparator = " && ";
#else
const std::string_view kSystemCommandSeparator = "; ";
#endif

namespace fs = std::filesystem;

Compiler::Compiler(Session* session)
    : m_session(session),
      m_commonCompilationUnit(nullptr),
      m_librarySet(new LibrarySet()),
      m_configSet(new ConfigSet()),
      m_design(new Design(m_session, m_serializer, m_librarySet, m_configSet)),
      m_compileDesign(nullptr) {
#ifdef USETBB
  if (m_session->useTbb() && (m_session->getMaxTreads() > 0))
    tbb::task_scheduler_init init(m_session->getMaxTreads());
#endif
}

Compiler::Compiler(Session* session, std::string_view text)
    : m_session(session),
      m_commonCompilationUnit(nullptr),
      m_librarySet(new LibrarySet()),
      m_configSet(new ConfigSet()),
      m_design(new Design(m_session, m_serializer, m_librarySet, m_configSet)),
      m_text(text),
      m_compileDesign(nullptr) {}

Compiler::~Compiler() {
  DeleteAssociativeContainerValuePointersAndClear(&m_antlrPpMap);
  delete m_design;
  delete m_configSet;
  delete m_librarySet;
  delete m_commonCompilationUnit;

  cleanup_();
  m_serializer.purge();
}

void Compiler::purgeParsers() {
  DeleteAssociativeContainerValuePointersAndClear(&m_antlrPpMap);
  DeleteSequenceContainerPointersAndClear(&m_compilers);
}

struct FunctorCompileOneFile {
  FunctorCompileOneFile(CompileSourceFile* compileSource,
                        CompileSourceFile::Action action)
      : m_compileSourceFile(compileSource), m_action(action) {}

  int32_t operator()() const {
#ifdef SURELOG_WITH_PYTHON
    if (m_session->pythonListener() || m_session->pythonEvalScriptPerFile()) {
      PyThreadState* interpState = PythonAPI::initNewInterp();
      m_compileSourceFile->setPythonInterp(interpState);
    }
#endif
    return m_compileSourceFile->compile(m_action);
  }

 private:
  CompileSourceFile* m_compileSourceFile;
  CompileSourceFile::Action m_action;
};

bool Compiler::compileOneFile_(CompileSourceFile* compiler,
                               CompileSourceFile::Action action) {
  bool status = compiler->compile(action);
  return status;
}

bool Compiler::isLibraryFile(PathId id) const {
  return (m_libraryFiles.find(id) != m_libraryFiles.end());
}

bool Compiler::ppinit_() {
  FileSystem* const fileSystem = m_session->getFileSystem();
  CommandLineParser* const clp = m_session->getCommandLineParser();
  if (!clp->fileUnit()) {
    m_commonCompilationUnit = new CompilationUnit(false);
    if (clp->parseBuiltIn()) {
      Builtin(m_session, nullptr, nullptr)
          .addBuiltinMacros(m_commonCompilationUnit);
    }
  }

  CompilationUnit* comp_unit = m_commonCompilationUnit;

  // Source files (.v, .sv on the command line)
  PathIdSet sourceFiles;
  for (const PathId& sourceFileId : clp->getSourceFiles()) {
    SymbolTable* symbols = m_session->getSymbolTable();
    if (clp->fileUnit()) {
      comp_unit = new CompilationUnit(true);
      m_compilationUnits.emplace_back(comp_unit);
      symbols = symbols->CreateSnapshot();
    }

    Library* library = m_librarySet->getLibrary(sourceFileId);
    sourceFiles.insert(sourceFileId);

    Session* const session = new Session(
        m_session->getFileSystem(), symbols, m_session->getLogListener(),
        nullptr, m_session->getCommandLineParser(), nullptr);
    m_sessions.emplace_back(session);

    if (clp->fileUnit() && clp->parseBuiltIn()) {
      Builtin(session, nullptr, nullptr).addBuiltinMacros(comp_unit);
    }

    CompileSourceFile* compiler =
        new CompileSourceFile(session, sourceFileId, this, comp_unit, library);
    m_compilers.emplace_back(compiler);
  }

  if (!m_text.empty()) {
    Library* library = new Library(m_session, "UnitTest");
    CompileSourceFile* compiler = new CompileSourceFile(
        m_session, BadPathId, this, comp_unit, library, m_text);
    m_compilers.emplace_back(compiler);
  }

  // Library files
  PathIdSet libFileIdSet;
  // (-v <file>)
  const auto& libFiles = clp->getLibraryFiles();
  std::copy_if(libFiles.begin(), libFiles.end(),
               std::inserter(libFileIdSet, libFileIdSet.end()),
               [&sourceFiles](const PathId& libFileId) {
                 return sourceFiles.find(libFileId) == sourceFiles.end();
               });

  // (-y <path> +libext+<ext>)
  for (const PathId& libFileId : clp->getLibraryPaths()) {
    for (const SymbolId& ext : clp->getLibraryExtensions()) {
      PathIdVector fileIds;
      fileSystem->collect(libFileId,
                          m_session->getSymbolTable()->getSymbol(ext),
                          m_session->getSymbolTable(), fileIds);
      std::copy_if(fileIds.begin(), fileIds.end(),
                   std::inserter(libFileIdSet, libFileIdSet.end()),
                   [&](const PathId& libFileId) {
                     if (sourceFiles.find(libFileId) == sourceFiles.end()) {
                       bool fileContainsModuleOfSameName = false;
                       std::filesystem::path dir_entry =
                           fileSystem->toPath(libFileId);
                       std::ifstream ifs(dir_entry.string());
                       if (ifs.good()) {
                         std::stringstream buffer;
                         buffer << ifs.rdbuf();
                         std::string moduleName = dir_entry.stem().string();
                         const std::regex regexpMod{"(module)[ \t]+(" +
                                                    moduleName + ")"};
                         if (std::regex_search(buffer.str(), regexpMod)) {
                           fileContainsModuleOfSameName = true;
                         }
                         const std::regex regexpPrim{"(primitive)[ \t]+(" +
                                                     moduleName + ")"};
                         if (std::regex_search(buffer.str(), regexpPrim)) {
                           fileContainsModuleOfSameName = true;
                         }
                         const std::regex regexpPack{"(package)[ \t]"};
                         if (std::regex_search(buffer.str(), regexpPack)) {
                           // Files containing packages cannot be imported with
                           // -y
                           fileContainsModuleOfSameName = false;
                         }
                       }
                       ifs.close();
                       return fileContainsModuleOfSameName;
                     } else {
                       return false;
                     }
                   });
    }
  }
  for (const auto& libFileId : libFileIdSet) {
    // This line registers the file in the "work" library:
    /*Library* library  = */ m_librarySet->getLibrary(libFileId);
    m_libraryFiles.insert(libFileId);
  }

  // Libraries (.map)
  for (auto& lib : m_librarySet->getLibraries()) {
    for (const PathId& id : lib.getFiles()) {
      if (sourceFiles.find(id) != sourceFiles.end()) {
        // These files are already included in the command line
        continue;
      }

      std::string_view type =
          std::get<1>(fileSystem->getType(id, m_session->getSymbolTable()));
      if (type == ".map") {
        // .map files are not parsed with the regular parser
        continue;
      }
      SymbolTable* symbols = m_session->getSymbolTable();
      if (clp->fileUnit()) {
        comp_unit = new CompilationUnit(true);
        m_compilationUnits.emplace_back(comp_unit);
        symbols = symbols->CreateSnapshot();
      }
      Session* const session = new Session(
          m_session->getFileSystem(), symbols, m_session->getLogListener(),
          nullptr, m_session->getCommandLineParser(), nullptr);
      m_sessions.emplace_back(session);

      CompileSourceFile* compiler =
          new CompileSourceFile(session, id, this, comp_unit, &lib);
      m_compilers.emplace_back(compiler);
    }
  }
  return true;
}

bool Compiler::createFileList_() {
  CommandLineParser* const clp = m_session->getCommandLineParser();
  if (!((clp->writePpOutput() || clp->writePpOutputFileId()) &&
        (!clp->parseOnly()))) {
    return true;
  }
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  {
    PathId fileId =
        fileSystem->getChild(clp->getCompileDirId(), "file.lst", symbols);
    std::ostream& ofs = fileSystem->openForWrite(fileId);
    if (ofs.good()) {
      for (CompileSourceFile* sourceFile : m_compilers) {
        m_ppFileMap[sourceFile->getFileId()].emplace_back(
            sourceFile->getPpOutputFileId());

        ofs << fileSystem->toPath(sourceFile->getPpOutputFileId()) << std::endl;
      }
      ofs.flush();
      fileSystem->close(ofs);
    } else {
      std::cerr << "Could not create filelist: " << PathIdPP(fileId, fileSystem)
                << std::endl;
    }
  }
  {
    PathId fileId =
        fileSystem->getChild(clp->getCompileDirId(), "file_map.lst", symbols);
    std::ostream& ofs = fileSystem->openForWrite(fileId);
    if (ofs.good()) {
      for (CompileSourceFile* sourceFile : m_compilers) {
        ofs << fileSystem->toPath(sourceFile->getPpOutputFileId()) << " "
            << fileSystem->toPath(sourceFile->getFileId()) << std::endl;
      }
      ofs.flush();
      fileSystem->close(ofs);
    } else {
      std::cerr << "Could not create filelist: " << PathIdPP(fileId, fileSystem)
                << std::endl;
    }
  }
  {
    if (clp->sepComp()) {
      std::ostringstream concatFiles;
      for (CompileSourceFile* sourceFile : m_compilers) {
        const PathId sourceFileId = sourceFile->getFileId();
        concatFiles << fileSystem->toPath(sourceFileId) << "|";
      }
      std::size_t val = std::hash<std::string>{}(concatFiles.str());
      {
        std::string hashedName = std::to_string(val) + ".sep_lst";
        PathId fileId =
            fileSystem->getChild(clp->getCompileDirId(), hashedName, symbols);
        std::ostream& ofs = fileSystem->openForWrite(fileId);
        if (ofs.good()) {
          for (CompileSourceFile* sourceFile : m_compilers) {
            ofs << fileSystem->toPath(sourceFile->getFileId()) << " ";
          }
          fileSystem->close(ofs);
        } else {
          std::cerr << "Could not create filelist: "
                    << PathIdPP(fileId, fileSystem) << std::endl;
        }
      }
      {
        std::string hashedName = std::to_string(val) + ".sepcmd.json";
        PathId fileId =
            fileSystem->getChild(clp->getCompileDirId(), hashedName, symbols);
        nlohmann::json sources;
        for (CompileSourceFile* sourceFile : m_compilers) {
          auto [prefix, suffix] =
              fileSystem->toSplitPlatformPath(sourceFile->getFileId());
          nlohmann::json entry;
          entry["base_directory"] = prefix;
          entry["relative_filepath"] = suffix;
          sources.emplace_back(entry);
        }

        nlohmann::json workingDirectories;
        for (const auto& wd : fileSystem->getWorkingDirs()) {
          workingDirectories.emplace_back(wd);
        }

        std::ostream& ofs = fileSystem->openForWrite(fileId);
        if (ofs.good()) {
          nlohmann::json table;
          table["sources"] = sources;
          table["working_directories"] = fileSystem->getWorkingDirs();
          // workingDirectories;
          ofs << std::setw(2) << table << std::endl;
          fileSystem->close(ofs);
        } else {
          std::cerr << "Could not create filelist: "
                    << PathIdPP(fileId, fileSystem) << std::endl;
        }
      }
    }
  }
  return true;
}

bool Compiler::createMultiProcessParser_() {
  CommandLineParser* const clp = m_session->getCommandLineParser();
  uint32_t nbProcesses = clp->getMaxProcesses();
  if (nbProcesses == 0) return true;

  if (!(clp->writePpOutput() || clp->writePpOutputFileId())) {
    return true;
  }

  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();

  // Create CMakeLists.txt
  const bool muted = clp->muteStdout();
  const fs::path outputDir =
      fileSystem->toPlatformAbsPath(clp->getOutputDirId());
  const fs::path programPath =
      fileSystem->toPlatformAbsPath(clp->getProgramId());
  const std::string_view profile = clp->profile() ? " -profile " : " ";
  const std::string_view sverilog = clp->fullSVMode() ? " -sverilog " : " ";
  const std::string_view fileUnit = clp->fileUnit() ? " -fileunit " : " ";
  std::string synth = clp->reportNonSynthesizable() ? " -synth " : " ";
  synth += clp->reportNonSynthesizableWithFormal() ? " -formal " : " ";
  const std::string_view noHash = clp->noCacheHash() ? " -nohash " : " ";

  // Optimize the load balance, try to even out the work in each thread by
  // the size of the files
  std::vector<std::vector<CompileSourceFile*>> jobArray(nbProcesses);
  std::vector<uint64_t> jobSize(nbProcesses, 0);
  size_t largestJob = 0;
  for (const auto& compiler : m_compilers) {
    size_t size = compiler->getJobSize(CompileSourceFile::Action::Parse);
    if (size > largestJob) {
      largestJob = size;
    }
  }

  uint32_t bigJobThreashold = (largestJob / nbProcesses) * 3;
  std::vector<CompileSourceFile*> bigJobs;
  Precompiled* const precompiled = m_session->getPrecompiled();
  const fs::path workingDir = fileSystem->getWorkingDir();
  for (const auto& compiler : m_compilers) {
    if (precompiled->isFilePrecompiled(compiler->getFileId())) {
      continue;
    }
    uint32_t size = compiler->getJobSize(CompileSourceFile::Action::Parse);
    if (size > bigJobThreashold) {
      bigJobs.emplace_back(compiler);
      continue;
    }
    uint32_t newJobIndex = 0;
    uint64_t minJobQueue = ULLONG_MAX;
    for (size_t ii = 0; ii < nbProcesses; ii++) {
      if (jobSize[ii] < minJobQueue) {
        newJobIndex = ii;
        minJobQueue = jobSize[ii];
      }
    }
    jobSize[newJobIndex] += size;
    jobArray[newJobIndex].emplace_back(compiler);
  }

  std::vector<std::string> batchProcessCommands;
  std::vector<std::string> targets;
  int32_t absoluteIndex = 0;

  // Big jobs
  for (CompileSourceFile* compiler : bigJobs) {
    SymbolTable* const symbols = m_session->getSymbolTable();
    FileSystem* const fileSystem = m_session->getFileSystem();
    absoluteIndex++;
    std::string targetname =
        StrCat(absoluteIndex, "_",
               std::get<1>(fileSystem->getLeaf(compiler->getPpOutputFileId(),
                                               symbols)));
    std::string_view svFile =
        clp->isSVFile(compiler->getFileId()) ? " -sv " : " ";
    std::string batchCmd =
        StrCat(profile, fileUnit, sverilog, synth, noHash,
               " -parseonly -nostdout -nobuiltin -mt 0 -mp 0 -l ",
               targetname + ".log ", svFile,
               fileSystem->toPath(compiler->getPpOutputFileId()));
    for (const std::string& wd : fileSystem->getWorkingDirs()) {
      StrAppend(&batchCmd, " -wd ", wd);
    }

    if (nbProcesses > 1) {
      StrAppend(&batchCmd, " -o ", outputDir);
    }

    targets.emplace_back(std::move(targetname));
    batchProcessCommands.emplace_back(std::move(batchCmd));
  }

  // Small jobs batch in clump processes
  for (size_t i = 0; i < nbProcesses; i++) {
    std::string fileList;
    absoluteIndex++;
    for (const auto compiler : jobArray[i]) {
      Session* const session = compiler->getSession();
      FileSystem* const fileSystem = session->getFileSystem();
      fs::path fileName =
          fileSystem->toPlatformAbsPath(compiler->getPpOutputFileId());
      std::string_view svFile =
          clp->isSVFile(compiler->getFileId()) ? " -sv " : " ";
      StrAppend(&fileList, svFile, fileName);
    }
    if (!fileList.empty()) {
      std::string targetname =
          StrCat(std::to_string(absoluteIndex), "_",
                 std::get<1>(fileSystem->getLeaf(
                     jobArray[i].back()->getPpOutputFileId(),
                     jobArray[i].back()->getSession()->getSymbolTable())));

      std::string batchCmd =
          StrCat(profile, fileUnit, sverilog, synth, noHash,
                 " -parseonly -nostdout -nobuiltin -mt 0 -mp 0 -l ",
                 targetname + ".log ", fileList);
      for (const std::string& wd : fileSystem->getWorkingDirs()) {
        StrAppend(&batchCmd, " -wd ", wd);
      }

      if (nbProcesses > 1) {
        StrAppend(&batchCmd, " -o ", outputDir);
      }

      targets.emplace_back(std::move(targetname));
      batchProcessCommands.emplace_back(std::move(batchCmd));
    }
  }

  const PathId dirId =
      fileSystem->getPpMultiprocessingDir(clp->fileUnit(), symbols);
  fileSystem->mkdirs(dirId);

  if (nbProcesses == 1) {
    // Single child process
    const PathId fileId =
        fileSystem->getChild(dirId, "parser_batch.txt", symbols);
    if (!fileSystem->writeLines(fileId, batchProcessCommands)) {
      std::cerr << "FATAL: Could not create file: "
                << PathIdPP(fileId, fileSystem) << std::endl;
      return false;
    }

    const std::string command =
        StrCat("cd ", workingDir, kSystemCommandSeparator, programPath, " -o ",
               outputDir, " -nostdout -batch ", fileSystem->toPath(fileId));
    if (!muted) std::cout << "Running: " << command << std::endl << std::flush;
    int32_t result = system(command.c_str());
    if (!muted) std::cout << "Surelog parsing status: " << result << std::endl;
    if (!result) return false;
  } else {
    // Multiple child processes managed by cmake
    const PathId fileId =
        fileSystem->getChild(dirId, "CMakeLists.txt", symbols);
    std::ostream& ofs = fileSystem->openForWrite(fileId);
    if (ofs.good()) {
      ofs << "cmake_minimum_required (VERSION 3.0)" << std::endl;
      ofs << "# Auto generated by Surelog" << std::endl;
      ofs << "project(SurelogParsing NONE)" << std::endl << std::endl;

      for (int32_t i = 0, n = targets.size(); i < n; ++i) {
        ofs << "add_custom_command(OUTPUT " << targets[i] << std::endl;
        ofs << "  COMMAND " << programPath << batchProcessCommands[i];
        ofs << std::endl;
        ofs << "  WORKING_DIRECTORY " << workingDir << std::endl;
        ofs << ")" << std::endl;
      }
      ofs << std::endl;

      ofs << "add_custom_target(Parse ALL DEPENDS" << std::endl;
      for (const auto& target : targets) {
        ofs << "  " << target << std::endl;
      }
      ofs << ")" << std::endl;
      ofs << std::flush;
      fileSystem->close(ofs);
    } else {
      std::cerr << "FATAL: Could not create file: "
                << PathIdPP(fileId, fileSystem) << std::endl;
      return false;
    }

    const std::string command =
        StrCat("cd ", fileSystem->toPath(dirId),
               "; cmake -G \"Unix Makefiles\" .; make -j ", nbProcesses);
    if (!muted) std::cout << "Running: " << command << std::endl << std::flush;
    int32_t result = system(command.c_str());
    if (!muted) std::cout << "Surelog parsing status: " << result << std::endl;
    if (!result) return false;
  }
  return true;
}

bool Compiler::createMultiProcessPreProcessor_() {
  CommandLineParser* const clp = m_session->getCommandLineParser();
  uint32_t nbProcesses = clp->getMaxProcesses();
  if (nbProcesses == 0) return true;

  if (!(clp->writePpOutput() || clp->writePpOutputFileId())) {
    return true;
  }

  FileSystem* const fileSystem = m_session->getFileSystem();
  SymbolTable* const symbols = m_session->getSymbolTable();

  const bool muted = clp->muteStdout();
  const fs::path workingDir = fileSystem->getWorkingDir();
  const fs::path outputDir =
      fileSystem->toPlatformAbsPath(clp->getOutputDirId());
  const fs::path programPath =
      fileSystem->toPlatformAbsPath(clp->getProgramId());
  const std::string_view profile = clp->profile() ? " -profile " : " ";
  const std::string_view sverilog = clp->fullSVMode() ? " -sverilog " : " ";
  const std::string_view fileUnit = clp->fileUnit() ? " -fileunit " : " ";
  std::string synth = clp->reportNonSynthesizable() ? " -synth " : " ";
  synth += clp->reportNonSynthesizableWithFormal() ? " -formal " : " ";
  const std::string_view noHash = clp->noCacheHash() ? " -nohash " : " ";

  std::string fileList;
  // +define+
  for (const auto& [id, value] : clp->getDefineList()) {
    const std::string_view defName = symbols->getSymbol(id);
    std::string val = StringUtils::replaceAll(value, "#", "\\#");
    StrAppend(&fileList, " -D", defName, "=", val);
  }

  // Source files (.v, .sv on the command line)
  for (const PathId& id : clp->getSourceFiles()) {
    std::string_view svFile = clp->isSVFile(id) ? " -sv " : " ";
    StrAppend(&fileList, svFile, fileSystem->toPath(id));
  }
  // Library files (-v <file>)
  for (const PathId& id : clp->getLibraryFiles()) {
    StrAppend(&fileList, " -v ", fileSystem->toPath(id));
  }
  // (-y <path> +libext+<ext>)
  for (const PathId& id : clp->getLibraryPaths()) {
    StrAppend(&fileList, " -y ", fileSystem->toPath(id));
  }
  // +libext+
  for (const SymbolId& id : clp->getLibraryExtensions()) {
    const std::string_view extName = symbols->getSymbol(id);
    StrAppend(&fileList, " +libext+", extName);
  }
  // Include dirs
  for (const PathId& id : clp->getIncludePaths()) {
    StrAppend(&fileList, " -I", fileSystem->toPath(id));
  }

  std::string batchCmd = StrCat(profile, fileUnit, sverilog, synth, noHash,
                                " -writepp -mt 0 -mp 0 -nobuiltin -noparse "
                                "-nostdout -l preprocessing.log -cd ",
                                workingDir, fileList);
  for (const std::string& wd : fileSystem->getWorkingDirs()) {
    StrAppend(&batchCmd, " -wd ", wd);
  }

  const PathId dirId =
      fileSystem->getParserMultiprocessingDir(clp->fileUnit(), symbols);
  fileSystem->mkdirs(dirId);

  if (nbProcesses == 1) {
    // Single child process
    const PathId fileId = fileSystem->getChild(dirId, "pp_batch.txt", symbols);
    if (!fileSystem->writeContent(fileId, batchCmd)) {
      std::cerr << "FATAL: Could not create file: "
                << PathIdPP(fileId, fileSystem) << std::endl;
      return false;
    }
    std::string command =
        StrCat("cd ", workingDir, kSystemCommandSeparator, programPath, " -o ",
               outputDir, " -nostdout -batch ", fileSystem->toPath(fileId));
    if (!muted) std::cout << "Running: " << command << std::endl << std::flush;
    int32_t result = system(command.c_str());
    if (!muted) std::cout << "Surelog preproc status: " << result << std::endl;
    if (!result) return false;
  } else {
    // Create CMakeLists.txt
    StrAppend(&batchCmd, " -o ", outputDir);

    const PathId fileId =
        fileSystem->getChild(dirId, "CMakeLists.txt", symbols);
    std::ostream& ofs = fileSystem->openForWrite(fileId);
    if (ofs.good()) {
      ofs << "cmake_minimum_required (VERSION 3.0)" << std::endl;
      ofs << "# Auto generated by Surelog" << std::endl;
      ofs << "project(SurelogPreprocessing NONE)" << std::endl << std::endl;
      ofs << "add_custom_command(OUTPUT preprocessing" << std::endl;
      ofs << "  COMMAND " << programPath << batchCmd << std::endl;
      ofs << "  WORKING_DIRECTORY " << workingDir << std::endl;
      ofs << ")" << std::endl << std::endl;
      ofs << "add_custom_target(Parse ALL DEPENDS preprocessing)" << std::endl;
      ofs << std::flush;
      fileSystem->close(ofs);
    } else {
      std::cerr << "FATAL: Could not create file: "
                << PathIdPP(fileId, fileSystem) << std::endl;
      return false;
    }

    std::string command =
        StrCat("cd ", fileSystem->toPath(dirId),
               "; cmake -G \"Unix Makefiles\" .; make -j ", nbProcesses);
    if (!muted) std::cout << "Running: " << command << std::endl << std::flush;
    int32_t result = system(command.c_str());
    if (!muted) std::cout << "Surelog preproc status: " << result << std::endl;
    if (!result) return false;
  }

  return true;
}

static int32_t calculateEffectiveThreads(int32_t nbThreads) {
  if (nbThreads <= 4) return nbThreads;
  return (int32_t)(log(((float)nbThreads + 1.0) / 4.0) * 10.0);
}

bool Compiler::parseinit_() {
  Precompiled* const prec = m_session->getPrecompiled();
  CommandLineParser* const clp = m_session->getCommandLineParser();

  // Single out the large files.
  // Small files are going to be scheduled in multiple threads based on size.
  // Large files are going to be compiled in a different batch in multithread

  std::vector<CompileSourceFile*> tmp_compilers;
  for (CompileSourceFile* const compiler : m_compilers) {
    const uint32_t nbThreads =
        prec->isFilePrecompiled(compiler->getPpOutputFileId())
            ? 0
            : clp->getMaxTreads();

    const int32_t effectiveNbThreads = calculateEffectiveThreads(nbThreads);

    AnalyzeFile* const fileAnalyzer = new AnalyzeFile(
        compiler->getSession(), m_design, compiler->getPpOutputFileId(),
        compiler->getFileId(), effectiveNbThreads, m_text);
    fileAnalyzer->analyze();
    compiler->setFileAnalyzer(fileAnalyzer);
    if (fileAnalyzer->getSplitFiles().size() > 1) {
      // Schedule parent
      m_compilersParentFiles.emplace_back(compiler);
      compiler->initParser();

      SymbolTable* symbols = m_session->getSymbolTable();
      if (!clp->fileUnit()) {
        symbols = symbols->CreateSnapshot();
      }

      Session* const session = new Session(
          m_session->getFileSystem(), symbols, m_session->getLogListener(),
          nullptr, m_session->getCommandLineParser(), nullptr);
      m_sessions.emplace_back(session);
      compiler->getParser()->setFileContent(new FileContent(
          session, compiler->getParser()->getFileId(0),
          compiler->getParser()->getLibrary(), nullptr, BadPathId));

      int32_t j = 0;
      for (const auto& ppId : fileAnalyzer->getSplitFiles()) {
        SymbolTable* symbols = m_session->getSymbolTable()->CreateSnapshot();
        Session* const session = new Session(
            m_session->getFileSystem(), symbols, m_session->getLogListener(),
            nullptr, m_session->getCommandLineParser(), nullptr);
        m_sessions.emplace_back(session);
        CompileSourceFile* chunkCompiler = new CompileSourceFile(
            session, compiler, ppId, fileAnalyzer->getLineOffsets()[j]);
        // Schedule chunk
        tmp_compilers.emplace_back(chunkCompiler);

        FileContent* const chunkFileContent =
            new FileContent(session, compiler->getParser()->getFileId(0),
                            compiler->getParser()->getLibrary(), nullptr, ppId);
        chunkCompiler->getParser()->setFileContent(chunkFileContent);
        getDesign()->addFileContent(compiler->getParser()->getFileId(0),
                                    chunkFileContent);

        j++;
      }
    } else {
      if ((!clp->fileUnit()) && m_text.empty()) {
        SymbolTable* symbols = m_session->getSymbolTable()->CreateSnapshot();

        Session* const session = new Session(
            m_session->getFileSystem(), symbols, m_session->getLogListener(),
            nullptr, m_session->getCommandLineParser(), nullptr);
        m_sessions.emplace_back(session);

        compiler->setSession(session);
      }

      tmp_compilers.emplace_back(compiler);
    }
  }
  m_compilers = std::move(tmp_compilers);

  return true;
}

bool Compiler::pythoninit_() { return parseinit_(); }

ErrorContainer::Stats Compiler::getErrorStats() const {
  std::set<ErrorContainer*> unique;
  ErrorContainer::Stats stats;
  for (const auto& s : m_sessions) {
    if (unique.emplace(s->getErrorContainer()).second) {
      stats += s->getErrorContainer()->getErrorStats();
    }
  }

  return stats;
}

bool Compiler::cleanup_() {
  DeleteSequenceContainerPointersAndClear(&m_compilers);
  DeleteSequenceContainerPointersAndClear(&m_compilationUnits);
  DeleteSequenceContainerPointersAndClear(&m_sessions);
  return true;
}

bool Compiler::compileFileSet_(CompileSourceFile::Action action,
                               bool allowMultithread,
                               std::vector<CompileSourceFile*>& container) {
  ErrorContainer* const errors = m_session->getErrorContainer();
  CommandLineParser* const clp = m_session->getCommandLineParser();
  const uint16_t maxThreadCount = allowMultithread ? clp->getMaxTreads() : 0;

  if (maxThreadCount < 1) {
    // Single thread
    for (CompileSourceFile* const source : container) {
#ifdef SURELOG_WITH_PYTHON
      source->setPythonInterp(PythonAPI::getMainInterp());
#endif
      bool status = compileOneFile_(source, action);
      Session* const sourceSession = source->getSession();
      ErrorContainer* const sourceErrors = sourceSession->getErrorContainer();

      errors->appendErrors(*sourceErrors);
      errors->printMessages(clp->muteStdout());
      if ((!status) || sourceErrors->hasFatalErrors()) {
        return false;
      }
    }
  } else if (clp->useTbb() && (action != CompileSourceFile::Action::Parse)) {
#ifdef USETBB
    // TBB Thread management
    if (maxThreadCount) {
      for (CompileSourceFile* const source : container) {
        m_taskGroup.run(FunctorCompileOneFile(source, action));
      }
      m_taskGroup.wait();
      bool fatalErrors = false;
      for (CompileSourceFile* const source : container) {
        // Promote report to master error container
        m_errors->appendErrors(*source->getErrorContainer());
        if (source->getErrorContainer()->hasFatalErrors()) {
          fatalErrors = true;
        }
        if (m_session->pythonListener()) {
          source->shutdownPythonInterp();
        }
        m_errors->printMessages(m_session->muteStdout());
      }
      if (fatalErrors) return false;
    } else {
      for (CompileSourceFile* const source : container) {
        source->setPythonInterp(PythonAPI::getMainInterp());
        bool status = compileOneFile_(source, action);
        m_errors->appendErrors(*souirce->getErrorContainer());
        m_errors->printMessages(m_session->muteStdout());
        if ((!status) || source->getErrorContainer()->hasFatalErrors())
          return false;
      }
    }
#endif
  } else {
    // Custom Thread management

    // Optimize the load balance, try to even out the work in each thread by the
    // size of the files
    std::vector<std::vector<CompileSourceFile*>> jobArray(maxThreadCount);
    std::vector<uint64_t> jobSize(maxThreadCount, 0);

    for (CompileSourceFile* const source : container) {
      const uint32_t size = source->getJobSize(action);
      uint32_t newJobIndex = 0;
      uint64_t minJobQueue = ULLONG_MAX;
      for (uint16_t ii = 0; ii < maxThreadCount; ii++) {
        if (jobSize[ii] < minJobQueue) {
          newJobIndex = ii;
          minJobQueue = jobSize[ii];
        }
      }

      jobSize[newJobIndex] += size;
      jobArray[newJobIndex].emplace_back(source);
    }

    if (clp->profile()) {
      if (action == CompileSourceFile::Action::Preprocess)
        std::cout << "Preprocessing task" << std::endl;
      else if (action == CompileSourceFile::Action::Parse)
        std::cout << "Parsing task" << std::endl;
      else
        std::cout << "Misc Task" << std::endl;
      for (uint16_t i = 0; i < maxThreadCount; i++) {
        std::cout << "Thread " << i << " : " << std::endl;
        int32_t sum = 0;
        for (CompileSourceFile* job : jobArray[i]) {
          Session* const jobSession = job->getSession();
          FileSystem* const jobFileSystem = jobSession->getFileSystem();
          PathId fileId;
          if (job->getPreprocessor())
            fileId = job->getPreprocessor()->getFileId(0);
          else if (job->getParser())
            fileId = job->getParser()->getFileId(0);
          sum += job->getJobSize(action);
          std::cout << job->getJobSize(action) << " "
                    << jobFileSystem->toPath(fileId) << std::endl;
        }
        std::cout << ", Total: " << sum << std::endl << std::flush;
      }
    }

    // Create the threads with their respective workloads
    std::vector<std::thread*> threads;
    for (uint16_t i = 0; i < maxThreadCount; i++) {
      std::thread* th = new std::thread([=] {
        for (CompileSourceFile* job : jobArray[i]) {
#ifdef SURELOG_WITH_PYTHON
          if (m_session->pythonListener() ||
              m_session->pythonEvalScriptPerFile()) {
            PyThreadState* interpState = PythonAPI::initNewInterp();
            job->setPythonInterp(interpState);
          }
#endif
          job->compile(action);
#ifdef SURELOG_WITH_PYTHON
          if (m_session->pythonListener() ||
              m_session->pythonEvalScriptPerFile()) {
            job->shutdownPythonInterp();
          }
#endif
        }
      });
      threads.emplace_back(th);
    }

    // Wait for all of them to finish
    for (auto& t : threads) {
      t->join();
    }

    // Delete the threads
    DeleteSequenceContainerPointersAndClear(&threads);

    // Promote report to master error container
    bool fatalErrors = false;
    for (CompileSourceFile* const source : container) {
      Session* const sourceSession = source->getSession();
      errors->appendErrors(*sourceSession->getErrorContainer());
      if (sourceSession->getErrorContainer()->hasFatalErrors()) {
        fatalErrors = true;
      }
    }
    errors->printMessages(clp->muteStdout());

    if (fatalErrors) return false;
  }
  return true;
}

void Compiler::writeUhdmSourceFiles() {
  uhdm::Design* const design = m_design->getUhdmDesign();

  std::map<const MacroInfo*, uhdm::PreprocMacroDefinition*> defMap;
  std::map<uhdm::PreprocMacroInstance*, const MacroInfo*> instanceMap;
  uhdm::SourceFileCollection* const sourcefiles = design->getSourceFiles(true);
  for (CompileSourceFile* sourceFile : m_compilers) {
    const PreprocessFile* const preprocessFile = sourceFile->getPreprocessor();
    const ParseFile* const parseFile = sourceFile->getParser();
    const FileContent* const fileContent = parseFile->getFileContent();
    Session* const session = sourceFile->getSession();
    FileSystem* const fileSystem = session->getFileSystem();
    SymbolTable* const symbolTable = session->getSymbolTable();
    const std::vector<VObject>& objects = fileContent->getVObjects();

    // TODO(HS): Macro definitions should include arguments & tokens
    // TODO(HS): Macro instances should include arguments & compiled text
    // TODO(HS): Macro definition should know all its use cases.

    std::vector<uhdm::SourceFile*> sourceFileStack;
    std::vector<uhdm::PreprocMacroInstance*> macroInstanceStack;
    std::vector<uhdm::PreprocMacroInstance*>& macroInstances =
        sourceFile->getPreprocMacroInstances();
    macroInstances.resize(objects.size(), nullptr);

    const std::vector<IncludeFileInfo>& includeFileInfos =
        preprocessFile->getIncludeFileInfo();
    for (const IncludeFileInfo& ifi : includeFileInfos) {
      if (ifi.m_context == IncludeFileInfo::Context::Include) {
        if (ifi.m_action == IncludeFileInfo::Action::Push) {
          const IncludeFileInfo& oifi = ifi;
          const IncludeFileInfo& cifi = includeFileInfos[oifi.m_indexOpposite];

          uhdm::SourceFile* const incl = m_serializer.make<uhdm::SourceFile>();
          incl->setName(symbolTable->getSymbol(oifi.m_symbolId));
          incl->setFile(fileSystem->toPath(oifi.m_sectionFileId));
          incl->setStartLine(oifi.m_symbolLine);
          incl->setStartColumn(oifi.m_symbolColumn);
          incl->setEndLine(cifi.m_symbolLine);
          incl->setEndColumn(cifi.m_symbolColumn);
          if (sourceFileStack.empty()) {
            incl->setParent(design);
            sourcefiles->emplace_back(incl);
          } else {
            incl->setParent(sourceFileStack.back());
            sourceFileStack.back()->getIncludes(true)->emplace_back(incl);
          }
          sourceFileStack.emplace_back(incl);

          for (MacroInfo* mi : oifi.m_macroDefinitions) {
            uhdm::PreprocMacroDefinition* const pmd =
                m_serializer.make<uhdm::PreprocMacroDefinition>();
            pmd->setName(mi->m_name);
            pmd->setParent(incl);
            pmd->setFile(fileSystem->toPath(mi->m_fileId));
            pmd->setStartLine(mi->m_startLine);
            pmd->setStartColumn(mi->m_startColumn);
            pmd->setEndLine(mi->m_endLine);
            pmd->setEndColumn(mi->m_endColumn);
            pmd->setNameStartColumn(mi->m_nameStartColumn);
            pmd->setBodyStartColumn(mi->m_bodyStartColumn);
            incl->getPreprocMacroDefinitions(true)->emplace_back(pmd);
            defMap.emplace(mi, pmd);
          }
        } else if (ifi.m_action == IncludeFileInfo::Action::Pop) {
          sourceFileStack.pop_back();
        }
      } else if (ifi.m_context == IncludeFileInfo::Context::Macro) {
        if (ifi.m_action == IncludeFileInfo::Action::Push) {
          const IncludeFileInfo& oifi = ifi;
          const IncludeFileInfo& cifi = includeFileInfos[oifi.m_indexOpposite];

          uhdm::PreprocMacroInstance* const pmi =
              m_serializer.make<uhdm::PreprocMacroInstance>();
          pmi->setName(oifi.m_macroDefinition->m_name);
          pmi->setFile(fileSystem->toPath(oifi.m_sectionFileId));
          pmi->setStartLine(oifi.m_symbolLine);
          pmi->setStartColumn(oifi.m_symbolColumn);
          pmi->setEndLine(cifi.m_symbolLine);
          pmi->setEndColumn(cifi.m_symbolColumn);
          pmi->setSectionStartLine(oifi.m_sectionLine);
          pmi->setSectionStartColumn(oifi.m_sectionColumn);
          pmi->setSectionEndLine(cifi.m_sectionLine);
          pmi->setSectionEndColumn(cifi.m_sectionColumn);
          pmi->setSourceStartLine(oifi.m_sourceLine);
          pmi->setSourceStartColumn(oifi.m_sourceColumn);
          pmi->setSourceEndLine(cifi.m_sourceLine);
          pmi->setSourceEndColumn(cifi.m_sourceColumn);
          if (macroInstanceStack.empty()) {
            pmi->setParent(sourceFileStack.back());
            sourceFileStack.back()
                ->getPreprocMacroInstances(true)
                ->emplace_back(pmi);
          } else {
            pmi->setParent(macroInstanceStack.back());
            macroInstanceStack.back()
                ->getPreprocMacroInstances(true)
                ->emplace_back(pmi);
          }
          macroInstanceStack.emplace_back(pmi);
          instanceMap.emplace(pmi, oifi.m_macroDefinition);
        } else if (ifi.m_action == IncludeFileInfo::Action::Pop) {
          const IncludeFileInfo& cifi = ifi;
          const IncludeFileInfo& oifi = includeFileInfos[cifi.m_indexOpposite];

          for (size_t i = 0, ni = objects.size(); i < ni; ++i) {
            const VObject& object = objects[i];
            if (object.m_ppStartLine < oifi.m_sourceLine) continue;
            if (object.m_ppEndLine > cifi.m_sourceLine) break;
            if (macroInstances[i] != nullptr) continue;

            if ((object.m_ppStartLine == oifi.m_sourceLine) &&
                (object.m_ppEndLine == cifi.m_sourceLine)) {
              if ((object.m_ppStartColumn >= oifi.m_sourceColumn) &&
                  (object.m_ppEndColumn <= cifi.m_sourceColumn)) {
                macroInstances[i] = macroInstanceStack.back();
              }
            } else if (object.m_ppStartLine == oifi.m_sourceLine) {
              if (object.m_ppStartColumn >= oifi.m_sourceColumn) {
                macroInstances[i] = macroInstanceStack.back();
              }
            } else if (object.m_ppEndLine == cifi.m_sourceLine) {
              if (object.m_ppEndColumn <= cifi.m_sourceColumn) {
                macroInstances[i] = macroInstanceStack.back();
              }
            } else {
              macroInstances[i] = macroInstanceStack.back();
            }
          }
          macroInstanceStack.pop_back();
        }
      }
    }
  }

  for (const auto& [pmi, mi] : instanceMap) {
    if (auto it = defMap.find(mi); it != defMap.cend()) {
      pmi->setPreprocMacroDefinition(it->second);
    }
  }
}

void Compiler::writePreprocMacroInstances() {
  const uhdm::Serializer::IdMap anys = m_serializer.getAllObjects();
  std::set<uhdm::PreprocMacroInstance*> allPpMIs;

  for (CompileSourceFile* sourceFile : m_compilers) {
    const ParseFile* const parseFile = sourceFile->getParser();
    const FileContent* const fileContent = parseFile->getFileContent();
    Session* const session = sourceFile->getSession();
    FileSystem* const fileSystem = session->getFileSystem();
    const std::vector<VObject>& objects = fileContent->getVObjects();
    const FileContent::AnyToNodeIdPairCache& anyToNodeIdPairCache =
        fileContent->getAnyToNodeIdPairCache();
    std::vector<uhdm::PreprocMacroInstance*>& pmis =
        sourceFile->getPreprocMacroInstances();

    for (const auto& [any, id] : anys) {
      if (any->getFile() != fileSystem->toPath(sourceFile->getFileId()))
        continue;

      FileContent::AnyToNodeIdPairCache::const_iterator it =
          anyToNodeIdPairCache.find(any);
      // TODO(hs): No cache entry! Based on the parent of this any
      // try and walk the objects tree to find an appropriate
      // start/end index. Make sure to use ppStart/ppEnd and not
      // start/end of the object.
      if (it == anyToNodeIdPairCache.end()) continue;

      const NodeId& startIndex = it->second.first;
      const NodeId& endIndex = it->second.second;

      if (startIndex && (pmis[startIndex] != nullptr)) {
        const VObject& object = objects[startIndex];
        if ((object.m_startLine == any->getStartLine()) &&
            (object.m_startColumn == any->getStartColumn())) {
          pmis[startIndex]->getObjects(true)->emplace_back(
              const_cast<uhdm::Any*>(any));
          allPpMIs.emplace(pmis[startIndex]);
        }
      }

      if (endIndex && (pmis[endIndex] != nullptr)) {
        const VObject& object = objects[startIndex];
        if ((object.m_endLine == any->getEndLine()) &&
            (object.m_endColumn == any->getEndColumn())) {
          pmis[endIndex]->getObjects(true)->emplace_back(
              const_cast<uhdm::Any*>(any));
          allPpMIs.emplace(pmis[endIndex]);
        }
      }
    }
  }

  for (uhdm::PreprocMacroInstance* pmi : allPpMIs) {
    if (uhdm::AnyCollection* const objects = pmi->getObjects()) {
      std::sort(objects->begin(), objects->end(),
                [](const uhdm::Any* const lhs, const uhdm::Any* const rhs) {
                  return lhs->getUhdmId() < rhs->getUhdmId();
                });
      objects->erase(std::unique(objects->begin(), objects->end()),
                     objects->end());
    }
  }
}

bool Compiler::compile() {
  std::string profile;
  Timer tmr;
  Timer tmrTotal;
  // Scan the libraries definition
  if (!parseLibrariesDef_()) return false;

  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errors = m_session->getErrorContainer();
  CommandLineParser* const clp = m_session->getCommandLineParser();
  if (clp->profile()) {
    std::string msg = "Scan libraries took " +
                      StringUtils::to_string(tmr.elapsed_rounded()) + "s\n";
    std::cout << msg << std::endl;
    profile += msg;
    tmr.reset();
  }

  // Preprocess
  ppinit_();
  createMultiProcessPreProcessor_();
  if (!compileFileSet_(CompileSourceFile::Action::Preprocess, clp->fileUnit(),
                       m_compilers)) {
    return false;
  }
  // Single thread post Preprocess
  if (!compileFileSet_(CompileSourceFile::Action::PostPreprocess, false,
                       m_compilers)) {
    return false;
  }

  if (clp->profile()) {
    std::string msg = "Preprocessing took " +
                      StringUtils::to_string(tmr.elapsed_rounded()) + "s\n";
    std::cout << msg << std::endl;
    for (const CompileSourceFile* compiler : m_compilers) {
      msg += compiler->getPreprocessor()->getProfileInfo();
    }
    std::cout << msg << std::endl;
    profile += msg;
    tmr.reset();
  }

  // Parse
  bool parserInitialized = false;
  if (clp->parse() || clp->pythonListener() || clp->pythonEvalScriptPerFile() ||
      clp->pythonEvalScript()) {
    parseinit_();
    createFileList_();
    createMultiProcessParser_();
    parserInitialized = true;
    if (!compileFileSet_(CompileSourceFile::Action::Parse, true, m_compilers)) {
      return false;  // Small files and large file chunks
    }
    if (!compileFileSet_(CompileSourceFile::Action::Parse, true,
                         m_compilersParentFiles)) {
      return false;  // Recombine chunks
    }
  } else {
    createFileList_();
  }

  // writeUhdmSourceFiles();

  if (clp->profile()) {
    std::string msg =
        "Parsing took " + StringUtils::to_string(tmr.elapsed_rounded()) + "s\n";
    for (const CompileSourceFile* compilerParent : m_compilersParentFiles) {
      msg += compilerParent->getParser()->getProfileInfo();
    }
    for (const CompileSourceFile* compiler : m_compilers) {
      msg += compiler->getParser()->getProfileInfo();
    }

    std::cout << msg << std::endl;
    profile += msg;
    tmr.reset();
  }

  // Check Parsing
  CheckCompile* checkComp = new CheckCompile(m_session, this);
  bool parseOk = checkComp->check();
  delete checkComp;
  errors->printMessages(clp->muteStdout());

  // Python Listener
  if (parseOk && (clp->pythonListener() || clp->pythonEvalScriptPerFile())) {
    if (!parserInitialized) pythoninit_();
    if (!compileFileSet_(CompileSourceFile::Action::PythonAPI, true, m_compilers))
      return false;
    if (!compileFileSet_(CompileSourceFile::Action::PythonAPI, true,
                         m_compilersParentFiles))
      return false;

    if (clp->profile()) {
      std::string msg = "Python file processing took " +
                        StringUtils::to_string(tmr.elapsed_rounded()) + "s\n";
      std::cout << msg << std::endl;
      profile += msg;
      tmr.reset();
    }
  }

  if (parseOk && clp->compile()) {
    // Compile Design, has its own thread management
    m_compileDesign = new CompileDesign(m_session, this);
    m_compileDesign->compile();
    errors->printMessages(clp->muteStdout());

    if (clp->profile()) {
      std::string msg = "Compilation took " +
                        StringUtils::to_string(tmr.elapsed_rounded()) + "s\n";
      std::cout << msg << std::endl;
      profile += msg;
      tmr.reset();
    }

    // writePreprocMacroInstances();
    m_compileDesign->purgeParsers();

    if (clp->elaborate()) {
      m_compileDesign->elaborate();
      errors->printMessages(clp->muteStdout());

      if (clp->profile()) {
        std::string msg = "Elaboration took " +
                          StringUtils::to_string(tmr.elapsed_rounded()) + "s\n";
        std::cout << msg << std::endl;
        profile += msg;
        tmr.reset();
      }

      if (clp->pythonEvalScript()) {
        PythonAPI::evalScript(fileSystem->toPath(clp->pythonEvalScriptId()),
                              m_design);
        if (clp->profile()) {
          std::string msg = "Python design processing took " +
                            StringUtils::to_string(tmr.elapsed_rounded()) +
                            "s\n";
          profile += msg;
          std::cout << msg << std::endl;
          tmr.reset();
        }
      }
      errors->printMessages(clp->muteStdout());
    }

    PathId uhdmFileId = fileSystem->getOutputUhdmFile(clp->fileUnit(), symbols);
    m_compileDesign->writeUHDM(uhdmFileId);
    // Do not delete as now UHDM has to live past the compilation step
    // delete compileDesign;
  }
  if (clp->profile()) {
    std::string msg = "Total time " +
                      StringUtils::to_string(tmrTotal.elapsed_rounded()) +
                      "s\n";
    profile += msg;
    profile = std::string("==============\n") + "PROFILE\n" +
              std::string("==============\n") + profile + "==============\n";
    std::cout << profile << std::endl;
    errors->printToLogFile(profile);
  }
  return true;
}

void Compiler::registerAntlrPpHandlerForId(
    SymbolId id, PreprocessFile::AntlrParserHandler* pp) {
  std::map<SymbolId, PreprocessFile::AntlrParserHandler*>::iterator itr =
      m_antlrPpMap.find(id);
  if (itr != m_antlrPpMap.end()) {
    delete (*itr).second;
    m_antlrPpMap.erase(itr);
    m_antlrPpMap.emplace(id, pp);
    return;
  }
  m_antlrPpMap.emplace(id, pp);
}

PreprocessFile::AntlrParserHandler* Compiler::getAntlrPpHandlerForId(
    SymbolId id) {
  std::map<SymbolId, PreprocessFile::AntlrParserHandler*>::iterator itr =
      m_antlrPpMap.find(id);
  if (itr != m_antlrPpMap.end()) {
    PreprocessFile::AntlrParserHandler* ptr = (*itr).second;
    return ptr;
  }
  return nullptr;
}

bool Compiler::parseLibrariesDef_() {
  ParseLibraryDef* libParser =
      new ParseLibraryDef(m_session, m_librarySet, m_configSet);
  bool result = libParser->parseLibrariesDefinition();
  delete libParser;
  return result;
}

uhdm::Design* Compiler::getUhdmDesign() const {
  return m_design->getUhdmDesign();
}

vpiHandle Compiler::getVpiDesign() const {
  uhdm::Design* const uhdmDesign = m_design->getUhdmDesign();
  return (uhdmDesign != nullptr) ? uhdmDesign->getSerializer()->makeUhdmHandle(
                                       uhdmDesign->getUhdmType(), uhdmDesign)
                                 : nullptr;
}
}  // namespace SURELOG
