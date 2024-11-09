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

#include <climits>
#include <filesystem>
#include <fstream>
#include <nlohmann/json.hpp>
#include <thread>

#include "Surelog/API/PythonAPI.h"
#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
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
#include "Surelog/Utils/ContainerUtils.h"
#include "Surelog/Utils/StringUtils.h"
#include "Surelog/Utils/Timer.h"

#if defined(_MSC_VER)
#include <direct.h>
#else
#include <unistd.h>
#endif

namespace SURELOG {

namespace fs = std::filesystem;

Compiler::Compiler(CommandLineParser* commandLineParser, ErrorContainer* errors,
                   SymbolTable* symbolTable)
    : m_commandLineParser(commandLineParser),
      m_errors(errors),
      m_symbolTable(symbolTable),
      m_commonCompilationUnit(nullptr),
      m_librarySet(new LibrarySet()),
      m_configSet(new ConfigSet()),
      m_design(new Design(getErrorContainer(), m_librarySet, m_configSet)),
      m_uhdmDesign(0),
      m_compileDesign(nullptr) {
#ifdef USETBB
  if (getCommandLineParser()->useTbb() &&
      (getCommandLineParser()->getNbMaxTreads() > 0))
    tbb::task_scheduler_init init(getCommandLineParser()->getNbMaxTreads());
#endif
}

Compiler::Compiler(CommandLineParser* commandLineParser, ErrorContainer* errors,
                   SymbolTable* symbolTable, std::string_view text)
    : m_commandLineParser(commandLineParser),
      m_errors(errors),
      m_symbolTable(symbolTable),
      m_commonCompilationUnit(nullptr),
      m_librarySet(new LibrarySet()),
      m_configSet(new ConfigSet()),
      m_design(new Design(getErrorContainer(), m_librarySet, m_configSet)),
      m_uhdmDesign(0),
      m_text(text),
      m_compileDesign(nullptr) {}

Compiler::~Compiler() {
  for (auto& entry : m_antlrPpMap) {
    delete entry.second;
  }

  m_antlrPpMap.clear();
  delete m_design;
  delete m_configSet;
  delete m_librarySet;
  delete m_commonCompilationUnit;

  cleanup_();
}

void Compiler::purgeParsers() {
  for (auto& entry : m_antlrPpMap) {
    delete entry.second;
  }

  m_antlrPpMap.clear();
  DeleteContainerPointersAndClear(&m_compilers);
}

struct FunctorCompileOneFile {
  FunctorCompileOneFile(CompileSourceFile* compileSource,
                        CompileSourceFile::Action action)
      : m_compileSourceFile(compileSource), m_action(action) {}

  int32_t operator()() const {
#ifdef SURELOG_WITH_PYTHON
    if (m_compileSourceFile->getCommandLineParser()->pythonListener() ||
        m_compileSourceFile->getCommandLineParser()
            ->pythonEvalScriptPerFile()) {
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
  FileSystem* const fileSystem = FileSystem::getInstance();
  if (!m_commandLineParser->fileunit()) {
    m_commonCompilationUnit = new CompilationUnit(false);
    if (m_commandLineParser->parseBuiltIn()) {
      Builtin* builtin = new Builtin(nullptr, nullptr);
      builtin->addBuiltinMacros(m_commonCompilationUnit);
    }
  }

  CompilationUnit* comp_unit = m_commonCompilationUnit;

  // Source files (.v, .sv on the command line)
  PathIdSet sourceFiles;
  for (const PathId& sourceFileId : m_commandLineParser->getSourceFiles()) {
    SymbolTable* symbols = m_symbolTable;
    if (m_commandLineParser->fileunit()) {
      comp_unit = new CompilationUnit(true);
      if (m_commandLineParser->parseBuiltIn()) {
        Builtin* builtin = new Builtin(nullptr, nullptr);
        builtin->addBuiltinMacros(comp_unit);
      }
      m_compilationUnits.push_back(comp_unit);
      symbols = m_commandLineParser->getSymbolTable()->CreateSnapshot();
      m_symbolTables.push_back(symbols);
    }
    ErrorContainer* errors =
        new ErrorContainer(symbols, m_errors->getLogListener());
    m_errorContainers.push_back(errors);
    errors->registerCmdLine(m_commandLineParser);

    Library* library = m_librarySet->getLibrary(sourceFileId);
    sourceFiles.insert(sourceFileId);

    CompileSourceFile* compiler =
        new CompileSourceFile(sourceFileId, m_commandLineParser, errors, this,
                              symbols, comp_unit, library);
    m_compilers.push_back(compiler);
  }

  if (!m_text.empty()) {
    Library* library = new Library("UnitTest", m_symbolTable);
    CompileSourceFile* compiler =
        new CompileSourceFile(BadPathId, m_commandLineParser, m_errors, this,
                              m_symbolTable, comp_unit, library, m_text);
    m_compilers.push_back(compiler);
  }

  // Library files
  PathIdSet libFileIdSet;
  // (-v <file>)
  const auto& libFiles = m_commandLineParser->getLibraryFiles();
  std::copy_if(libFiles.begin(), libFiles.end(),
               std::inserter(libFileIdSet, libFileIdSet.end()),
               [&sourceFiles](const PathId& libFileId) {
                 return sourceFiles.find(libFileId) == sourceFiles.end();
               });

  // (-y <path> +libext+<ext>)
  for (const PathId& libFileId : m_commandLineParser->getLibraryPaths()) {
    for (const SymbolId& ext : m_commandLineParser->getLibraryExtensions()) {
      PathIdVector fileIds;
      fileSystem->collect(libFileId,
                          m_commandLineParser->getSymbolTable()->getSymbol(ext),
                          m_commandLineParser->getSymbolTable(), fileIds);
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
    SymbolTable* symbols = m_symbolTable;
    if (m_commandLineParser->fileunit()) {
      comp_unit = new CompilationUnit(true);
      m_compilationUnits.push_back(comp_unit);
      symbols = m_commandLineParser->getSymbolTable()->CreateSnapshot();
      m_symbolTables.push_back(symbols);
    }
    ErrorContainer* errors =
        new ErrorContainer(symbols, m_errors->getLogListener());
    m_errorContainers.push_back(errors);
    errors->registerCmdLine(m_commandLineParser);

    // This line registers the file in the "work" library:
    /*Library* library  = */ m_librarySet->getLibrary(libFileId);
    m_libraryFiles.insert(libFileId);
    // No need to register a compiler
    // CompileSourceFile* compiler = new CompileSourceFile
    // (m_commandLineParser->getLibraryFiles ()[i],
    //                                                     m_commandLineParser,
    //                                                     errors, this,
    //                                                     symbols, comp_unit,
    //                                                     library);
    // m_compilers.push_back (compiler);
  }

  // Libraries (.map)
  for (auto& lib : m_librarySet->getLibraries()) {
    for (const PathId& id : lib.getFiles()) {
      if (sourceFiles.find(id) != sourceFiles.end()) {
        // These files are already included in the command line
        continue;
      }

      std::string_view type =
          std::get<1>(fileSystem->getType(id, lib.getSymbols()));
      if (type == ".map") {
        // .map files are not parsed with the regular parser
        continue;
      }
      SymbolTable* symbols = m_symbolTable;
      if (m_commandLineParser->fileunit()) {
        comp_unit = new CompilationUnit(true);
        m_compilationUnits.push_back(comp_unit);
        symbols = m_commandLineParser->getSymbolTable()->CreateSnapshot();
        m_symbolTables.push_back(symbols);
      }
      ErrorContainer* errors =
          new ErrorContainer(symbols, m_errors->getLogListener());
      m_errorContainers.push_back(errors);
      errors->registerCmdLine(m_commandLineParser);

      CompileSourceFile* compiler = new CompileSourceFile(
          id, m_commandLineParser, errors, this, symbols, comp_unit, &lib);
      m_compilers.push_back(compiler);
    }
  }
  return true;
}

bool Compiler::createFileList_() {
  if (!((m_commandLineParser->writePpOutput() ||
         m_commandLineParser->writePpOutputFileId()) &&
        (!m_commandLineParser->parseOnly()))) {
    return true;
  }
  FileSystem* const fileSystem = FileSystem::getInstance();
  SymbolTable* symbolTable = getSymbolTable();
  {
    PathId fileId = fileSystem->getChild(m_commandLineParser->getCompileDirId(),
                                         "file.lst", symbolTable);
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
      std::cerr << "Could not create filelist: " << PathIdPP(fileId)
                << std::endl;
    }
  }
  {
    PathId fileId = fileSystem->getChild(m_commandLineParser->getCompileDirId(),
                                         "file_map.lst",
                                         m_commandLineParser->getSymbolTable());
    std::ostream& ofs = fileSystem->openForWrite(fileId);
    if (ofs.good()) {
      for (CompileSourceFile* sourceFile : m_compilers) {
        ofs << fileSystem->toPath(sourceFile->getPpOutputFileId()) << " "
            << fileSystem->toPath(sourceFile->getFileId()) << std::endl;
      }
      ofs.flush();
      fileSystem->close(ofs);
    } else {
      std::cerr << "Could not create filelist: " << PathIdPP(fileId)
                << std::endl;
    }
  }
  {
    if (m_commandLineParser->sepComp()) {
      std::ostringstream concatFiles;
      for (CompileSourceFile* sourceFile : m_compilers) {
        const PathId sourceFileId = sourceFile->getFileId();
        concatFiles << fileSystem->toPath(sourceFileId) << "|";
      }
      std::size_t val = std::hash<std::string>{}(concatFiles.str());
      {
        std::string hashedName = std::to_string(val) + ".sep_lst";
        PathId fileId = fileSystem->getChild(
            m_commandLineParser->getCompileDirId(), hashedName,
            m_commandLineParser->getSymbolTable());
        std::ostream& ofs = fileSystem->openForWrite(fileId);
        if (ofs.good()) {
          for (CompileSourceFile* sourceFile : m_compilers) {
            ofs << fileSystem->toPath(sourceFile->getFileId()) << " ";
          }
          fileSystem->close(ofs);
        } else {
          std::cerr << "Could not create filelist: " << PathIdPP(fileId)
                    << std::endl;
        }
      }
      {
        std::string hashedName = std::to_string(val) + ".sepcmd.json";
        PathId fileId = fileSystem->getChild(
            m_commandLineParser->getCompileDirId(), hashedName,
            m_commandLineParser->getSymbolTable());
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
          std::cerr << "Could not create filelist: " << PathIdPP(fileId)
                    << std::endl;
        }
      }
    }
  }
  return true;
}

bool Compiler::createMultiProcessParser_() {
  uint32_t nbProcesses = m_commandLineParser->getNbMaxProcesses();
  if (nbProcesses == 0) return true;

  if (!(m_commandLineParser->writePpOutput() ||
        m_commandLineParser->writePpOutputFileId())) {
    return true;
  }

  FileSystem* const fileSystem = FileSystem::getInstance();
  SymbolTable* symbolTable = getSymbolTable();

  // Create CMakeLists.txt
  const bool muted = m_commandLineParser->muteStdout();
  const fs::path outputDir =
      fileSystem->toPlatformAbsPath(m_commandLineParser->getOutputDirId());
  const fs::path programPath =
      fileSystem->toPlatformAbsPath(m_commandLineParser->getProgramId());
  const std::string_view profile =
      m_commandLineParser->profile() ? " -profile " : " ";
  const std::string_view sverilog =
      m_commandLineParser->fullSVMode() ? " -sverilog " : " ";
  const std::string_view fileUnit =
      m_commandLineParser->fileunit() ? " -fileunit " : " ";
  std::string synth =
      m_commandLineParser->reportNonSynthesizable() ? " -synth " : " ";
  synth += m_commandLineParser->reportNonSynthesizableWithFormal() ? " -formal "
                                                                   : " ";
  const std::string_view noHash =
      m_commandLineParser->noCacheHash() ? " -nohash " : " ";

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
  Precompiled* prec = Precompiled::getSingleton();

  const fs::path workingDir = fileSystem->getWorkingDir();
  for (const auto& compiler : m_compilers) {
    if (prec->isFilePrecompiled(compiler->getFileId(),
                                compiler->getSymbolTable())) {
      continue;
    }
    uint32_t size = compiler->getJobSize(CompileSourceFile::Action::Parse);
    if (size > bigJobThreashold) {
      bigJobs.push_back(compiler);
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
    jobArray[newJobIndex].push_back(compiler);
  }

  std::vector<std::string> batchProcessCommands;
  std::vector<std::string> targets;
  int32_t absoluteIndex = 0;

  // Big jobs
  for (CompileSourceFile* compiler : bigJobs) {
    absoluteIndex++;
    std::string targetname =
        StrCat(absoluteIndex, "_",
               std::get<1>(fileSystem->getLeaf(compiler->getPpOutputFileId(),
                                               compiler->getSymbolTable())));
    std::string_view svFile =
        m_commandLineParser->isSVFile(compiler->getFileId()) ? " -sv " : " ";
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
      fs::path fileName =
          fileSystem->toPlatformAbsPath(compiler->getPpOutputFileId());
      std::string_view svFile =
          m_commandLineParser->isSVFile(compiler->getFileId()) ? " -sv " : " ";
      StrAppend(&fileList, svFile, fileName);
    }
    if (!fileList.empty()) {
      std::string targetname =
          StrCat(std::to_string(absoluteIndex), "_",
                 std::get<1>(fileSystem->getLeaf(
                     jobArray[i].back()->getPpOutputFileId(),
                     jobArray[i].back()->getSymbolTable())));

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

  const PathId dirId = fileSystem->getPpMultiprocessingDir(
      m_commandLineParser->fileunit(), symbolTable);
  fileSystem->mkdirs(dirId);

  if (nbProcesses == 1) {
    // Single child process
    const PathId fileId =
        fileSystem->getChild(dirId, "parser_batch.txt", symbolTable);
    if (!fileSystem->writeLines(fileId, batchProcessCommands)) {
      std::cerr << "FATAL: Could not create file: " << PathIdPP(fileId)
                << std::endl;
      return false;
    }

    const std::string command =
        StrCat("cd ", workingDir, "; ", programPath, " -o ", outputDir,
               " -nostdout -batch ", fileSystem->toPath(fileId));
    if (!muted) std::cout << "Running: " << command << std::endl << std::flush;
    int32_t result = system(command.c_str());
    if (!muted) std::cout << "Surelog parsing status: " << result << std::endl;
    if (!result) return false;
  } else {
    // Multiple child processes managed by cmake
    const PathId fileId =
        fileSystem->getChild(dirId, "CMakeLists.txt", symbolTable);
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
      std::cerr << "FATAL: Could not create file: " << PathIdPP(fileId)
                << std::endl;
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
  uint32_t nbProcesses = m_commandLineParser->getNbMaxProcesses();
  if (nbProcesses == 0) return true;

  if (!(m_commandLineParser->writePpOutput() ||
        m_commandLineParser->writePpOutputFileId())) {
    return true;
  }

  FileSystem* const fileSystem = FileSystem::getInstance();
  SymbolTable* symbolTable = getSymbolTable();

  const bool muted = m_commandLineParser->muteStdout();
  const fs::path workingDir = fileSystem->getWorkingDir();
  const fs::path outputDir =
      fileSystem->toPlatformAbsPath(m_commandLineParser->getOutputDirId());
  const fs::path programPath =
      fileSystem->toPlatformAbsPath(m_commandLineParser->getProgramId());
  const std::string_view profile =
      m_commandLineParser->profile() ? " -profile " : " ";
  const std::string_view sverilog =
      m_commandLineParser->fullSVMode() ? " -sverilog " : " ";
  const std::string_view fileUnit =
      m_commandLineParser->fileunit() ? " -fileunit " : " ";
  std::string synth =
      m_commandLineParser->reportNonSynthesizable() ? " -synth " : " ";
  synth += m_commandLineParser->reportNonSynthesizableWithFormal() ? " -formal "
                                                                   : " ";
  const std::string_view noHash =
      m_commandLineParser->noCacheHash() ? " -nohash " : " ";

  std::string fileList;
  // +define+
  for (const auto& [id, value] : m_commandLineParser->getDefineList()) {
    const std::string_view defName =
        m_commandLineParser->getSymbolTable()->getSymbol(id);
    std::string val = StringUtils::replaceAll(value, "#", "\\#");
    StrAppend(&fileList, " -D", defName, "=", val);
  }

  // Source files (.v, .sv on the command line)
  for (const PathId& id : m_commandLineParser->getSourceFiles()) {
    std::string_view svFile = m_commandLineParser->isSVFile(id) ? " -sv " : " ";
    StrAppend(&fileList, svFile, fileSystem->toPath(id));
  }
  // Library files (-v <file>)
  for (const PathId& id : m_commandLineParser->getLibraryFiles()) {
    StrAppend(&fileList, " -v ", fileSystem->toPath(id));
  }
  // (-y <path> +libext+<ext>)
  for (const PathId& id : m_commandLineParser->getLibraryPaths()) {
    StrAppend(&fileList, " -y ", fileSystem->toPath(id));
  }
  // +libext+
  for (const SymbolId& id : m_commandLineParser->getLibraryExtensions()) {
    const std::string_view extName =
        m_commandLineParser->getSymbolTable()->getSymbol(id);
    StrAppend(&fileList, " +libext+", extName);
  }
  // Include dirs
  for (const PathId& id : m_commandLineParser->getIncludePaths()) {
    StrAppend(&fileList, " -I", fileSystem->toPath(id));
  }

  std::string batchCmd = StrCat(profile, fileUnit, sverilog, synth, noHash,
                                " -writepp -mt 0 -mp 0 -nobuiltin -noparse "
                                "-nostdout -l preprocessing.log -cd ",
                                workingDir, fileList);
  for (const std::string& wd : fileSystem->getWorkingDirs()) {
    StrAppend(&batchCmd, " -wd ", wd);
  }

  const PathId dirId = fileSystem->getParserMultiprocessingDir(
      m_commandLineParser->fileunit(), symbolTable);
  fileSystem->mkdirs(dirId);

  if (nbProcesses == 1) {
    // Single child process
    const PathId fileId =
        fileSystem->getChild(dirId, "pp_batch.txt", symbolTable);
    if (!fileSystem->writeContent(fileId, batchCmd)) {
      std::cerr << "FATAL: Could not create file: " << PathIdPP(fileId)
                << std::endl;
      return false;
    }
    std::string command =
        StrCat("cd ", workingDir, "; ", programPath, " -o ", outputDir,
               " -nostdout -batch ", fileSystem->toPath(fileId));
    if (!muted) std::cout << "Running: " << command << std::endl << std::flush;
    int32_t result = system(command.c_str());
    if (!muted) std::cout << "Surelog preproc status: " << result << std::endl;
    if (!result) return false;
  } else {
    // Create CMakeLists.txt
    StrAppend(&batchCmd, " -o ", outputDir);

    const PathId fileId =
        fileSystem->getChild(dirId, "CMakeLists.txt", symbolTable);
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
      std::cerr << "FATAL: Could not create file: " << PathIdPP(fileId)
                << std::endl;
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
  Precompiled* const prec = Precompiled::getSingleton();

  // Single out the large files.
  // Small files are going to be scheduled in multiple threads based on size.
  // Large files are going to be compiled in a different batch in multithread

  if (!m_commandLineParser->fileunit()) {
    DeleteContainerPointersAndClear(&m_symbolTables);
    DeleteContainerPointersAndClear(&m_errorContainers);
  }

  std::vector<CompileSourceFile*> tmp_compilers;
  for (CompileSourceFile* const compiler : m_compilers) {
    const uint32_t nbThreads =
        prec->isFilePrecompiled(compiler->getPpOutputFileId(),
                                compiler->getSymbolTable())
            ? 0
            : m_commandLineParser->getNbMaxTreads();

    const int32_t effectiveNbThreads = calculateEffectiveThreads(nbThreads);

    AnalyzeFile* const fileAnalyzer = new AnalyzeFile(
        m_commandLineParser, m_design, compiler->getPpOutputFileId(),
        compiler->getFileId(), effectiveNbThreads, m_text);
    fileAnalyzer->analyze();
    compiler->setFileAnalyzer(fileAnalyzer);
    if (fileAnalyzer->getSplitFiles().size() > 1) {
      // Schedule parent
      m_compilersParentFiles.push_back(compiler);
      compiler->initParser();

      if (!m_commandLineParser->fileunit()) {
        SymbolTable* symbols =
            m_commandLineParser->getSymbolTable()->CreateSnapshot();
        m_symbolTables.push_back(symbols);
        compiler->setSymbolTable(symbols);
        // fileContent->setSymbolTable(symbols);
        ErrorContainer* errors =
            new ErrorContainer(symbols, m_errors->getLogListener());
        m_errorContainers.push_back(errors);
        errors->registerCmdLine(m_commandLineParser);
        compiler->setErrorContainer(errors);
      }

      compiler->getParser()->setFileContent(new FileContent(
          compiler->getParser()->getFileId(0),
          compiler->getParser()->getLibrary(), compiler->getSymbolTable(),
          compiler->getErrorContainer(), nullptr, BadPathId));

      int32_t j = 0;
      for (const auto& ppId : fileAnalyzer->getSplitFiles()) {
        SymbolTable* symbols =
            m_commandLineParser->getSymbolTable()->CreateSnapshot();
        m_symbolTables.push_back(symbols);
        CompileSourceFile* chunkCompiler = new CompileSourceFile(
            compiler, ppId, fileAnalyzer->getLineOffsets()[j]);
        // Schedule chunk
        tmp_compilers.push_back(chunkCompiler);

        chunkCompiler->setSymbolTable(symbols);
        ErrorContainer* errors =
            new ErrorContainer(symbols, m_errors->getLogListener());
        m_errorContainers.push_back(errors);
        errors->registerCmdLine(m_commandLineParser);
        chunkCompiler->setErrorContainer(errors);
        // chunkCompiler->getParser ()->setFileContent (fileContent);

        FileContent* const chunkFileContent =
            new FileContent(compiler->getParser()->getFileId(0),
                            compiler->getParser()->getLibrary(), symbols,
                            errors, nullptr, ppId);
        chunkCompiler->getParser()->setFileContent(chunkFileContent);
        getDesign()->addFileContent(compiler->getParser()->getFileId(0),
                                    chunkFileContent);

        j++;
      }
    } else {
      if ((!m_commandLineParser->fileunit()) && m_text.empty()) {
        SymbolTable* symbols =
            m_commandLineParser->getSymbolTable()->CreateSnapshot();
        m_symbolTables.push_back(symbols);
        compiler->setSymbolTable(symbols);
        ErrorContainer* errors =
            new ErrorContainer(symbols, m_errors->getLogListener());
        m_errorContainers.push_back(errors);
        errors->registerCmdLine(m_commandLineParser);
        compiler->setErrorContainer(errors);
      }

      tmp_compilers.push_back(compiler);
    }
  }
  m_compilers = tmp_compilers;

  return true;
}

bool Compiler::pythoninit_() { return parseinit_(); }

ErrorContainer::Stats Compiler::getErrorStats() const {
  ErrorContainer::Stats stats;
  for (const auto& s : m_errorContainers) {
    stats += s->getErrorStats();
  }

  return stats;
}

bool Compiler::cleanup_() {
  DeleteContainerPointersAndClear(&m_compilers);
  DeleteContainerPointersAndClear(&m_compilationUnits);
  DeleteContainerPointersAndClear(&m_symbolTables);
  DeleteContainerPointersAndClear(&m_errorContainers);
  return true;
}

bool Compiler::compileFileSet_(CompileSourceFile::Action action,
                               bool allowMultithread,
                               std::vector<CompileSourceFile*>& container) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  const uint16_t maxThreadCount =
      allowMultithread ? m_commandLineParser->getNbMaxTreads() : 0;

  if (maxThreadCount < 1) {
    // Single thread
    for (CompileSourceFile* const source : container) {
#ifdef SURELOG_WITH_PYTHON
      source->setPythonInterp(PythonAPI::getMainInterp());
#endif
      bool status = compileOneFile_(source, action);
      m_errors->appendErrors(*source->getErrorContainer());
      m_errors->printMessages(m_commandLineParser->muteStdout());
      if ((!status) || source->getErrorContainer()->hasFatalErrors()) {
        return false;
      }
    }
  } else if (getCommandLineParser()->useTbb() &&
             (action != CompileSourceFile::Action::Parse)) {
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
        if (getCommandLineParser()->pythonListener()) {
          source->shutdownPythonInterp();
        }
        m_errors->printMessages(m_commandLineParser->muteStdout());
      }
      if (fatalErrors) return false;
    } else {
      for (CompileSourceFile* const source : container) {
        source->setPythonInterp(PythonAPI::getMainInterp());
        bool status = compileOneFile_(source, action);
        m_errors->appendErrors(*souirce->getErrorContainer());
        m_errors->printMessages(m_commandLineParser->muteStdout());
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
      jobArray[newJobIndex].push_back(source);
    }

    if (getCommandLineParser()->profile()) {
      if (action == CompileSourceFile::Preprocess)
        std::cout << "Preprocessing task" << std::endl;
      else if (action == CompileSourceFile::Parse)
        std::cout << "Parsing task" << std::endl;
      else
        std::cout << "Misc Task" << std::endl;
      for (uint16_t i = 0; i < maxThreadCount; i++) {
        std::cout << "Thread " << i << " : " << std::endl;
        int32_t sum = 0;
        for (const CompileSourceFile* job : jobArray[i]) {
          PathId fileId;
          if (job->getPreprocessor())
            fileId = job->getPreprocessor()->getFileId(0);
          else if (job->getParser())
            fileId = job->getParser()->getFileId(0);
          sum += job->getJobSize(action);
          std::cout << job->getJobSize(action) << " "
                    << fileSystem->toPath(fileId) << std::endl;
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
          if (getCommandLineParser()->pythonListener() ||
              getCommandLineParser()->pythonEvalScriptPerFile()) {
            PyThreadState* interpState = PythonAPI::initNewInterp();
            job->setPythonInterp(interpState);
          }
#endif
          job->compile(action);
#ifdef SURELOG_WITH_PYTHON
          if (getCommandLineParser()->pythonListener() ||
              getCommandLineParser()->pythonEvalScriptPerFile()) {
            job->shutdownPythonInterp();
          }
#endif
        }
      });
      threads.push_back(th);
    }

    // Wait for all of them to finish
    for (auto& t : threads) {
      t->join();
    }

    // Delete the threads
    DeleteContainerPointersAndClear(&threads);

    // Promote report to master error container
    bool fatalErrors = false;
    for (CompileSourceFile* const source : container) {
      m_errors->appendErrors(*source->getErrorContainer());
      if (source->getErrorContainer()->hasFatalErrors()) {
        fatalErrors = true;
      }
    }
    m_errors->printMessages(m_commandLineParser->muteStdout());

    if (fatalErrors) return false;
  }
  return true;
}

bool Compiler::compile() {
  FileSystem* const fileSystem = FileSystem::getInstance();
  std::string profile;
  Timer tmr;
  Timer tmrTotal;
  // Scan the libraries definition
  if (!parseLibrariesDef_()) return false;

  if (m_commandLineParser->profile()) {
    std::string msg = "Scan libraries took " +
                      StringUtils::to_string(tmr.elapsed_rounded()) + "s\n";
    std::cout << msg << std::endl;
    profile += msg;
    tmr.reset();
  }

  // Preprocess
  ppinit_();
  createMultiProcessPreProcessor_();
  if (!compileFileSet_(CompileSourceFile::Preprocess,
                       m_commandLineParser->fileunit(), m_compilers)) {
    return false;
  }
  // Single thread post Preprocess
  if (!compileFileSet_(CompileSourceFile::PostPreprocess, false, m_compilers)) {
    return false;
  }

  if (m_commandLineParser->profile()) {
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
  if (m_commandLineParser->parse() || m_commandLineParser->pythonListener() ||
      m_commandLineParser->pythonEvalScriptPerFile() ||
      m_commandLineParser->pythonEvalScript()) {
    parseinit_();
    createFileList_();
    createMultiProcessParser_();
    parserInitialized = true;
    if (!compileFileSet_(CompileSourceFile::Parse, true, m_compilers)) {
      return false;  // Small files and large file chunks
    }
    if (!compileFileSet_(CompileSourceFile::Parse, true,
                         m_compilersParentFiles)) {
      return false;  // Recombine chunks
    }
  } else {
    createFileList_();
  }

  if (m_commandLineParser->profile()) {
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
  CheckCompile* checkComp = new CheckCompile(this);
  bool parseOk = checkComp->check();
  delete checkComp;
  m_errors->printMessages(m_commandLineParser->muteStdout());

  // Python Listener
  if (parseOk && (m_commandLineParser->pythonListener() ||
                  m_commandLineParser->pythonEvalScriptPerFile())) {
    if (!parserInitialized) pythoninit_();
    if (!compileFileSet_(CompileSourceFile::PythonAPI, true, m_compilers))
      return false;
    if (!compileFileSet_(CompileSourceFile::PythonAPI, true,
                         m_compilersParentFiles))
      return false;

    if (m_commandLineParser->profile()) {
      std::string msg = "Python file processing took " +
                        StringUtils::to_string(tmr.elapsed_rounded()) + "s\n";
      std::cout << msg << std::endl;
      profile += msg;
      tmr.reset();
    }
  }

  if (parseOk && m_commandLineParser->compile()) {
    // Compile Design, has its own thread management
    m_compileDesign = new CompileDesign(this);
    m_compileDesign->compile();
    m_errors->printMessages(m_commandLineParser->muteStdout());

    if (m_commandLineParser->profile()) {
      std::string msg = "Compilation took " +
                        StringUtils::to_string(tmr.elapsed_rounded()) + "s\n";
      std::cout << msg << std::endl;
      profile += msg;
      tmr.reset();
    }

    m_compileDesign->purgeParsers();

    if (m_commandLineParser->elaborate()) {
      m_compileDesign->elaborate();
      m_errors->printMessages(m_commandLineParser->muteStdout());

      if (m_commandLineParser->profile()) {
        std::string msg = "Elaboration took " +
                          StringUtils::to_string(tmr.elapsed_rounded()) + "s\n";
        std::cout << msg << std::endl;
        profile += msg;
        tmr.reset();
      }

      if (m_commandLineParser->pythonEvalScript()) {
        PythonAPI::evalScript(
            fileSystem->toPath(m_commandLineParser->pythonEvalScriptId()),
            m_design);
        if (m_commandLineParser->profile()) {
          std::string msg = "Python design processing took " +
                            StringUtils::to_string(tmr.elapsed_rounded()) +
                            "s\n";
          profile += msg;
          std::cout << msg << std::endl;
          tmr.reset();
        }
      }
      m_errors->printMessages(m_commandLineParser->muteStdout());
    }

    PathId uhdmFileId = fileSystem->getChild(
        m_commandLineParser->getCompileDirId(), "surelog.uhdm",
        m_compileDesign->getCompiler()->getSymbolTable());
    m_uhdmDesign = m_compileDesign->writeUHDM(uhdmFileId);
    // Do not delete as now UHDM has to live past the compilation step
    // delete compileDesign;
  }
  if (m_commandLineParser->profile()) {
    std::string msg = "Total time " +
                      StringUtils::to_string(tmrTotal.elapsed_rounded()) +
                      "s\n";
    profile += msg;
    profile = std::string("==============\n") + "PROFILE\n" +
              std::string("==============\n") + profile + "==============\n";
    std::cout << profile << std::endl;
    m_errors->printToLogFile(profile);
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
  ParseLibraryDef* libParser = new ParseLibraryDef(
      m_commandLineParser, m_errors, m_symbolTable, m_librarySet, m_configSet);
  bool result = libParser->parseLibrariesDefinition();
  delete libParser;
  return result;
}
}  // namespace SURELOG
