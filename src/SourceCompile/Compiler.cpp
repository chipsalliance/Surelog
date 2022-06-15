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

#include <Surelog/API/PythonAPI.h>
#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Config/ConfigSet.h>
#include <Surelog/Design/Design.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/DesignCompile/Builtin.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/Library/Library.h>
#include <Surelog/Library/LibrarySet.h>
#include <Surelog/Library/ParseLibraryDef.h>
#include <Surelog/Package/Precompiled.h>
#include <Surelog/SourceCompile/AnalyzeFile.h>
#include <Surelog/SourceCompile/CheckCompile.h>
#include <Surelog/SourceCompile/CompilationUnit.h>
#include <Surelog/SourceCompile/CompileSourceFile.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/ParseFile.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/ContainerUtils.h>
#include <Surelog/Utils/FileUtils.h>
#include <Surelog/Utils/StringUtils.h>
#include <Surelog/Utils/Timer.h>
#include <antlr4-runtime.h>

#include <thread>

#if defined(_MSC_VER)
#include <direct.h>
#else
#include <sys/param.h>
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
                   SymbolTable* symbolTable, const std::string& text)
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

struct FunctorCompileOneFile {
  FunctorCompileOneFile(CompileSourceFile* compileSource,
                        CompileSourceFile::Action action)
      : m_compileSourceFile(compileSource), m_action(action) {}

  int operator()() const {
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

bool Compiler::isLibraryFile(SymbolId id) const {
  return (m_libraryFiles.find(id) != m_libraryFiles.end());
}

bool Compiler::ppinit_() {
  if (!m_commandLineParser->fileunit()) {
    m_commonCompilationUnit = new CompilationUnit(false);
    if (m_commandLineParser->parseBuiltIn()) {
      Builtin* builtin = new Builtin(nullptr, nullptr);
      builtin->addBuiltinMacros(m_commonCompilationUnit);
    }
  }

  CompilationUnit* comp_unit = m_commonCompilationUnit;

  // Source files (.v, .sv on the command line)
  SymbolIdSet sourceFiles;
  std::set<fs::path> sourceFileNames;
  for (const SymbolId& source_file_id : m_commandLineParser->getSourceFiles()) {
    SymbolTable* symbols = m_symbolTable;
    if (m_commandLineParser->fileunit()) {
      comp_unit = new CompilationUnit(true);
      if (m_commandLineParser->parseBuiltIn()) {
        Builtin* builtin = new Builtin(nullptr, nullptr);
        builtin->addBuiltinMacros(comp_unit);
      }
      m_compilationUnits.push_back(comp_unit);
      symbols = m_commandLineParser->getSymbolTable().CreateSnapshot();
      m_symbolTables.push_back(symbols);
    }
    ErrorContainer* errors = new ErrorContainer(symbols);
    m_errorContainers.push_back(errors);
    errors->registerCmdLine(m_commandLineParser);

    const fs::path fileName =
        m_commandLineParser->getSymbolTable().getSymbol(source_file_id);
    const fs::path fullPath = FileUtils::getFullPath(fileName);
    sourceFileNames.insert(fullPath);
    const SymbolId fullPathId =
        m_commandLineParser->mutableSymbolTable()->registerSymbol(
            fullPath.string());
    Library* library = m_librarySet->getLibrary(fullPathId);
    sourceFiles.insert(fullPathId);

    CompileSourceFile* compiler =
        new CompileSourceFile(source_file_id, m_commandLineParser, errors, this,
                              symbols, comp_unit, library);
    m_compilers.push_back(compiler);
  }

  if (!m_text.empty()) {
    Library* library = new Library("UnitTest", m_symbolTable);
    CompileSourceFile* compiler =
        new CompileSourceFile(BadSymbolId, m_commandLineParser, m_errors, this,
                              m_symbolTable, comp_unit, library, m_text);
    m_compilers.push_back(compiler);
  }

  // Library files
  SymbolIdSet libFiles;
  // (-v <file>)
  for (const SymbolId& id : m_commandLineParser->getLibraryFiles()) {
    const fs::path fileName =
        m_commandLineParser->getSymbolTable().getSymbol(id);
    const fs::path fullPath = FileUtils::getFullPath(fileName);
    if (sourceFileNames.find(fullPath) == sourceFileNames.end()) {
      libFiles.insert(id);
    }
  }
  // (-y <path> +libext+<ext>)
  for (const auto& path : m_commandLineParser->getLibraryPaths()) {
    for (const auto& ext : m_commandLineParser->getLibraryExtensions()) {
      auto files = FileUtils::collectFiles(
          path, ext, m_commandLineParser->mutableSymbolTable());
      for (const auto& file : files) {
        const fs::path fileName =
            m_commandLineParser->getSymbolTable().getSymbol(file);
        const fs::path fullPath = FileUtils::getFullPath(fileName);
        if (sourceFileNames.find(fullPath) == sourceFileNames.end()) {
          libFiles.insert(file);
        }
      }
    }
  }
  for (const auto& id : libFiles) {
    SymbolTable* symbols = m_symbolTable;
    if (m_commandLineParser->fileunit()) {
      comp_unit = new CompilationUnit(true);
      m_compilationUnits.push_back(comp_unit);
      symbols = m_commandLineParser->getSymbolTable().CreateSnapshot();
      m_symbolTables.push_back(symbols);
    }
    ErrorContainer* errors = new ErrorContainer(symbols);
    m_errorContainers.push_back(errors);
    errors->registerCmdLine(m_commandLineParser);

    fs::path fullPath = FileUtils::getFullPath(
        m_commandLineParser->getSymbolTable().getSymbol(id));

    // This line registers the file in the "work" library:
    SymbolId fullPathId =
        m_commandLineParser->mutableSymbolTable()->registerSymbol(
            fullPath.string());
    /*Library* library  = */ m_librarySet->getLibrary(fullPathId);
    m_libraryFiles.insert(id);
    m_libraryFiles.insert(fullPathId);
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
    for (const auto& id : lib.getFiles()) {
      fs::path fileName = lib.getSymbols()->getSymbol(id);
      if (sourceFiles.find(id) != sourceFiles.end()) {
        // These files are already included in the command line
        continue;
      }

      if (fileName.extension() == ".map") {
        // .map files are not parsed with the regular parser
        continue;
      }
      SymbolTable* symbols = m_symbolTable;
      if (m_commandLineParser->fileunit()) {
        comp_unit = new CompilationUnit(true);
        m_compilationUnits.push_back(comp_unit);
        symbols = m_commandLineParser->getSymbolTable().CreateSnapshot();
        m_symbolTables.push_back(symbols);
      }
      ErrorContainer* errors = new ErrorContainer(symbols);
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
  if ((m_commandLineParser->writePpOutput() ||
       m_commandLineParser->writePpOutputFileId()) &&
      (!m_commandLineParser->parseOnly())) {
    SymbolTable* symbolTable = getSymbolTable();
    const fs::path directory =
        symbolTable->getSymbol(m_commandLineParser->getFullCompileDir());
    {
      std::ofstream ofs;
      fs::path fileList = directory / "file.lst";
      ofs.open(fileList);
      if (ofs.good()) {
        unsigned int size = m_compilers.size();
        for (unsigned int i = 0; i < size; i++) {
          fs::path ppFileName = m_compilers[i]->getSymbolTable()->getSymbol(
              m_compilers[i]->getPpOutputFileId());
          fs::path fileName = m_compilers[i]->getSymbolTable()->getSymbol(
              m_compilers[i]->getFileId());
          ppFileName = FileUtils::getPreferredPath(ppFileName);
          ppFileMap[fileName].push_back(ppFileName);
          ofs << ppFileName << std::flush << std::endl;
        }
        ofs.close();
      } else {
        std::cout << "Could not create filelist: " << fileList << std::endl;
      }
    }
    {
      std::ofstream ofs;
      fs::path fileList = directory / "file_map.lst";
      ofs.open(fileList);
      if (ofs.good()) {
        unsigned int size = m_compilers.size();
        for (unsigned int i = 0; i < size; i++) {
          fs::path ppFileName = m_compilers[i]->getSymbolTable()->getSymbol(
              m_compilers[i]->getPpOutputFileId());
          fs::path fileName = m_compilers[i]->getSymbolTable()->getSymbol(
              m_compilers[i]->getFileId());
          ppFileName = FileUtils::getPreferredPath(ppFileName);
          ppFileName = ppFileName.lexically_relative(directory);
          ofs << ppFileName << " " << fileName << std::flush << std::endl;
        }
        ofs.close();
      } else {
        std::cout << "Could not create filelist: " << fileList << std::endl;
      }
    }
    {
      if (m_commandLineParser->sepComp()) {
        std::string concatFiles;
        unsigned int size = m_compilers.size();
        for (unsigned int i = 0; i < size; i++) {
          fs::path fileName = m_compilers[i]->getSymbolTable()->getSymbol(
              m_compilers[i]->getFileId());
          concatFiles += fileName.string() + "|";
        }
        std::size_t val = std::hash<std::string>{}(concatFiles);
        std::string hashedName = std::to_string(val);
        hashedName += ".sep_lst";
        std::ofstream ofs;
        fs::path fileList = directory / hashedName;
        ofs.open(fileList);
        if (ofs.good()) {
          unsigned int size = m_compilers.size();
          for (unsigned int i = 0; i < size; i++) {
            fs::path fileName = m_compilers[i]->getSymbolTable()->getSymbol(
                m_compilers[i]->getFileId());
            if (i > 0) ofs << " ";
            ofs << fileName.string();
          }
          ofs.close();
        } else {
          std::cout << "Could not create filelist: " << fileList << std::endl;
        }
      }
    }
  }
  return true;
}

bool Compiler::createMultiProcessParser_() {
  unsigned int nbProcesses = m_commandLineParser->getNbMaxProcesses();
  if (nbProcesses == 0) return true;
  // Create CMakeLists.txt
  if (m_commandLineParser->writePpOutput() ||
      m_commandLineParser->writePpOutputFileId()) {
    bool muted = m_commandLineParser->muteStdout();
    SymbolTable* symbolTable = getSymbolTable();
    const fs::path directory =
        symbolTable->getSymbol(m_commandLineParser->getFullCompileDir());
    std::ofstream ofs;
    fs::path fileList = directory / "CMakeLists.txt";
    ofs.open(fileList);
    std::vector<std::string> batchProcessCommands;
    if (ofs.good()) {
      ofs << "cmake_minimum_required (VERSION 3.0)" << std::endl;
      ofs << "# Auto generated by Surelog" << std::endl;
      ofs << "project(SurelogParsing)" << std::endl;
      // Optimize the load balance, try to even out the work in each thread by
      // the size of the files
      std::vector<std::vector<CompileSourceFile*>> jobArray(nbProcesses);
      std::vector<unsigned long> jobSize(nbProcesses);
      size_t largestJob = 0;
      for (const auto& compiler : m_compilers) {
        size_t size = compiler->getJobSize(CompileSourceFile::Action::Parse);
        if (size > largestJob) {
          largestJob = size;
        }
      }
      unsigned int bigJobThreashold = (largestJob / nbProcesses) * 3;
      std::vector<CompileSourceFile*> bigJobs;
      for (size_t i = 0; i < nbProcesses; i++) jobSize[i] = 0;
      bool forcedSVMode = m_commandLineParser->fullSVMode();
      std::string sverilog = (forcedSVMode) ? " -sverilog " : "";
      Precompiled* prec = Precompiled::getSingleton();

      char path[10000];
      char* p = getcwd(path, 9999);
      fs::path outputPath = fs::path(p) / directory / ".." / "";
      for (const auto& compiler : m_compilers) {
        fs::path root =
            compiler->getSymbolTable()->getSymbol(compiler->getFileId());
        root = FileUtils::basename(root);
        if (prec->isFilePrecompiled(root)) {
          continue;
        }
        unsigned int size =
            compiler->getJobSize(CompileSourceFile::Action::Parse);
        if (size > bigJobThreashold) {
          bigJobs.push_back(compiler);
          continue;
        }
        unsigned int newJobIndex = 0;
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

      fs::path full_exe_path = m_commandLineParser->getExePath();
      if (m_commandLineParser->profile()) {
        full_exe_path += " -profile";
      }

      std::string fileUnit;
      if (m_commandLineParser->fileunit()) fileUnit = " -fileunit ";
      std::string synth;
      if (m_commandLineParser->reportNonSynthesizable()) synth = " -synth ";

      std::vector<std::string> targets;
      int absoluteIndex = 0;

      // Big jobs
      for (CompileSourceFile* compiler : bigJobs) {
        absoluteIndex++;
        fs::path fileName = compiler->getSymbolTable()->getSymbol(
            compiler->getPpOutputFileId());
        fileName = fileName.lexically_relative(directory);
        std::string targetname = std::to_string(absoluteIndex) + "_" +
                                 FileUtils::basename(fileName).string();
        targets.push_back(targetname);
        std::string svFile;
        fs::path baseFileName = FileUtils::basename(fileName);
        if (m_commandLineParser->isSVFile(baseFileName)) {
          svFile = " -sv ";
        }
        std::string noHash;
        if (m_commandLineParser->noCacheHash()) {
          noHash = " -nohash ";
        }
        std::string batchCmd = fileUnit + sverilog + synth + noHash +
                               " -parseonly -nostdout -mt 0 -mp 0 -o " +
                               outputPath.string() + " -nobuiltin -l " +
                               FileUtils::basename(targetname).string() +
                               ".log" + " " + svFile + fileName.string();

        ofs << "add_custom_command(OUTPUT " << targetname << std::endl;
        ofs << "  COMMAND " << full_exe_path << batchCmd << std::endl;
        ofs << ")" << std::endl;
        batchProcessCommands.push_back(batchCmd);
      }

      // Small jobs batch in clump processes
      for (size_t i = 0; i < nbProcesses; i++) {
        std::string fileList;
        fs::path lastFile;
        absoluteIndex++;
        for (const auto compiler : jobArray[i]) {
          fs::path fileName = compiler->getSymbolTable()->getSymbol(
              compiler->getPpOutputFileId());
          fs::path baseFileName = FileUtils::basename(fileName);
          std::string svFile;
          if (m_commandLineParser->isSVFile(baseFileName)) {
            svFile = " -sv ";
          }
          fileName = fileName.lexically_relative(directory);
          fileList += " " + svFile + fileName.string();
          lastFile = fileName;
        }
        if (!fileList.empty()) {
          std::string targetname = std::to_string(absoluteIndex) + "_" +
                                   FileUtils::basename(lastFile).string();
          targets.push_back(targetname);

          std::string batchCmd = fileUnit + sverilog + synth +
                                 " -parseonly -nostdout -mt 0 -mp 0 -o " +
                                 outputPath.string() + " -nobuiltin -l " +
                                 FileUtils::basename(targetname).string() +
                                 ".log" + " " + fileList;

          ofs << "add_custom_command(OUTPUT " << targetname << std::endl;
          ofs << "  COMMAND " << full_exe_path << batchCmd << std::endl;
          ofs << ")" << std::endl;
          batchProcessCommands.push_back(batchCmd);
        }
      }

      ofs << "add_custom_target(Parse ALL DEPENDS" << std::endl;
      for (const auto& target : targets) {
        ofs << target << std::endl;
      }
      ofs << ")" << std::endl;
      ofs << std::flush;
      ofs.close();

      if (nbProcesses == 1) {
        // Single child process
        fs::path fileList = directory / "parser_batch.txt";
        ofs.open(fileList);
        for (const auto& line : batchProcessCommands) {
          ofs << line << "\n";
        }
        ofs.close();
        std::string command = "cd " + directory.string() + ";" +
                              full_exe_path.string() +
                              " -nostdout -batch parser_batch.txt";
        if (!muted)
          std::cout << "Running: " << command << std::endl << std::flush;
        int result = system(command.c_str());
        if (!muted)
          std::cout << "Surelog parsing status: " << result << std::endl;
      } else {
        // Multiple child processes managed by cmake
        std::string command = "cd " + directory.string() + ";" +
                              "cmake .; make -j " + std::to_string(nbProcesses);
        if (!muted)
          std::cout << "Running: " << command << std::endl << std::flush;
        int result = system(command.c_str());
        if (!muted)
          std::cout << "Surelog parsing status: " << result << std::endl;
      }
    } else {
      if (!muted)
        std::cout << "FATAL: Could not create CMakeLists.txt: " << fileList
                  << std::endl;
    }
  }
  return true;
}

bool Compiler::createMultiProcessPreProcessor_() {
  unsigned int nbProcesses = m_commandLineParser->getNbMaxProcesses();
  if (nbProcesses == 0) return true;
  // Create CMakeLists.txt
  if (m_commandLineParser->writePpOutput() ||
      m_commandLineParser->writePpOutputFileId()) {
    bool muted = m_commandLineParser->muteStdout();
    SymbolTable* symbolTable = getSymbolTable();
    const fs::path directory =
        symbolTable->getSymbol(m_commandLineParser->getFullCompileDir());
    std::ofstream ofs;
    fs::path fileList = directory / "CMakeLists.txt";
    ofs.open(fileList);
    if (ofs.good()) {
      ofs << "cmake_minimum_required (VERSION 3.0)" << std::endl;
      ofs << "# Auto generated by Surelog" << std::endl;
      ofs << "project(SurelogPreprocessing)" << std::endl;

      bool forcedSVMode = m_commandLineParser->fullSVMode();
      std::string sverilog = (forcedSVMode) ? " -sverilog " : "";
      char path[10000] = {'\0'};
      char* p = getcwd(path, 9999);
      fs::path outputPath = fs::path(p) / directory / "..";
      fs::path full_exe_path = m_commandLineParser->getExePath();
      if (m_commandLineParser->profile()) {
        full_exe_path += " -profile";
      }

      std::string fileUnit;
      if (m_commandLineParser->fileunit()) fileUnit = " -fileunit ";

      std::string synth;
      if (m_commandLineParser->reportNonSynthesizable()) synth = " -synth ";

      std::string fileList;
      // +define+
      for (const auto& id_value : m_commandLineParser->getDefineList()) {
        const std::string defName =
            m_commandLineParser->getSymbolTable().getSymbol(id_value.first);
        std::string val;
        for (char c : id_value.second) {
          if (c == '#') {
            val += '\\';
          }
          val += c;
        }

        fileList += " -D" + defName + "=" + val;
      }

      // Source files (.v, .sv on the command line)
      for (const SymbolId& id : m_commandLineParser->getSourceFiles()) {
        const fs::path fileName =
            m_commandLineParser->getSymbolTable().getSymbol(id);
        std::string svFile;
        fs::path baseFileName = FileUtils::basename(fileName);
        if (m_commandLineParser->isSVFile(baseFileName)) {
          svFile = " -sv ";
        }
        fileList += " " + svFile + fileName.string();
      }
      // Library files
      // (-v <file>)
      for (const SymbolId& id : m_commandLineParser->getLibraryFiles()) {
        const fs::path fileName =
            m_commandLineParser->getSymbolTable().getSymbol(id);
        fileList += " -v " + fileName.string();
      }
      // (-y <path> +libext+<ext>)
      for (const auto& id : m_commandLineParser->getLibraryPaths()) {
        const fs::path fileName =
            m_commandLineParser->getSymbolTable().getSymbol(id);
        fileList += " -y " + fileName.string();
      }
      // +libext+
      for (const auto& id : m_commandLineParser->getLibraryExtensions()) {
        const std::string extName =
            m_commandLineParser->getSymbolTable().getSymbol(id);
        fileList += " +libext+" + extName;
      }
      // Include dirs
      for (const SymbolId& id : m_commandLineParser->getIncludePaths()) {
        const fs::path fileName =
            m_commandLineParser->getSymbolTable().getSymbol(id);
        fileList += " -I" + fileName.string();
      }
      std::string noHash;
      if (m_commandLineParser->noCacheHash()) {
        noHash = " -nohash ";
      }
      std::string batchCmd = fileUnit + sverilog + synth + noHash +
                             " -writepp -mt 0 -mp 0 -o " + outputPath.string() +
                             " -nobuiltin -noparse -nostdout -cd " +
                             std::string(p) + " -l " + directory.string() +
                             "/preprocessing.log" + " " + fileList;

      ofs << "add_custom_command(OUTPUT preprocessing" << std::endl;
      ofs << "  COMMAND " << full_exe_path << batchCmd << std::endl;
      ofs << ")" << std::endl;

      ofs << "add_custom_target(Parse ALL DEPENDS preprocessing)" << std::endl;
      ofs << std::flush;
      ofs.close();
      if (nbProcesses == 1) {
        // Single child process
        fs::path fileList = directory / "pp_batch.txt";
        ofs.open(fileList);
        ofs << batchCmd << "\n";
        ofs.close();
        std::string command = "cd " + directory.string() + ";" +
                              full_exe_path.string() +
                              " -nostdout -batch pp_batch.txt";
        if (!muted)
          std::cout << "Running: " << command << std::endl << std::flush;
        int result = system(command.c_str());
        if (!muted)
          std::cout << "Surelog preproc status: " << result << std::endl;
      } else {
        std::string command =
            "cd " + directory.string() + ";" + "cmake .; make";
        if (!muted)
          std::cout << "Running: " << command << std::endl << std::flush;
        int result = system(command.c_str());
        if (!muted)
          std::cout << "Surelog preproc status: " << result << std::endl;
      }
    } else {
      std::cout << "FATAL: Could not create CMakeLists.txt: " << fileList
                << std::endl;
    }
  }
  return true;
}

static int calculateEffectiveThreads(int nbThreads) {
  if (nbThreads <= 4) return nbThreads;
  return (int)(log(((float)nbThreads + 1.0) / 4.0) * 10.0);
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
    const fs::path fileName =
        compiler->getSymbolTable()->getSymbol(compiler->getPpOutputFileId());
    const fs::path origFile =
        compiler->getSymbolTable()->getSymbol(compiler->getFileId());
    const fs::path root = FileUtils::basename(fileName);
    const unsigned int nbThreads = prec->isFilePrecompiled(root)
                                       ? 0
                                       : m_commandLineParser->getNbMaxTreads();

    const int effectiveNbThreads = calculateEffectiveThreads(nbThreads);

    AnalyzeFile* const fileAnalyzer =
        new AnalyzeFile(m_commandLineParser, m_design, fileName, origFile,
                        effectiveNbThreads, m_text);
    fileAnalyzer->analyze();
    compiler->setFileAnalyzer(fileAnalyzer);
    if (fileAnalyzer->getSplitFiles().size() > 1) {
      // Schedule parent
      m_compilersParentFiles.push_back(compiler);
      compiler->initParser();

      if (!m_commandLineParser->fileunit()) {
        SymbolTable* symbols =
            m_commandLineParser->getSymbolTable().CreateSnapshot();
        m_symbolTables.push_back(symbols);
        compiler->setSymbolTable(symbols);
        // fileContent->setSymbolTable(symbols);
        ErrorContainer* errors = new ErrorContainer(symbols);
        m_errorContainers.push_back(errors);
        errors->registerCmdLine(m_commandLineParser);
        compiler->setErrorContainer(errors);
      }

      compiler->getParser()->setFileContent(new FileContent(
          compiler->getParser()->getFileId(0),
          compiler->getParser()->getLibrary(), compiler->getSymbolTable(),
          compiler->getErrorContainer(), nullptr, BadSymbolId));

      int j = 0;
      for (auto& chunk : fileAnalyzer->getSplitFiles()) {
        SymbolTable* symbols =
            m_commandLineParser->getSymbolTable().CreateSnapshot();
        m_symbolTables.push_back(symbols);
        SymbolId ppId = symbols->registerSymbol(chunk.string());
        symbols->registerSymbol(
            compiler->getParser()->getFileName(LINE1).string());
        CompileSourceFile* chunkCompiler = new CompileSourceFile(
            compiler, ppId, fileAnalyzer->getLineOffsets()[j]);
        // Schedule chunk
        tmp_compilers.push_back(chunkCompiler);

        chunkCompiler->setSymbolTable(symbols);
        ErrorContainer* errors = new ErrorContainer(symbols);
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
            m_commandLineParser->getSymbolTable().CreateSnapshot();
        m_symbolTables.push_back(symbols);
        compiler->setSymbolTable(symbols);
        ErrorContainer* errors = new ErrorContainer(symbols);
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
  const unsigned short maxThreadCount =
      allowMultithread ? m_commandLineParser->getNbMaxTreads() : 0;

  if (maxThreadCount == 0) {
    // Single thread
    for (CompileSourceFile* const source : container) {
#ifdef SURELOG_WITH_PYTHON
      source->setPythonInterp(PythonAPI::getMainInterp());
#endif
      bool status = compileOneFile_(source, action);
      m_errors->appendErrors(*source->getErrorContainer());
      m_errors->printMessages(m_commandLineParser->muteStdout());
      if ((!status) || source->getErrorContainer()->hasFatalErrors())
        return false;
    }
  } else if (getCommandLineParser()->useTbb() &&
             (action != CompileSourceFile::Action::Parse)) {
#ifdef USETBB
    // TBB Thread management
    const int maxThreadCount =
        allowMultithread ? m_commandLineParser->getNbMaxTreads() : 0;

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
    std::vector<unsigned long> jobSize(maxThreadCount, 0);

    for (CompileSourceFile* const source : container) {
      const unsigned int size = source->getJobSize(action);
      unsigned int newJobIndex = 0;
      uint64_t minJobQueue = ULLONG_MAX;
      for (unsigned short ii = 0; ii < maxThreadCount; ii++) {
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
        std::cout << "Preprocessing task\n";
      else if (action == CompileSourceFile::Parse)
        std::cout << "Parsing task\n";
      else
        std::cout << "Misc Task\n";
      for (unsigned short i = 0; i < maxThreadCount; i++) {
        std::cout << "Thread " << i << " : \n";
        int sum = 0;
        for (const CompileSourceFile* job : jobArray[i]) {
          fs::path fileName;
          if (job->getPreprocessor())
            fileName = job->getPreprocessor()->getFileName(0);
          if (job->getParser()) fileName = job->getParser()->getFileName(0);
          sum += job->getJobSize(action);
          std::cout << job->getJobSize(action) << " " << fileName << "\n";
        }
        std::cout << ", Total: " << sum << std::endl << std::flush;
      }
    }

    // Create the threads with their respective workloads
    std::vector<std::thread*> threads;
    for (unsigned short i = 0; i < maxThreadCount; i++) {
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
      if (source->getErrorContainer()->hasFatalErrors()) fatalErrors = true;
    }
    m_errors->printMessages(m_commandLineParser->muteStdout());

    if (fatalErrors) return false;
  }
  return true;
}

bool Compiler::compile() {
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
                       m_commandLineParser->fileunit(), m_compilers))
    return false;
  // Single thread post Preprocess
  if (!compileFileSet_(CompileSourceFile::PostPreprocess, false, m_compilers))
    return false;

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
    if (!compileFileSet_(CompileSourceFile::Parse, true, m_compilers))
      return false;  // Small files and large file chunks
    if (!compileFileSet_(CompileSourceFile::Parse, true,
                         m_compilersParentFiles))
      return false;  // Recombine chunks
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
        PythonAPI::evalScript(m_commandLineParser->getSymbolTable().getSymbol(
                                  m_commandLineParser->pythonEvalScriptId()),
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

    fs::path directory = m_commandLineParser->getSymbolTable().getSymbol(
        m_commandLineParser->getFullCompileDir());
    fs::path uhdmFile = directory / "surelog.uhdm";

    m_uhdmDesign = m_compileDesign->writeUHDM(uhdmFile.string());
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
    m_antlrPpMap.insert(std::make_pair(id, pp));
    return;
  }
  m_antlrPpMap.insert(std::make_pair(id, pp));
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
  return libParser->parseLibrariesDefinition();
}
}  // namespace SURELOG
