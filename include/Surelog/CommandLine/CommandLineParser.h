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
 * File:   CommandLineParser.hpp
 * Author: alain
 *
 * Created on January 26, 2017, 9:47 PM
 */

#ifndef SURELOG_COMMANDLINEPARSER_H
#define SURELOG_COMMANDLINEPARSER_H
#pragma once

#include <Surelog/Common/SymbolId.h>

#include <filesystem>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace SURELOG {

class ErrorContainer;
class SymbolTable;

class CommandLineParser final {
 public:
  CommandLineParser(ErrorContainer* errors, SymbolTable* symbolTable,
                    bool diff_comp_mode = false, bool fileUnit = false);
  bool parseCommandLine(int argc, const char** argv);

  /* Verilog command line content */
  const std::vector<SymbolId>& getLibraryPaths() const {
    return m_libraryPaths;
  }
  const std::vector<SymbolId>& getSourceFiles() const { return m_sourceFiles; }
  const std::vector<SymbolId>& getLibraryFiles() const {
    return m_libraryFiles;
  }
  const std::vector<SymbolId>& getLibraryExtensions() const {
    return m_libraryExtensions;
  }
  const std::vector<SymbolId>& getIncludePaths() const {
    return m_includePaths;
  }
  const std::vector<SymbolId>& getOrdredLibraries() const {
    return m_orderedLibraries;
  }
  const std::vector<SymbolId>& getLibraryMapFiles() const {
    return m_libraryMapFiles;
  }
  const std::vector<SymbolId>& getConfigFiles() const { return m_configFiles; }
  const std::vector<SymbolId>& getUseConfigs() const { return m_useConfigs; }
  const std::map<SymbolId, std::string>& getDefineList() const {
    return m_defineList;
  }
  const std::map<SymbolId, std::string>& getParamList() const {
    return m_paramList;
  }
  bool fileunit() const {
    return m_fileunit;
  }  // File or all compilation semantic
  void setFileUnit() { m_fileunit = true; }
  /* PP Output file/dir options */
  SymbolId writePpOutputFileId() const { return m_writePpOutputFileId; }
  SymbolId getOutputDir() const { return m_outputDir; }
  SymbolId getCompileAllDir() const { return m_compileAllDirectory; }
  SymbolId getCompileUnitDir() const { return m_compileUnitDirectory; }
  SymbolId getCompileDir() const {
    return fileunit() ? m_compileUnitDirectory : m_compileAllDirectory;
  }
  SymbolId getFullCompileDir() const { return m_fullCompileDir; }
  SymbolId getLogFileId() const { return m_logFileId; }
  SymbolId getDefaultLogFileId() const { return m_defaultLogFileId; }
  bool writePpOutput() const { return m_writePpOutput; }
  void setwritePpOutput(bool value) { m_writePpOutput = value; }
  bool cacheAllowed() const { return m_cacheAllowed; }
  void setCacheAllowed(bool val) { m_cacheAllowed = val; }
  bool lineOffsetsAsComments() const { return m_lineOffsetsAsComments; }
  SymbolId getCacheDir() const { return m_cacheDirId; }
  SymbolId getPrecompiledDir() const { return m_precompiledDirId; }
  bool usePPOutputFileLocation() const { return m_ppOutputFileLocation; }
  /* PP Output content generation options */
  bool filterFileLine() const { return m_filterFileLine; }
  void setFilterFileLine(bool val) { m_filterFileLine = val; }
  bool filterSimpleDirectives() const { return m_filterSimpleDirectives; }
  bool filterProtectedRegions() const { return m_filterProtectedRegions; }
  bool filterComments() const { return m_filterComments; }
  /* error reporting options */
  bool filterInfo() const { return !m_info; }
  bool filterNote() const { return !m_note; }
  bool filterWarning() const { return !m_warning; }
  void setFilterInfo() { m_info = false; }
  void setFilterNote() { m_note = false; }
  void setFilterWarning() { m_warning = false; }
  void setReportNonSynthesizable(bool report) { m_nonSynthesizable = report; }
  bool reportNonSynthesizable() { return m_nonSynthesizable; }
  /* Debug/traces options */
  bool muteStdout() const { return m_muteStdout; }
  void setMuteStdout() { m_muteStdout = true; }
  bool verbose() const { return m_verbose; }
  bool profile() const { return m_profile; }
  int getDebugLevel() const { return m_debugLevel; }
  bool getDebugAstModel() const { return m_debugAstModel; }
  bool getDebugUhdm() const { return m_dumpUhdm; }
  bool getUhdmStats() const { return m_uhdmStats; }
  bool getElabUhdm() const { return m_elabUhdm; }
  bool getCoverUhdm() const { return m_coverUhdm; }
  bool getParametersSubstitution() const { return m_parametersubstitution; }
  bool showVpiIds() const { return m_showVpiIDs; }
  bool replay() const { return m_replay; }
  bool getDebugInstanceTree() const { return m_debugInstanceTree; }
  bool getDebugLibraryDef() const { return m_debugLibraryDef; }
  bool getDebugIncludeFileInfo() const { return m_debugIncludeFileInfo; }
  bool help() const { return m_help; }
  void logBanner(int argc, const char** argv);
  void logFooter();
  static const std::string& getVersionNumber();
  /* Core functions options */
  bool parse() const { return m_parse; }
  bool parseOnly() const { return m_parseOnly; }
  bool lowMem() const { return m_lowMem; }
  bool compile() const { return m_compile; }
  bool elaborate() const { return m_elaborate; }
  bool writeUhdm() const { return m_writeUhdm; }
  void setParse(bool val) { m_parse = val; }
  void setParseOnly(bool val) { m_parseOnly = val; }
  void setLowMem(bool val) { m_lowMem = val; }
  void setCompile(bool val) { m_compile = val; }
  void setElaborate(bool val) { m_elaborate = val; }
  void setElabUhdm(bool val) {
    m_elaborate = val;
    m_elabUhdm = val;
  }
  void setWriteUhdm(bool val) { m_writeUhdm = val; }
  void setParametersSubstitution(bool val) { m_parametersubstitution = val; }
  bool pythonListener() const { return m_pythonListener && m_pythonAllowed; }
  bool pythonAllowed() const { return m_pythonAllowed; }
  void noPython() { m_pythonAllowed = false; }
  void withPython();
  bool pythonEvalScriptPerFile() const {
    return m_pythonEvalScriptPerFile && m_pythonAllowed;
  }
  bool pythonEvalScript() const {
    return m_pythonEvalScript && m_pythonAllowed;
  }
  SymbolId pythonEvalScriptPerFileId() const {
    return m_pythonEvalScriptPerFileId;
  }
  SymbolId pythonEvalScriptId() const { return m_pythonEvalScriptId; }
  SymbolId pythonListenerId() const { return m_pythonListenerFileId; }
  const SymbolTable& getSymbolTable() const { return *m_symbolTable; }

  // There are some places that modify the command-line symbol table.
  SymbolTable* mutableSymbolTable() const { return m_symbolTable; }

  /* Internal */
  ErrorContainer* getErrorContainer() const { return m_errors; }
  unsigned short int getNbMaxTreads() const { return m_nbMaxTreads; }
  unsigned short int getNbMaxProcesses() const { return m_nbMaxProcesses; }
  void setNbMaxTreads(unsigned short int max) { m_nbMaxTreads = max; }
  void setNbMaxProcesses(unsigned short int max) { m_nbMaxProcesses = max; }
  unsigned int getNbLinesForFileSpliting() const {
    return m_nbLinesForFileSplitting;
  }
  bool useTbb() const { return m_useTbb; }
  std::string getTimeScale() const { return m_timescale; }
  bool createCache() const { return m_createCache; }
  const std::string currentDateTime();
  bool parseBuiltIn();
  std::filesystem::path getBuiltInPath() const { return m_builtinPath; }
  std::filesystem::path getExePath() const { return m_exePath; }
  std::string getExeCommand() const { return m_exeCommand; }
  std::set<std::string>& getTopLevelModules() { return m_topLevelModules; }
  bool fullSVMode() const { return m_sverilog; }
  void fullSVMode(bool sverilog) { m_sverilog = sverilog; }
  bool isSVFile(const std::filesystem::path& fileName) const;
  bool cleanCache();

 private:
  CommandLineParser(const CommandLineParser& orig) = delete;

  bool plus_arguments_(const std::string& s);
  void processArgs_(std::vector<std::string>& args,
                    std::vector<std::string>& container);
  void splitPlusArg_(const std::string& s, const std::string& prefix,
                     std::vector<SymbolId>& container);
  void splitPlusArg_(const std::string& s, const std::string& prefix,
                     std::map<SymbolId, std::string>& container);
  bool checkCommandLine_();
  bool prepareCompilation_(int argc, const char** argv);
  bool setupCache_();

  std::vector<SymbolId> m_libraryPaths;             // -y
  std::vector<SymbolId> m_sourceFiles;              // .v .sv
  std::set<std::filesystem::path> m_svSourceFiles;  // user forced sv files
  std::vector<SymbolId> m_libraryFiles;             // -v
  std::vector<SymbolId> m_includePaths;             // +incdir+
  std::set<SymbolId> m_includePathSet;
  std::vector<SymbolId> m_libraryExtensions;     // +libext+
  std::vector<SymbolId> m_orderedLibraries;      // -L <libName>
  std::vector<SymbolId> m_libraryMapFiles;       // -map
  std::vector<SymbolId> m_configFiles;           // -cfgFile <config file>
  std::vector<SymbolId> m_useConfigs;            // -cfg <configName>
  std::map<SymbolId, std::string> m_defineList;  // +define+
  std::map<SymbolId, std::string> m_paramList;   // -Pparameter=value
  SymbolId m_writePpOutputFileId;
  bool m_writePpOutput;
  bool m_filterFileLine;
  int m_debugLevel;
  ErrorContainer* m_errors;
  SymbolTable* m_symbolTable;
  SymbolId m_logFileId;
  bool m_lineOffsetsAsComments;
  bool m_liborder;
  bool m_librescan;
  bool m_libverbose;
  bool m_nolibcell;
  bool m_muteStdout;
  bool m_verbose;
  bool m_fileunit;
  bool m_filterSimpleDirectives;
  bool m_filterProtectedRegions;
  bool m_filterComments;
  bool m_parse;
  bool m_parseOnly;
  bool m_compile;
  bool m_elaborate;
  bool m_parametersubstitution;
  bool m_diff_comp_mode;
  bool m_help;
  bool m_cacheAllowed;
  unsigned short int m_nbMaxTreads;
  unsigned short int m_nbMaxProcesses;
  SymbolId m_compileUnitDirectory;
  SymbolId m_compileAllDirectory;
  SymbolId m_outputDir;
  SymbolId m_fullCompileDir;
  SymbolId m_defaultLogFileId;
  SymbolId m_defaultCacheDirId;
  SymbolId m_cacheDirId;
  SymbolId m_precompiledDirId;
  bool m_note;
  bool m_info;
  bool m_warning;
  bool m_pythonListener;
  bool m_debugAstModel;
  bool m_debugInstanceTree;
  bool m_debugLibraryDef;
  bool m_useTbb;
  bool m_pythonAllowed;
  unsigned int m_nbLinesForFileSplitting;
  std::string m_timescale;
  bool m_pythonEvalScriptPerFile;
  bool m_pythonEvalScript;
  SymbolId m_pythonEvalScriptPerFileId;
  SymbolId m_pythonEvalScriptId;
  SymbolId m_pythonListenerFileId;
  bool m_debugIncludeFileInfo;
  bool m_createCache;
  bool m_profile;
  bool m_parseBuiltIn;
  bool m_ppOutputFileLocation;
  bool m_logFileSpecified;
  std::filesystem::path m_builtinPath;
  std::filesystem::path m_exePath;
  std::string m_exeCommand;
  std::set<std::string> m_topLevelModules;
  bool m_sverilog;
  bool m_dumpUhdm;
  bool m_elabUhdm;
  bool m_coverUhdm;
  bool m_showVpiIDs;
  bool m_replay;
  bool m_uhdmStats;
  bool m_lowMem;
  bool m_writeUhdm;
  bool m_nonSynthesizable;
};

}  // namespace SURELOG

#endif /* SURELOG_COMMANDLINEPARSER_H */
