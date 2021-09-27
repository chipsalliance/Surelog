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

#ifndef COMMANDLINEPARSER_HPP
#define COMMANDLINEPARSER_HPP
#include <map>
#include <string>
#include <vector>

#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/SymbolTable.h"

namespace SURELOG {

class CommandLineParser final {
 public:
  CommandLineParser(ErrorContainer* errors, SymbolTable* symbolTable,
                    bool diff_comp_mode = false, bool fileUnit = false);
  bool parseCommandLine(int argc, const char** argv);

  /* Verilog command line content */
  const std::vector<SymbolId>& getLibraryPaths() { return m_libraryPaths; }
  const std::vector<SymbolId>& getSourceFiles() { return m_sourceFiles; }
  const std::vector<SymbolId>& getLibraryFiles() { return m_libraryFiles; }
  const std::vector<SymbolId>& getLibraryExtensions() {
    return m_libraryExtensions;
  }
  const std::vector<SymbolId>& getIncludePaths() { return m_includePaths; }
  const std::vector<SymbolId>& getOrdredLibraries() {
    return m_orderedLibraries;
  }
  const std::vector<SymbolId>& getLibraryMapFiles() {
    return m_libraryMapFiles;
  }
  const std::vector<SymbolId>& getConfigFiles() { return m_configFiles; }
  const std::vector<SymbolId>& getUseConfigs() { return m_useConfigs; }
  const std::map<SymbolId, std::string>& getDefineList() {
    return m_defineList;
  }
  const std::map<SymbolId, std::string>& getParamList() { return m_paramList; }
  bool fileunit() { return m_fileunit; }  // File or all compilation semantic
  void setFileUnit() { m_fileunit = true; }
  /* PP Output file/dir options */
  SymbolId writePpOutputFileId() { return m_writePpOutputFileId; }
  SymbolId getOutputDir() { return m_outputDir; }
  SymbolId getCompileAllDir() { return m_compileAllDirectory; }
  SymbolId getCompileUnitDir() { return m_compileUnitDirectory; }
  SymbolId getCompileDir() {
    return fileunit() ? m_compileUnitDirectory : m_compileAllDirectory;
  }
  SymbolId getFullCompileDir() { return m_fullCompileDir; }
  SymbolId getLogFileId() { return m_logFileId; }
  SymbolId getDefaultLogFileId() { return m_defaultLogFileId; }
  bool writePpOutput() { return m_writePpOutput; }
  void setwritePpOutput(bool value) { m_writePpOutput = value; }
  bool cacheAllowed() { return m_cacheAllowed; }
  void setCacheAllowed(bool val) { m_cacheAllowed = val; }
  bool lineOffsetsAsComments() { return m_lineOffsetsAsComments; }
  SymbolId getCacheDir() { return m_cacheDirId; }
  SymbolId getPrecompiledDir() { return m_precompiledDirId; }
  bool usePPOutputFileLocation() { return m_ppOutputFileLocation; }
  /* PP Output content generation options */
  bool filterFileLine() { return m_filterFileLine; }
  void setFilterFileLine(bool val) { m_filterFileLine = val; }
  bool filterSimpleDirectives() { return m_filterSimpleDirectives; }
  bool filterProtectedRegions() { return m_filterProtectedRegions; }
  bool filterComments() { return m_filterComments; }
  bool filterInfo() { return !m_info; }
  bool filterNote() { return !m_note; }
  bool filterWarning() { return !m_warning; }
  void setFilterInfo() { m_info = false; }
  void setFilterNote() { m_note = false; }
  void setFilterWarning() { m_warning = false; }
  /* Debug/traces options */
  bool muteStdout() { return m_muteStdout; }
  void setMuteStdout() { m_muteStdout = true; }
  bool verbose() { return m_verbose; }
  bool profile() { return m_profile; }
  int getDebugLevel() { return m_debugLevel; }
  bool getDebugAstModel() { return m_debugAstModel; }
  bool getDebugUhdm() { return m_dumpUhdm; }
  bool getUhdmStats() { return m_uhdmStats; }
  bool getElabUhdm() { return m_elabUhdm; }
  bool getCoverUhdm() { return m_coverUhdm; }
  bool getParametersSubstitution() { return m_parametersubstitution; }
  bool showVpiIds() { return m_showVpiIDs; }
  bool replay() { return m_replay; }
  bool getDebugInstanceTree() { return m_debugInstanceTree; }
  bool getDebugLibraryDef() { return m_debugLibraryDef; }
  bool getDebugIncludeFileInfo() { return m_debugIncludeFileInfo; }
  bool help() { return m_help; }
  void logBanner(int argc, const char** argv);
  void logFooter();
  static const std::string& getVersionNumber();
  /* Core functions options */
  bool parse() { return m_parse; }
  bool parseOnly() { return m_parseOnly; }
  bool lowMem() { return m_lowMem; }
  bool compile() { return m_compile; }
  bool elaborate() { return m_elaborate; }
  bool writeUhdm() { return m_writeUhdm; }
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
  bool pythonListener() { return m_pythonListener && m_pythonAllowed; }
  bool pythonAllowed() { return m_pythonAllowed; }
  void noPython() { m_pythonAllowed = false; }
  void withPython();
  bool pythonEvalScriptPerFile() {
    return m_pythonEvalScriptPerFile && m_pythonAllowed;
  }
  bool pythonEvalScript() { return m_pythonEvalScript && m_pythonAllowed; }
  SymbolId pythonEvalScriptPerFileId() { return m_pythonEvalScriptPerFileId; }
  SymbolId pythonEvalScriptId() { return m_pythonEvalScriptId; }
  SymbolId pythonListenerId() { return m_pythonListenerFileId; }
  const SymbolTable& getSymbolTable() const { return *m_symbolTable; }

  // There are some places that modify the command-line symbol table.
  SymbolTable* mutableSymbolTable() { return m_symbolTable; }

  /* Internal */
  ErrorContainer* getErrorContainer() { return m_errors; }
  unsigned short int getNbMaxTreads() { return m_nbMaxTreads; }
  unsigned short int getNbMaxProcesses() { return m_nbMaxProcesses; }
  void setNbMaxTreads(unsigned short int max) { m_nbMaxTreads = max; }
  void setNbMaxProcesses(unsigned short int max) { m_nbMaxProcesses = max; }
  unsigned int getNbLinesForFileSpliting() { return m_nbLinesForFileSplitting; }
  bool useTbb() { return m_useTbb; }
  std::string getTimeScale() { return m_timescale; }
  bool createCache() { return m_createCache; }
  const std::string currentDateTime();
  bool parseBuiltIn();
  std::string getBuiltInPath() { return m_builtinPath; }
  std::string getExePath() { return m_exePath; }
  std::string getExeCommand() { return m_exeCommand; }
  std::set<std::string>& getTopLevelModules() { return m_topLevelModules; }
  bool fullSVMode() const { return m_sverilog; }
  bool isSVFile(const std::string& fileName) const;
  bool cleanCache();

 private:
  CommandLineParser(const CommandLineParser& orig) = delete;

  bool plus_arguments_(const std::string& s);
  void processArgs_(std::vector<std::string>& args,
                    std::vector<std::string>& container);
  void splitPlusArg_(std::string s, std::string prefix,
                     std::vector<SymbolId>& container);
  void splitPlusArg_(std::string s, std::string prefix,
                     std::map<SymbolId, std::string>& container);
  bool checkCommandLine_();
  bool prepareCompilation_(int argc, const char** argv);
  bool setupCache_();

  std::vector<SymbolId> m_libraryPaths;          // -y
  std::vector<SymbolId> m_sourceFiles;           // .v .sv
  std::set<std::string> m_svSourceFiles;         // user forced sv files
  std::vector<SymbolId> m_libraryFiles;          // -v
  std::vector<SymbolId> m_includePaths;          // +incdir+
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
  std::string m_builtinPath;
  std::string m_exePath;
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
};

}  // namespace SURELOG

#endif /* COMMANDLINEPARSER_HPP */
