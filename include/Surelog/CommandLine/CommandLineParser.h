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

#include <Surelog/Common/PathId.h>
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
                    bool diffCompMode = false, bool fileUnit = false);
  bool parseCommandLine(int32_t argc, const char** argv);

  /* Verilog command line content */
  const PathIdVector& getWorkingDirs() const { return m_workingDirs; }
  const PathIdVector& getLibraryPaths() const { return m_libraryPaths; }
  const PathIdVector& getSourceFiles() const { return m_sourceFiles; }
  const PathIdVector& getLibraryFiles() const { return m_libraryFiles; }
  const SymbolIdVector& getLibraryExtensions() const {
    return m_libraryExtensions;
  }
  const PathIdVector& getIncludePaths() const { return m_includePaths; }
  const PathIdVector& getOrdredLibraries() const { return m_orderedLibraries; }
  const PathIdVector& getLibraryMapFiles() const { return m_libraryMapFiles; }
  const PathIdVector& getConfigFiles() const { return m_configFiles; }
  const SymbolIdVector& getUseConfigs() const { return m_useConfigs; }
  const std::map<SymbolId, std::string, SymbolIdLessThanComparer>&
  getDefineList() const {
    return m_defineList;
  }
  const std::map<SymbolId, std::string, SymbolIdLessThanComparer>&
  getParamList() const {
    return m_paramList;
  }
  bool fileunit() const {
    return m_fileUnit;
  }  // File or all compilation semantic
  void setFileUnit() { m_fileUnit = true; }
  /* PP Output file/dir options */
  PathId writePpOutputFileId() const { return m_writePpOutputFileId; }
  PathId getOutputDirId() const { return m_outputDirId; }
  PathId getCompileAllDirId() const { return m_compileAllDirId; }
  PathId getCompileUnitDirId() const { return m_compileUnitDirId; }
  PathId getCompileDirId() const {
    return fileunit() ? m_compileUnitDirId : m_compileAllDirId;
  }
  PathId getLogFileId() const { return m_logFileId; }
  SymbolId getLogFileNameId() const { return m_logFileNameId; }
  bool writePpOutput() const { return m_writePpOutput; }
  void setwritePpOutput(bool value) { m_writePpOutput = value; }
  bool cacheAllowed() const { return m_cacheAllowed; }
  bool writeCache() const { return m_writeCache; }
  bool precompiledCacheAllowed() const { return m_precompiledCacheAllowed; }
  bool debugCache() const { return m_debugCache; }
  void debugCache(bool on) { m_debugCache = on; }
  void noCacheHash(bool noCachePath) { m_noCacheHash = noCachePath; }
  bool noCacheHash() const { return m_noCacheHash; }
  void setCacheAllowed(bool val) { m_cacheAllowed = val; }
  void setWriteCache(bool val) { m_writeCache = val; }
  void setPrecompiledCacheAllowed(bool val) { m_precompiledCacheAllowed = val; }
  void setUsePPOutputFileLocation(bool val) { m_ppOutputFileLocation = val; }
  bool lineOffsetsAsComments() const { return m_lineOffsetsAsComments; }
  PathId getCacheDirId() const { return m_cacheDirId; }
  PathId getPrecompiledDirId() const { return m_precompiledDirId; }
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
  void setReportNonSynthesizableWithFormal(bool report) {
    m_nonSynthesizableWithFormal = report;
  }
  bool reportNonSynthesizableWithFormal() {
    return m_nonSynthesizableWithFormal;
  }
  /* Debug/traces options */
  bool muteStdout() const { return m_muteStdout; }
  void setMuteStdout() { m_muteStdout = true; }
  bool verbose() const { return m_verbose; }
  bool profile() const { return m_profile; }
  int32_t getDebugLevel() const { return m_debugLevel; }
  bool getDebugAstModel() const { return m_debugAstModel; }
  bool getDebugUhdm() const { return m_dumpUhdm; }
  bool getUhdmStats() const { return m_uhdmStats; }
  bool getElabUhdm() const { return m_elabUhdm; }
  bool getCoverUhdm() const { return m_coverUhdm; }
  bool getParametersSubstitution() const { return m_parametersubstitution; }
  bool getLetExprSubstitution() const { return m_letexprsubstitution; }
  bool showVpiIds() const { return m_showVpiIDs; }
  bool replay() const { return m_replay; }
  bool getDebugInstanceTree() const { return m_debugInstanceTree; }
  bool getDebugLibraryDef() const { return m_debugLibraryDef; }
  bool getDebugIncludeFileInfo() const { return m_debugIncludeFileInfo; }
  bool help() const { return m_help; }
  void logBanner(int32_t argc, const char** argv);
  void logFooter();
  static std::string_view getVersionNumber();
  /* Core functions options */
  bool parse() const { return m_parse; }
  bool parseOnly() const { return m_parseOnly; }
  bool lowMem() const { return m_lowMem; }
  bool compile() const { return m_compile; }
  bool elaborate() const { return m_elaborate; }
  bool writeUhdm() const { return m_writeUhdm; }
  bool sepComp() const { return m_sepComp; }
  bool link() const { return m_link; }
  bool gc() const { return m_gc; }
  bool parseTree() const { return m_parseTree; }
  void setParse(bool val) { m_parse = val; }
  void setParseTree(bool val) { m_parseTree = val; }
  void setParseOnly(bool val) { m_parseOnly = val; }
  void setLowMem(bool val) { m_lowMem = val; }
  void setCompile(bool val) { m_compile = val; }
  void setElaborate(bool val) { m_elaborate = val; }
  void setSepComp(bool val) {
    m_sepComp = val;
    m_writePpOutput = val;
    m_parse = val;
    m_compile = false;
    m_elaborate = false;
    m_elabUhdm = false;
    m_writeUhdm = false;
    m_parseBuiltIn = false;
  }
  void setLink(bool val) {
    m_link = val;
    m_parse = val;
    m_compile = val;
    m_elaborate = val;
    m_writePpOutput = val;
  }
  void setElabUhdm(bool val) {
    m_elaborate = val;
    m_elabUhdm = val;
  }
  void setDebugUhdm(bool val) { m_dumpUhdm = val; }
  void setCoverUhdm(bool val) { m_coverUhdm = val; }
  void setWriteUhdm(bool val) { m_writeUhdm = val; }
  void setGC(bool val) { m_gc = val; }
  void showVpiIds(bool val) { m_showVpiIDs = val; }
  void setDebugAstModel(bool val) { m_debugAstModel = val; }
  void setParametersSubstitution(bool val) { m_parametersubstitution = val; }
  void setLetExprSubstitution(bool val) { m_letexprsubstitution = val; }
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
  PathId pythonEvalScriptPerFileId() const {
    return m_pythonEvalScriptPerFileId;
  }
  PathId pythonEvalScriptId() const { return m_pythonEvalScriptId; }
  PathId pythonListenerId() const { return m_pythonListenerFileId; }

  // There are some places that modify the command-line symbol table.
  SymbolTable* getSymbolTable() { return m_symbolTable; }
  const SymbolTable* getSymbolTable() const { return m_symbolTable; }

  /* Internal */
  ErrorContainer* getErrorContainer() const { return m_errors; }
  uint16_t getNbMaxTreads() const { return m_nbMaxTreads; }
  uint16_t getNbMaxProcesses() const { return m_nbMaxProcesses; }
  void setNbMaxTreads(uint16_t max) { m_nbMaxTreads = max; }
  void setNbMaxProcesses(uint16_t max) { m_nbMaxProcesses = max; }
  uint32_t getNbLinesForFileSpliting() const {
    return m_nbLinesForFileSplitting;
  }
  bool useTbb() const { return m_useTbb; }
  std::string getTimeScale() const { return m_timescale; }
  bool createCache() const { return m_createCache; }
  std::string currentDateTime();
  bool parseBuiltIn() const { return m_parseBuiltIn; }
  PathId getProgramId() const { return m_programId; }
  std::string getExeCommand() const { return m_exeCommand; }
  std::set<std::string, std::less<>>& getTopLevelModules() {
    return m_topLevelModules;
  }
  std::set<std::string, std::less<>>& getBlackBoxModules() {
    return m_blackboxModules;
  }
  std::set<std::string, std::less<>>& getBlackBoxInstances() {
    return m_blackboxInstances;
  }
  void setTopLevelModule(std::string_view module) {
    m_topLevelModules.emplace(module);
  }
  void setBlackBoxModule(std::string_view module) {
    m_blackboxModules.emplace(module);
  }
  void setBlackBoxInstance(std::string_view instance) {
    m_blackboxInstances.emplace(instance);
  }

  bool fullSVMode() const { return m_sverilog; }
  void fullSVMode(bool sverilog) { m_sverilog = sverilog; }
  bool isSVFile(PathId fileId) const;
  bool cleanCache();

 private:
  CommandLineParser(const CommandLineParser& orig) = delete;

  std::pair<PathId, std::filesystem::path> addWorkingDirectory_(
      const std::filesystem::path& wd, const std::filesystem::path& rwd);
  bool plus_arguments_(std::string_view s, const std::filesystem::path& cd);
  void processOutputDirectory_(const std::vector<std::string>& args);
  void processArgs_(const std::vector<std::string>& args,
                    std::filesystem::path& wd, std::filesystem::path& cd,
                    std::vector<std::string>& container);
  void splitPlusArg_(std::string_view s, std::string_view prefix,
                     SymbolIdVector& container);
  void splitPlusArg_(std::string_view s, std::string_view prefix,
                     const std::filesystem::path& cd, PathIdVector& container);
  void splitPlusArg_(
      std::string_view s, std::string_view prefix,
      std::map<SymbolId, std::string, SymbolIdLessThanComparer>& container);
  void splitEqArg_(
      std::string_view s,
      std::map<SymbolId, std::string, SymbolIdLessThanComparer>& container);
  bool checkCommandLine_();
  bool prepareCompilation_(int32_t argc, const char** argv);
  bool setupCache_();

  PathIdVector m_workingDirs;
  PathIdVector m_libraryPaths;  // -y
  PathIdVector m_sourceFiles;   // .v .sv
  PathIdSet m_svSourceFiles;    // user forced sv files
  PathIdVector m_libraryFiles;  // -v
  PathIdVector m_includePaths;  // +incdir+
  PathIdSet m_includePathSet;
  SymbolIdVector m_libraryExtensions;  // +libext+
  PathIdVector m_orderedLibraries;     // -L <libName>
  PathIdVector m_libraryMapFiles;      // -map
  PathIdVector m_configFiles;          // -cfgFile <config file>
  SymbolIdVector m_useConfigs;         // -cfg <configName>
  std::map<SymbolId, std::string, SymbolIdLessThanComparer>
      m_defineList;  // +define+
  std::map<SymbolId, std::string, SymbolIdLessThanComparer>
      m_paramList;  // -Pparameter=value
  PathId m_writePpOutputFileId;
  bool m_writePpOutput;
  bool m_filterFileLine;
  int32_t m_debugLevel;
  ErrorContainer* m_errors = nullptr;
  SymbolTable* m_symbolTable = nullptr;
  PathId m_logFileId;
  SymbolId m_logFileNameId;
  bool m_lineOffsetsAsComments;
  bool m_liborder;
  bool m_librescan;
  bool m_libverbose;
  bool m_nolibcell;
  bool m_muteStdout;
  bool m_verbose;
  bool m_fileUnit;
  bool m_filterSimpleDirectives;
  bool m_filterProtectedRegions;
  bool m_filterComments;
  bool m_parse;
  bool m_parseOnly;
  bool m_compile;
  bool m_elaborate;
  bool m_parametersubstitution;
  bool m_letexprsubstitution;
  bool m_diffCompMode;
  bool m_parseTree;
  bool m_help;
  bool m_cacheAllowed;
  bool m_writeCache;
  bool m_precompiledCacheAllowed;
  bool m_debugCache;
  bool m_debugFSConfig;
  uint16_t m_nbMaxTreads;
  uint16_t m_nbMaxProcesses;
  PathId m_compileUnitDirId;
  PathId m_compileAllDirId;
  PathId m_outputDirId;
  PathId m_cacheDirId;
  PathId m_precompiledDirId;
  bool m_note;
  bool m_info;
  bool m_warning;
  bool m_pythonListener;
  bool m_debugAstModel;
  bool m_debugInstanceTree;
  bool m_debugLibraryDef;
  bool m_useTbb;
  bool m_pythonAllowed;
  uint32_t m_nbLinesForFileSplitting;
  std::string m_timescale;
  bool m_pythonEvalScriptPerFile;
  bool m_pythonEvalScript;
  PathId m_pythonEvalScriptPerFileId;
  PathId m_pythonEvalScriptId;
  PathId m_pythonListenerFileId;
  bool m_debugIncludeFileInfo;
  bool m_createCache;
  bool m_profile;
  bool m_parseBuiltIn;
  bool m_ppOutputFileLocation;
  PathId m_programId;
  std::string m_exeCommand;
  std::set<std::string, std::less<>> m_topLevelModules;
  std::set<std::string, std::less<>> m_blackboxModules;
  std::set<std::string, std::less<>> m_blackboxInstances;
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
  bool m_nonSynthesizableWithFormal;
  bool m_noCacheHash;
  bool m_sepComp;
  bool m_link;
  bool m_gc;
};

}  // namespace SURELOG

#endif /* SURELOG_COMMANDLINEPARSER_H */
