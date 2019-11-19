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
 * File:   CommandLineParser.cpp
 * Author: alain
 *
 * Created on January 26, 2017, 9:47 PM
 */
#include <string>
#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <sys/types.h>
#include <sys/stat.h>
#include "CommandLine/CommandLineParser.hpp"
#include "Utils/StringUtils.h"
#include "Utils/FileUtils.h"

#include "antlr4-runtime.h"
using namespace antlr4;

#include "API/PythonAPI.h"

#include <ctime>
#include <thread>

using namespace SURELOG;

std::string defaultLogFileName = "surelog.log";
std::string CommandLineParser::m_versionNumber = "1.00";

const std::vector<std::string> copyright = {
    "Copyright (c) 2017-2019 Alain Dargelas,",
    "http://www.apache.org/licenses/LICENSE-2.0"};

const std::vector<std::string> banner = {
    "********************************************",
    "*  SURELOG System Verilog Compiler/Linter  *",
    "********************************************",
};

const std::vector<std::string> footer = {
    "********************************************",
    "*   End SURELOG SVerilog Compiler/Linter   *",
    "********************************************",
};

const std::vector<std::string> helpText = {
    "  ------------ SURELOG HELP --------------", "",
    "STANDARD VERILOG COMMAND LINE:",
    "  -f <file>             Accepts a file containing command line arguments",
    "  -v <file>             Library file",
    "  -y <path>             Library directory",
    "  +incdir+<dir>[+<dir>...] Specifies include paths",
    "  -Idir                 Specifies include paths",
    "  +libext+<extname>+... Specifies the library extensions",
    "  <file>.v              Verilog File",
    "  <file>.sv             System Verilog File",
    "  +liborder             Lib Order option (ignored)",
    "  +librescan            Lib Rescan option (ignored)",
    "  +libverbose           Lib Verbose option (ignored)",
    "  +nolibcell            No Lib Cell option (ignored)",
    "  +define+<name>=<value>[+<name>=<value>...]",
    "                        Defines a macro and optionally its value",
    "  -L <libName>          Defines library compilation order",
    "  -map <mapFile>        Specifies a library mapping file (multiple -map "
    "options supported)",
    "  -cfgfile <confiFile>  Specifies a configuration file (multiple -cfgFile "
    "options supported)",
    "  -cfg <configName>     Specifies a configuration to use (multiple -cfg "
    "options supported)",
    "  -Dvar=value           Same as env var definition for -f files var substitution",
    "FLOWS OPTIONS:",
    "  -fileunit             Compiles each Verilog file as an independent",
    "                        compilation unit (under slpp_unit/ if -writepp "
    "used)",
    "  -diffcompunit         Compiles both all files as a whole unit and",
    "                        separate compilation units to perform diffs",
    "  -parse                Parse/Compile/Elaborate the files after "
    "pre-processing step",
    "  -nocomp               Turns off Compilation & Elaboration",
    "  -noelab               Turns off Elaboration",
    "  -pythonlistener       Enables the Parser Python Listener",
    "  -pythonlistenerfile <script.py> Specifies the AST python listener file",
    "  -pythonevalscriptperfile <script.py>  Eval the Python script on each "
    "source file (Multithreaded)",
    "  -pythonevalscript <script.py> Eval the Python script at the design "
    "level",
    "  -nopython             Turns off all Python features, including waivers",
    "  -strictpythoncheck    Turns on strict Python checks",
    "  -mt <nb_max_treads>   0 up to 512 max threads, 0 or 1 being single "
    "threaded,",
    "                        if \"max\" is given, the program will use one "
    "thread",
    "                        per core on the host",
    "  -split <line number>  Split files or modules larger than specified line "
    "number for multi thread compilation",
    "  -timescale=<timescale> Specifies the overall timescale",
    "  -nobuiltin            Do not parse SV builtin classes (array...)", "",
    "TRACES OPTIONS:",
    "  -d <int>              Debug <level> 1-4, lib, ast, inst, incl",
    "  -nostdout             Mutes Standard output",
    "  -verbose              Gives verbose processing information",
    "  -profile              Gives Profiling information",
    "  -l <file>             Specifies log file, default is surelog.log under "
    "output dir",
    "", "OUTPUT OPTIONS:",
    "  -odir <dir>           Specifies the output directory, default is ./",
    "  -writeppfile <file>   Writes out Preprocessor output in file",
    "                        (all compilation units will override this file)",
    "  -writepp              Writes out Preprocessor output (all compilation",
    "                        units will generate files under slpp_all/ or "
    "slpp_unit/)",
    "  -lineoffsetascomments Writes the preprocessor line offsets as comments "
    "as opposed as parser directives",
    "  -nocache              Default allows to create a cache for include "
    "files, this option prevents it",
    "  -cache <dir>          Specifies the cache directory, default is "
    "slpp_all/cache or slpp_unit/cache",
    "  -createcache          Create cache for precompiled packages",
    "  -filterdirectives     Filters out simple directives like",
    "                        `default_nettype in pre-processor's output",
    "  -filterprotected      Filters out protected regions in pre-processor's "
    "output",
    "  -filtercomments       Filters out comments in pre-processor's output",
    "  -outputlineinfo       Outputs SLline directives in pre-processor's "
    "output",
    "  -pploc                Output message location in terms of post "
    "preprocessor location",
    "  -noinfo               Filters out INFO messages",
    "  -nonote               Filters out NOTE messages",
    "  -nowarning            Filters out WARNING messages",
    "  -o <path>             Turns on all compilation stages, produces all ",
    "  -builtin <path>       Alternative path to builtin.sv, python/ and pkg/ dirs",        
    "outputs under that path",
    "  --help               This help",
    "  --version            Surelog version"
};

std::string printStringArray(const std::vector<std::string>& array) {
  std::string report;
  for (unsigned int i = 0; i < array.size(); i++) {
    report += array[i] + "\n";
  }
  report += "\n";
  return report;
}

const std::string CommandLineParser::currentDateTime() {
  time_t now = time(0);
  struct tm tstruct;
  char buf[80];
  tstruct = *localtime(&now);
  // Visit http://en.cppreference.com/w/cpp/chrono/c/strftime
  // for more information about date/time format
  strftime(buf, sizeof(buf), "%Y-%m-%d.%X", &tstruct);

  return buf;
}

void CommandLineParser::logBanner(int argc, const char** argv) {
  std::string banners = printStringArray(banner);
  std::string copyrights = printStringArray(copyright);
  m_errors->printToLogFile(banners);
  m_errors->printToLogFile(copyrights);
  std::string version = "VERSION: " + m_versionNumber +"\n" +
                        "BUILT  : " + std::string(__DATE__) + "\n";
  std::string date = "DATE   : " + currentDateTime() + "\n";
  std::string cmd = "COMMAND:";
  for (int i = 1; i < argc; i++) {
    cmd += std::string(" ") + argv[i];
  }
  cmd += "\n\n";
  m_errors->printToLogFile(version);
  m_errors->printToLogFile(date);
  m_errors->printToLogFile(cmd);
}

void CommandLineParser::logFooter() {
  std::string footers = "\n";
  footers += printStringArray(footer);
  m_errors->printToLogFile(footers);
}

CommandLineParser::CommandLineParser(ErrorContainer* errors,
                                     SymbolTable* symbolTable,
                                     bool diff_comp_mode, bool fileUnit)
    : m_writePpOutputFileId(0),
      m_writePpOutput(false),
      m_filterFileLine(true),
      m_debugLevel(0),
      m_errors(errors),
      m_symbolTable(symbolTable),
      m_lineOffsetsAsComments(false),
      m_liborder(false),
      m_librescan(false),
      m_libverbose(false),
      m_nolibcell(false),
      m_muteStdout(false),
      m_verbose(false),
      m_fileunit(fileUnit),
      m_filterSimpleDirectives(false),
      m_filterProtectedRegions(false),
      m_filterComments(false),
      m_parse(false),
      m_compile(false),
      m_elaborate(false),
      m_diff_comp_mode(diff_comp_mode),
      m_help(false),
      m_cacheAllowed(true),
      m_nbMaxTreads(0),
      m_fullCompileDir(0),
      m_cacheDirId(0),
      m_note(true),
      m_info(true),
      m_warning(true),
      m_pythonListener(false),
      m_debugAstModel(false),
      m_debugInstanceTree(false),
      m_debugLibraryDef(false),
      m_useTbb(false),
      m_pythonAllowed(true),
      m_nbLinesForFileSplitting(500),
      m_pythonEvalScriptPerFile(false),
      m_pythonEvalScript(false),
      m_pythonEvalScriptPerFileId(0),
      m_pythonEvalScriptId(0),
      m_pythonListenerFileId(0),
      m_debugIncludeFileInfo(false),
      m_createCache(false),
      m_profile(false),
      m_parseBuiltIn(true),
      m_ppOutputFileLocation(false),
      m_logFileSpecified(false) {
  m_errors->regiterCmdLine(this);
  m_logFileId = m_symbolTable->registerSymbol(defaultLogFileName);
  m_compileUnitDirectory = m_symbolTable->registerSymbol("slpp_unit/");
  m_compileAllDirectory = m_symbolTable->registerSymbol("slpp_all/");
  m_outputDir = m_symbolTable->registerSymbol("./");
  m_defaultLogFileId = m_symbolTable->registerSymbol(defaultLogFileName);
  m_defaultCacheDirId = m_symbolTable->registerSymbol("cache/");
  m_precompiledDirId = m_symbolTable->registerSymbol("pkg");
  if (m_diff_comp_mode) {
    m_muteStdout = true;
    m_verbose = false;
  }
}

CommandLineParser::CommandLineParser(const CommandLineParser& orig) {}

CommandLineParser::~CommandLineParser() {}

void CommandLineParser::splitPlusArg_(std::string s, std::string prefix,
                                      std::vector<SymbolId>& container) {
  std::istringstream f(s);
  std::string tmp;
  while (getline(f, tmp, '+')) {
    if (tmp.size() && (tmp != prefix)) {
      SymbolId id = m_symbolTable->registerSymbol(tmp);
      container.push_back(id);
    }
  }
}

void CommandLineParser::splitPlusArg_(
    std::string s, std::string prefix,
    std::map<SymbolId, std::string>& container) {
  std::istringstream f(s);
  std::string tmp;
  while (getline(f, tmp, '+')) {
    if (tmp.size() && (tmp != prefix)) {
      std::string def;
      std::string value;
      const size_t loc = tmp.find("=");
      if (loc == std::string::npos) {
        SymbolId id = m_symbolTable->registerSymbol(tmp);
        container.insert(std::make_pair(id, std::string()));
      } else {
        def = tmp.substr(0, loc);
        value = tmp.substr(loc + 1);
        SymbolId id = m_symbolTable->registerSymbol(def);
        container.insert(std::make_pair(id, value));
      }
    }
  }
}

/* Custom parser for +arguments */
bool CommandLineParser::plus_arguments_(const std::string& s) {
  std::string incdir("+incdir+");
  std::string libext("+libext+");
  std::string define("+define+");
  if (s.size() == 0) return false;
  if (s.at(0) != '+') return false;
  if (s.compare(0, incdir.size(), incdir) == 0) {
    splitPlusArg_(s, "incdir", m_includePaths);
    return true;
  }
  if (s.compare(0, libext.size(), libext) == 0) {
    splitPlusArg_(s, "libext", m_libraryExtensions);
    return true;
  }
  if (s.compare(0, define.size(), define) == 0) {
    splitPlusArg_(s, "define", m_defineList);
    return true;
  }
  return false;
}

void CommandLineParser::processArgs_(std::vector<std::string>& args,
                                     std::vector<std::string>& container) {
  for (unsigned int i = 0; i < args.size(); i++) {
    if (args[i] == "-f") {
      std::string f = args[i + 1];
      SymbolId fId = m_symbolTable->registerSymbol(f);
      std::ifstream ifs(f);
      if (!ifs) {
        Location loc(fId);
        Error err(ErrorDefinition::CMD_DASH_F_FILE_DOES_NOT_EXIST, loc);
        m_errors->addError(err);
      } else {
        std::stringstream ss;
        ss << ifs.rdbuf();
        ifs.close();
        std::string fileContent = ss.str();
        fileContent = StringUtils::removeComments(fileContent);
        fileContent = StringUtils::evaluateEnvVars (fileContent);
        std::vector<std::string> argsInFile;
        StringUtils::tokenize(fileContent, " \n\t\r", argsInFile);
        processArgs_(argsInFile, container);
      }
      i++;
    } else {
      container.push_back(args[i]);
    }
  }
}

int CommandLineParser::parseCommandLine(int argc, const char** argv) {
  std::string exe_name = argv[0];
  std::string exe_path = FileUtils::getPathName(exe_name);
  m_precompiledDirId = m_symbolTable->registerSymbol(exe_path + "pkg/");
  if (!FileUtils::fileExists(exe_path + "pkg/")) {
    if (FileUtils::fileExists("/usr/lib/surelog/pkg/")) {
      m_precompiledDirId = m_symbolTable->registerSymbol("/usr/lib/surelog/pkg/");   
    }
  if (FileUtils::fileExists("/usr/local/lib/surelog/pkg/")) {
      m_precompiledDirId = m_symbolTable->registerSymbol("/usr/local/lib/surelog/pkg/");   
    }
  }
  
  std::string built_in_verilog = exe_path + "/sv/builtin.sv";
  if (!FileUtils::fileExists(built_in_verilog)) {
    built_in_verilog = "/usr/lib/surelog/sv/builtin.sv";
    if (!FileUtils::fileExists("/usr/lib/surelog/sv/builtin.sv")) {
      built_in_verilog = "/usr/local/lib/surelog/sv/builtin.sv";   
    }
  }
  
  std::vector<std::string> all_arguments;
  std::vector<std::string> cmd_line;
  for (int i = 1; i < argc; i++) {
    cmd_line.push_back(argv[i]);
      if (!strcmp(argv[i], "-builtin")) {
          if (i < argc - 1) {
            m_builtinPath = argv[i + 1];
            built_in_verilog = m_builtinPath + "/builtin.sv";
          }
      } else if (!strcmp (argv[i], "-l"))
        {
          if (i < argc - 1)
            {
              m_logFileId = m_symbolTable->registerSymbol (argv[i + 1]);
              m_logFileSpecified = true;
            }
        }
      else if (strstr (argv[i], "-D"))
        {
          std::string def;
          std::string value;
          std::string tmp = argv[i];
          const size_t loc = tmp.find ("=");
          if (loc == std::string::npos)
            {
              StringUtils::registerEnvVar (def, "");
            }
          else
            {
              def = tmp.substr (2, loc - 2);
              value = tmp.substr (loc + 1);
              StringUtils::registerEnvVar (def, value);
            }
        }
    }
  processArgs_(cmd_line, all_arguments);
  for (unsigned int i = 0; i < all_arguments.size(); i++) {
    if (all_arguments[i] == "-help" || all_arguments[i] == "-h" || 
        all_arguments[i] == "--help") {
      m_help = true;
      std::string help = printStringArray(helpText);
      m_errors->init();
      logBanner(argc, argv);
      std::cout << help;
      return true;
    }
    if (all_arguments[i] == "--version") {
      std::string version = "VERSION: " + m_versionNumber +"\n" +
                        "BUILT  : " + std::string(__DATE__) + "\n";
      std::cout << version << std::flush;
      m_help = true;
      return true;
    }
    if (all_arguments[i] == "-nobuiltin") {
      m_parseBuiltIn = false;
    }
  }
  if (m_parseBuiltIn) {
    m_sourceFiles.push_back(m_symbolTable->registerSymbol(built_in_verilog));
  }
  for (unsigned int i = 0; i < all_arguments.size(); i++) {
    if (all_arguments[i] == "-fileunit") {
      if (m_diff_comp_mode == false)  // Controlled by constructor
        m_fileunit = true;
    } else if (all_arguments[i] == "-mutestdout") {
      m_muteStdout = true;
    } else if (all_arguments[i] == "-nopython") {
      m_pythonAllowed = false;
    }
  }

  for (unsigned int i = 0; i < all_arguments.size(); i++) {
    if (all_arguments[i] == "-odir" || all_arguments[i] == "-o") {
      if (i == all_arguments.size() - 1) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_PP_FILE_MISSING_ODIR, loc);
        m_errors->addError(err);
        break;
      }
      i++;
      m_outputDir = m_symbolTable->registerSymbol(all_arguments[i]);
    }
  }
  bool status = prepareCompilation_(argc, argv);
  if (!status) return status;

  for (unsigned int i = 0; i < all_arguments.size(); i++) {
    if (plus_arguments_(all_arguments[i])) {
    } else if (all_arguments[i] == "-d") {
      if (i == all_arguments.size() - 1) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_DEBUG_MISSING_LEVEL, loc);
        m_errors->addError(err);
        break;
      }
      i++;
      if (all_arguments[i] == "ast") {
        m_debugAstModel = true;
      } else if (all_arguments[i] == "inst") {
        m_debugInstanceTree = true;
      } else if (all_arguments[i] == "lib") {
        m_debugLibraryDef = true;
      } else if (all_arguments[i] == "incl") {
        m_debugIncludeFileInfo = true;
      } else {
        int debugLevel = atoi(all_arguments[i].c_str());
        if (debugLevel < 0 || debugLevel > 4) {
          Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
          Error err(ErrorDefinition::CMD_DEBUG_INCORRECT_LEVEL, loc);
          m_errors->addError(err);
        } else {
          m_debugLevel = debugLevel;
        }
      }
    } else if (strstr(all_arguments[i].c_str(), "-timescale=")) {
      std::string timescale;
      timescale = all_arguments[i].substr(11, std::string::npos);
      if (timescale == "") {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_TIMESCALE_MISSING_SETTING, loc);
        m_errors->addError(err);
        break;
      }
      m_timescale = timescale;
    } else if (strstr (all_arguments[i].c_str(), "-D")) {
    } else if (strstr(all_arguments[i].c_str(), "-I")) {
      std::string include;
      include = all_arguments[i].substr(2, std::string::npos);
      if (include == "") {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_INCLUDE_PATH_DOES_NOT_EXIST, loc);
        m_errors->addError(err);
        break;
      }
      m_includePaths.push_back(getSymbolTable()->registerSymbol(include));
    } else if (all_arguments[i] == "-split") {
      if (i == all_arguments.size() - 1) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_SPLIT_FILE_MISSING_SIZE, loc);
        m_errors->addError(err);
        break;
      }
      i++;
      m_nbLinesForFileSplitting = atoi(all_arguments[i].c_str());
    } else if (all_arguments[i] == "-mt") {
      if (i == all_arguments.size() - 1) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_MT_MISSING_LEVEL, loc);
        m_errors->addError(err);
        break;
      }
      i++;
      unsigned int maxMT = 0;
      if (all_arguments[i] == "max") {
        unsigned int concurentThreadsSupported =
            std::thread::hardware_concurrency();
        maxMT = concurentThreadsSupported;

      } else {
        maxMT = atoi(all_arguments[i].c_str());
      }
      if (maxMT < 0 || maxMT > 512) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_MT_INCORRECT_LEVEL, loc);
        m_errors->addError(err);
      } else {
        if (m_diff_comp_mode) {
          unsigned int concurentThreadsSupported =
              std::thread::hardware_concurrency();
          if (maxMT > (concurentThreadsSupported / 2))
            maxMT = (concurentThreadsSupported / 2);
        }

        if (maxMT == 0)
          m_nbMaxTreads = maxMT;
        else {
          m_nbMaxTreads = maxMT;
          if (m_nbMaxTreads < 2) m_nbMaxTreads = 2;
          Location loc(
              getSymbolTable()->registerSymbol(std::to_string(m_nbMaxTreads)));
          Error err(ErrorDefinition::CMD_NUMBER_THREADS, loc);
          m_errors->addError(err);
        }
      }
    } else if (all_arguments[i] == "-strictpythoncheck") {
      PythonAPI::setStrictMode(true);

    } else if (all_arguments[i] == "-tbb") {
      m_useTbb = true;

    } else if (all_arguments[i] == "-createcache") {
      m_createCache = true;
    } else if (all_arguments[i] == "-lineoffsetascomments") {
      m_lineOffsetsAsComments = true;
    } else if (all_arguments[i] == "-v") {
      if (i == all_arguments.size() - 1) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_LIBRARY_FILE_MISSING_FILE, loc);
        m_errors->addError(err);
        break;
      }
      i++;
      m_libraryFiles.push_back(m_symbolTable->registerSymbol(all_arguments[i]));
    } else if (all_arguments[i] == "-y") {
      if (i == all_arguments.size() - 1) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_LIBRARY_PATH_MISSING_PATH, loc);
        m_errors->addError(err);
        break;
      }
      i++;
      m_libraryPaths.push_back(m_symbolTable->registerSymbol(all_arguments[i]));
    } else if (all_arguments[i] == "-l") {
      if (i == all_arguments.size() - 1) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_LOG_FILE_MISSING_FILE, loc);
        m_errors->addError(err);
        break;
      }
      i++;
      m_logFileId = m_symbolTable->registerSymbol(all_arguments[i]);
      m_logFileSpecified = true;
    } else if (all_arguments[i] == "-L") {
      i++;
      m_orderedLibraries.push_back(
          m_symbolTable->registerSymbol(all_arguments[i]));
    } else if (all_arguments[i] == "-map") {
      i++;
      m_libraryMapFiles.push_back(
          m_symbolTable->registerSymbol(all_arguments[i]));
    } else if (all_arguments[i] == "-cfgfile") {
      i++;
      m_configFiles.push_back(m_symbolTable->registerSymbol(all_arguments[i]));
    } else if (all_arguments[i] == "-cfg") {
      i++;
      m_useConfigs.push_back(m_symbolTable->registerSymbol(all_arguments[i]));
    } else if (all_arguments[i] == "-writeppfile") {
      if (i == all_arguments.size() - 1) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_PP_FILE_MISSING_FILE, loc);
        m_errors->addError(err);
        break;
      }
      i++;
      m_writePpOutputFileId = m_symbolTable->registerSymbol(all_arguments[i]);
    } else if (all_arguments[i] == "-cache") {
      if (i == all_arguments.size() - 1) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_PP_FILE_MISSING_FILE, loc);
        m_errors->addError(err);
        break;
      }
      i++;
      m_cacheDirId = m_symbolTable->registerSymbol(all_arguments[i]);
    } else if (all_arguments[i] == "-writepp") {
      m_writePpOutput = true;
    } else if (all_arguments[i] == "-noinfo") {
      m_info = false;
    } else if (all_arguments[i] == "-nonote") {
      m_note = false;
    } else if (all_arguments[i] == "-nowarning") {
      m_warning = false;
    } else if (all_arguments[i] == "-profile") {
      m_profile = true;
    } else if (all_arguments[i] == "-nobuiltin") {
      m_parseBuiltIn = false;
    } else if (all_arguments[i] == "-outputlineinfo") {
      m_filterFileLine = false;
    } else if (all_arguments[i] == "+liborder") {
      m_liborder = true;
    } else if (all_arguments[i] == "+librescan") {
      m_librescan = true;
    } else if (all_arguments[i] == "+libverbose") {
      m_libverbose = true;
    } else if (all_arguments[i] == "+nolibcell") {
      m_nolibcell = true;
    } else if (all_arguments[i] == "-fileunit") {
      Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
      Error err(ErrorDefinition::CMD_SEPARATE_COMPILATION_UNIT_ON, loc);
      m_errors->addError(err);
    } else if (all_arguments[i] == "-diffcompunit") {
      if (m_fileunit) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_SEPARATE_COMPILATION_UNIT_ON, loc);
        m_errors->addError(err);
      }
    } else if (all_arguments[i] == "-odir") {
      i++;
    } else if (all_arguments[i] == "-o") {
      i++;
      m_writePpOutput = true;
      m_parse = true;
    } else if (all_arguments[i] == "-nostdout") {
      m_muteStdout = true;
    } else if (all_arguments[i] == "-verbose") {
      m_verbose = true;
    } else if (all_arguments[i] == "-filterdirectives") {
      m_filterSimpleDirectives = true;
    } else if (all_arguments[i] == "-filterprotected") {
      m_filterProtectedRegions = true;
    } else if (all_arguments[i] == "-filtercomments") {
      m_filterComments = true;
    } else if (all_arguments[i] == "-parse") {
      m_writePpOutput = true;
      m_parse = true;
      m_compile = true;
      m_elaborate = true;
    } else if (all_arguments[i] == "-nocomp") {
      m_compile = false;
      m_elaborate = false;
    } else if (all_arguments[i] == "-noelab") {
      m_elaborate = false;
    } else if (all_arguments[i] == "-pploc") {
      m_ppOutputFileLocation = true;
    } else if (all_arguments[i] == "-pythonlistener") {
      m_writePpOutput = true;
      m_parse = true;
      m_compile = true;
      m_elaborate = true;
      m_pythonListener = true;
      if (!PythonAPI::isListenerLoaded()) {
        Location loc(0);
        Error err(ErrorDefinition::PY_NO_PYTHON_LISTENER_FOUND, loc);
        m_errors->addError(err);
      }
      if (!m_pythonAllowed)
        std::cout << "ERROR: No Python allowed, check your arguments!\n";
    } else if (all_arguments[i] == "-nopython") {
      m_pythonAllowed = false;
    } else if (all_arguments[i] == "-pythonevalscriptperfile") {
      if (i == all_arguments.size() - 1) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_PP_FILE_MISSING_FILE, loc);
        m_errors->addError(err);
        break;
      }
      i++;
      m_writePpOutput = true;
      m_parse = true;
      m_compile = true;
      m_elaborate = true;
      m_pythonEvalScriptPerFile = true;
      m_pythonEvalScriptPerFileId =
          m_symbolTable->registerSymbol(all_arguments[i]);
      if (m_pythonAllowed)
        PythonAPI::loadScript(all_arguments[i], true);
      else
        std::cout << "ERROR: No Python allowed, check your arguments!\n";
    } else if (all_arguments[i] == "-pythonlistenerfile") {
      if (i == all_arguments.size() - 1) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_PP_FILE_MISSING_FILE, loc);
        m_errors->addError(err);
        break;
      }
      i++;
      m_writePpOutput = true;
      m_parse = true;
      m_compile = true;
      m_elaborate = true;
      m_pythonListener = true;
      m_pythonListenerFileId = m_symbolTable->registerSymbol(all_arguments[i]);
      PythonAPI::setListenerScript(all_arguments[i]);
    } else if (all_arguments[i] == "-pythonevalscript") {
      if (i == all_arguments.size() - 1) {
        Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
        Error err(ErrorDefinition::CMD_PP_FILE_MISSING_FILE, loc);
        m_errors->addError(err);
        break;
      }
      i++;
      m_writePpOutput = true;
      m_parse = true;
      m_compile = true;
      m_elaborate = true;
      m_pythonEvalScript = true;
      m_pythonEvalScriptId = m_symbolTable->registerSymbol(all_arguments[i]);
      if (m_pythonAllowed)
        PythonAPI::loadScript(all_arguments[i], true);
      else
        std::cout << "ERROR: No Python allowed, check your arguments!\n";
    } else if (all_arguments[i] == "-nocache") {
      m_cacheAllowed = false;
    } else if (all_arguments[i].size() && all_arguments[i].at(0) == '+') {
      Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
      Error err(ErrorDefinition::CMD_PLUS_ARG_IGNORED, loc);
      m_errors->addError(err);
    } else if (all_arguments[i].size() && all_arguments[i].at(0) == '-') {
      Location loc(getSymbolTable()->registerSymbol(all_arguments[i]));
      Error err(ErrorDefinition::CMD_MINUS_ARG_IGNORED, loc);
      m_errors->addError(err);
    } else {
      if (all_arguments[i] != "")
        m_sourceFiles.push_back(
            m_symbolTable->registerSymbol(all_arguments[i]));
    }
  }

  status = checkCommandLine_();
  return status;
}

bool CommandLineParser::checkCommandLine_() {
  bool noError = true;
  for (auto fid : m_sourceFiles) {
    if (!FileUtils::fileExists(m_symbolTable->getSymbol(fid))) {
      Location loc(fid);
      Error err(ErrorDefinition::CMD_VERILOG_FILE_DOES_NOT_EXIST, loc);
      m_errors->addError(err);
      noError = false;
    }
  }
  for (auto fid : m_libraryPaths) {
    if (!FileUtils::fileExists(m_symbolTable->getSymbol(fid))) {
      Location loc(fid);
      Error err(ErrorDefinition::CMD_LIBRARY_PATH_DOES_NOT_EXIST, loc);
      m_errors->addError(err);
    }
  }
  for (auto fid : m_libraryFiles) {
    if (!FileUtils::fileExists(m_symbolTable->getSymbol(fid))) {
      Location loc(fid);
      Error err(ErrorDefinition::CMD_LIBRARY_FILE_DOES_NOT_EXIST, loc);
      m_errors->addError(err);
      noError = false;
    }
  }
  for (auto fid : m_includePaths) {
    if (!FileUtils::fileExists(m_symbolTable->getSymbol(fid))) {
      Location loc(fid);
      Error err(ErrorDefinition::CMD_INCLUDE_PATH_DOES_NOT_EXIST, loc);
      m_errors->addError(err);
    }
  }
  if (!m_errors->printMessages(m_muteStdout)) {
    noError = false;
  }

  return noError;
}

bool CommandLineParser::prepareCompilation_(int argc, const char** argv) {
  bool noError = true;
  std::string odir = m_symbolTable->getSymbol(m_outputDir);
  if (odir.size()) {
    if (odir[odir.size() - 1] != '/') {
      odir += '/';
    }
  }

  odir += m_symbolTable->getSymbol(
      (fileunit() ? m_compileUnitDirectory : m_compileAllDirectory));
  m_fullCompileDir = m_symbolTable->registerSymbol(odir);

  if (!m_logFileSpecified)
    m_logFileId = m_symbolTable->registerSymbol(odir + defaultLogFileName);

  std::string cachedir;
  if (m_cacheAllowed) {
    if (m_cacheDirId == 0) {
      cachedir = odir + m_symbolTable->getSymbol(m_defaultCacheDirId);
      m_cacheDirId = m_symbolTable->registerSymbol(cachedir);
    } else {
      cachedir = m_symbolTable->getSymbol(m_cacheDirId);
    }
  }

  int status = FileUtils::mkDir(odir.c_str());
  if (status != 0) {
    Location loc(m_fullCompileDir);
    Error err(ErrorDefinition::CMD_PP_CANNOT_CREATE_OUTPUT_DIR, loc);
    m_errors->addError(err);
    noError = false;
  }

  m_errors->init();
  logBanner(argc, argv);
  Location loc(m_logFileId);
  Error err(ErrorDefinition::CMD_CREATING_LOG_FILE, loc);
  m_errors->addError(err);

  if (m_cacheAllowed) {
    status = FileUtils::mkDir(cachedir.c_str());
    if (status != 0) {
      Location loc(m_cacheDirId);
      Error err(ErrorDefinition::CMD_PP_CANNOT_CREATE_CACHE_DIR, loc);
      m_errors->addError(err);
      noError = false;
    }
  }

  if (m_errors->hasFatalErrors()) {
    noError = false;
  }

  return noError;
}
