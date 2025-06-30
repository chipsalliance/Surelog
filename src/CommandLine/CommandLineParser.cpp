/*
 Copyright 2017-2022 Alain Dargelas

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

#include "Surelog/CommandLine/CommandLineParser.h"

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <map>
#include <nlohmann/json.hpp>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>
#include <vector>

#include "Surelog/API/PythonAPI.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/PlatformFileSystem.h"
#include "Surelog/Common/Session.h"
#include "Surelog/Common/SymbolId.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/Utils/StringUtils.h"
#include "Surelog/surelog-version.h"

#if defined(_MSC_VER)
#include <direct.h>
#endif

#include <cstring>
#include <iostream>
#include <thread>

namespace SURELOG {
namespace fs = std::filesystem;

constexpr uint32_t kLinesForFileSplitting = 10000000;

static std::unordered_map<std::string, int32_t>
    cmd_ignore;  // commands with an arg to be dropped, and the number of args
                 // to drop
static std::unordered_map<std::string, std::string>
    cmd_rename;  // commands to be renamed (no args)
static std::unordered_map<std::string, std::string>
    cmd_merge;  // commands to be merged into 1 argument

// !!! Update this number when the grammar changes !!!
//         Or when the cache schema changes
//        This will render the cache invalid
std::string_view CommandLineParser::getVersionNumber() {
#define VSTRINGIFY(x) #x
#define VERSION_STRING(major, minor) VSTRINGIFY(major) "." VSTRINGIFY(minor)
  // Defined in CMakeList.txt in project() call.
  static constexpr std::string_view kVersionNumber(
      VERSION_STRING(SURELOG_VERSION_MAJOR, SURELOG_VERSION_MINOR));
#undef VERSION_STRING
#undef VSTRINGIFY
  return kVersionNumber;
}

static const std::initializer_list<std::string_view> copyright = {
    "Copyright (c) 2017-2023 Alain Dargelas,",
    "http://www.apache.org/licenses/LICENSE-2.0"};

static const std::initializer_list<std::string_view> banner = {
    "********************************************",
    "*  SURELOG SystemVerilog  Compiler/Linter  *",
    "********************************************",
};

static const std::initializer_list<std::string_view> footer = {
    "********************************************",
    "*   End SURELOG SVerilog Compiler/Linter   *",
    "********************************************",
};

static const std::initializer_list<std::string_view> helpText = {
    "  ------------ SURELOG HELP --------------",
    "",
    "STANDARD VERILOG COMMAND LINE:",
    "  -f <file>             Accepts a file containing command line arguments",
    "  -v <file>             Library file",
    "  -y <path>             Library directory",
    "  +incdir+<dir>[+<dir>...]",
    "                        Specifies include paths",
    "  -Idir                 Specifies include paths",
    "  +libext+<extname>+... Specifies the library extensions, ",
    "                        default is .v+.sv",
    "  <file>.v              Verilog File",
    "  <file>.sv             SystemVerilog File",
    "  +liborder             Lib Order option (ignored)",
    "  +librescan            Lib Rescan option (ignored)",
    "  +libverbose           Lib Verbose option (ignored)",
    "  +nolibcell            No Lib Cell option (ignored)",
    "  +define+<name>=<value>[+<name>=<value>...]",
    "                        Defines a macro and optionally its value",
    "  -L <libName>          Defines library compilation order",
    "  -map <mapFile>        Specifies a library mapping file (multiple -map",
    "                        options supported)",
    "  -cfgfile <confiFile>  Specifies a configuration file (multiple",
    "                        -cfgFile options supported)",
    "  -cfg <configName>     Specifies a configuration to use (multiple -cfg",
    "                        options supported)",
    "  -Dvar=value           Same as env var definition for -f files var",
    "                        substitution",
    "  -Pparameter=value     Top level parameter override",
    "  -pvalue+parameter=value",
    "                        Top level parameter override",
    "  -sverilog/-sv         Forces all files to be parsed as SystemVerilog",
    "                        files",
    "  -sv <file>            Forces the following file to be parsed as",
    "                        SystemVerilog file",
    "",
    "EDA TOOLS COMPATIBILITY OPTIONS:",
    "  -cmd_ign <cmd> <argc>    Ignore <cmd> when encountered and drop <argc>",
    "                           arguments",
    "  -cmd_ren <flag1> <flag2> Rename <flag1> into <flag2> when encountered",
    "  -cmd_mrg <flag1> <flag2> Merge <flag1> argument into a unified <flag2>",
    "                           '+' argument when encountered",
    "",
    "FLOWS OPTIONS:",
    "  -fileunit             Compiles each Verilog file as an independent",
    "                        compilation unit (under slpp_unit/ if -writepp",
    "                        used)",
    "  -diffcompunit         Compiles both all files as a whole unit and",
    "                        separate compilation units to perform diffs",
    "  -parse                Parse/Compile/Elaborate the files after",
    "                        pre-processing step",
    "  -noparse              Turns off Parsing & Compilation & Elaboration",
    "  -nocomp               Turns off Compilation & Elaboration",
    "  -noelab               Turns off Elaboration",
    "  -noreduce             Turns off reduction",
    "  -parseonly            Only Parses, reloads Preprocessor saved db",
    "  -init                 Initialize cache for separate compile flow",
    "                        (-sepcomp, -link)",
    "  -sepcomp              Separate compilation, each invocation creates a",
    "                        compilation unit",
    "  -link                 Link and elaborate the separately compiled files",
    "  -elabuhdm             Forces UHDM/VPI Full Elaboration, default is the",
    "                        Folded Model",
    "  -nouhdm               No UHDM db write",
    "  -top/--top-module <module>",
    "                        Top level module for elaboration",
    "                        (multiple cmds ok)",
    "  -bb_mod <module>      Blackbox module (multiple cmds ok, ex: -bb_mod",
    "                        work@top)",
    "  -bb_inst <instance>   Blackbox instance (multiple cmds ok, ex:",
    "                        -bb_inst work@top.u1)",
    "  -batch <batch.txt>    Runs all the tests specified in the file in",
    "                        batch mode. Tests are expressed as one full",
    "                        command line per line.",
    "  --enable-feature=<feature>",
    "  --disable-feature=<feature>",
    "    Features: parametersubstitution Enables substitution of assignment",
    "                                    patterns in parameters",
    "              letexprsubstitution   Enables Let expr substitution",
    "                                    (Inlining)",
#ifdef SURELOG_WITH_PYTHON
    "  -pythonlistener       Enables the Parser Python Listener",
    "  -pythonlistenerfile <script.py>",
    "                        Specifies the AST python listener file",
    "  -pythonevalscriptperfile <script.py>",
    "                        Eval the Python script on each source file",
    "                        (Multithreaded)",
    "  -pythonevalscript <script.py>",
    "                        Eval the Python script at the design level",
    "  -nopython             Turns off all Python features, including waivers",
    "  -withpython           Turns on all Python features, including waivers",
    "  -strictpythoncheck    Turns on strict Python checks",
#endif
    "  -mt/--threads <nb_max_threads>",
    "                        0 up to 512 max threads, 0 or 1 being single",
    "                        threaded, if \"max\" is given, the program will",
    "                        use one thread per core on the host",
    "  -mp <mb_max_process>  0 up to 512 max processes, 0 or 1 being single",
    "                        process",
    "  -lowmem               Minimizes memory high water mark (uses multiple",
    "                        staggered processes for preproc, parsing and",
    "                        elaboration)",
    "  -split <line number>  Split files or modules larger than specified",
    "                        line number for multi thread compilation",
    "  -timescale=<timescale>",
    "                        Specifies the overall timescale",
    "  -nobuiltin            Do not parse SV builtin classes (array...)",
    "",
    "TRACES OPTIONS:",
    "  -d <int|tag>          Debug <level> 1-4, lib, ast, inst, incl, uhdm,",
    "                        cache, coveruhdm, vpi_ids, fsconfig",
    "  -nostdout             Mutes Standard output",
    "  -verbose              Gives verbose processing information",
    "  -profile              Gives Profiling information",
    "  -replay               Enables replay of internal elaboration errors",
    "  -l <filename>         Specifies log file name, default is surelog.log",
    "",
    "OUTPUT OPTIONS:",
    "  -odir/--Mdir <dir>    Specifies the output directory, default is ./",
    "  -writeppfile <file>   Writes out Preprocessor output in file",
    "                        (all compilation units will override this file)",
    "  -writepp              Writes out Preprocessor output (all compilation",
    "                        units will generate files under slpp_all/ or",
    "                        slpp_unit/)",
    "  -lineoffsetascomments Writes the preprocessor line offsets as comments",
    "                        as opposed as parser directives",
    "  -nocache              Default allows to read cache for include files,",
    "                        this option prevents it",
    "  -noprecompiledcache   Default allows to read precompiled cache, this",
    "                        option prevents it",
    "  -nowritecache         Default allows writing cache, this option",
    "                        prevents it",
    "  -cache <dir>          Specifies the cache directory, default is",
    "                        slpp_all/cache or slpp_unit/cache",
    "  -nohash               Treat cache as always valid (no",
    "                        timestamp/dependancy check)",
    "  -createcache          Create cache for precompiled packages",
    "  -filterdirectives     Filters out simple directives like",
    "                        `default_nettype in pre-processor's output",
    "  -filterprotected      Filters out protected regions in pre-processor's",
    "                        output",
    "  -filtercomments       Filters out comments in pre-processor's output",
    "  -outputlineinfo       Outputs SLline directives in pre-processor's",
    "                        output",
    "  -pploc                Output message location in terms of post",
    "                        preprocessor location",
    "  -ppextra_loc          Adds pre-processor location to syntax errors",
    "  -noinfo               Filters out INFO messages",
    "  -nonote               Filters out NOTE messages",
    "  -nowarning            Filters out WARNING messages",
    "  -synth                Reports non-synthesizable constructs. Honors",
    "                        // pragma translate_off",
    "                        // pragma translate_on",
    "  -formal               Reports non-synthesizable constructs like -synth,",
    "                        but still allows model checking constructs",
    "  -o <path>             Turns on all compilation stages, produces all",
    "  -builtin <path>       Alternative path to python/ and pkg/ dirs",
    "                        outputs under that path",
    "  -wd <dir>             Internally change directory to <dir>. Relative",
    "                        paths are w.r.t. FileSystem's working directory.",
    "                        All following relative paths using -cd option are",
    "                        w.r.t.this directory.Defaults to the current",
    "                        working directory.",
    "  -cd <dir>             Internally change directory to <dir>. This should",
    "                        only be relative and is w.r.t.to last - wd",
    "                        option.",
    "  -remap <what> <with>  When loading cache, source paths can be remapped",
    "                        from<what> to<with>.Use it to relocate sources",
    "                        and still use pregenerated cache. Both <what> and",
    "                        <with> are expected to be absolute paths.",
    "  -exe <command>        Post execute a system call <command>, passes it",
    "                        the preprocessor file list.",
    "  -gc                   Enable garbage collection during save.",
    "  -nogc                 Disable garbage collection during save.",
    "  --help                This help",
    "  --version             Surelog version",
    "",
    "RETURN CODE:",
    "   Bit mask the return code, more than 1 bit can be on.",
    "   0   - No issues",
    "   0x1 - Fatal error(s)",
    "   0x2 - Syntax error(s)",
    "   0x4 - Error(s)",
    "",
    "NOTES:",
    "  -wd/-cd : Working directory & current directory options work in pairs.",
    "            Relative working directory arguments should be relative to",
    "            FileSystem's working directory and relative current",
    "            directory arguments should be relative to the last working",
    "            directory argument. Multiple series of -wd / -cd are",
    "            supported. Working directory arguments are also used to",
    "            compute the absolute root (all sources, includes, libraries,",
    "            etc are under this absolute root) for the FileSystem (which",
    "            in turn is used to organize the output directory)."};

static bool is_number(const std::string_view s) {
  return s.find_first_not_of("-.0123456789") == std::string_view::npos;
}

static bool is_c_file(const std::string_view s) {
  const std::string_view ext = StringUtils::leaf(s);
  return (ext == "c" || ext == "cpp" || ext == "cc");
}

static std::string printStringArray(
    const std::initializer_list<std::string_view>& all_strings) {
  std::string report;
  for (std::string_view s : all_strings) {
    report.append(s).append("\n");
  }
  report += "\n";
  return report;
}

void CommandLineParser::withPython() {
#ifdef SURELOG_WITH_PYTHON
  m_pythonAllowed = true;
#endif
}

std::string CommandLineParser::currentDateTime() {
  time_t now = time(nullptr);
  struct tm tstruct = *localtime(&now);
  // Visit http://en.cppreference.com/w/cpp/chrono/c/strftime
  // for more information about date/time format
  char buf[80] = {'\0'};
  strftime(buf, sizeof(buf), "%Y-%m-%d.%X", &tstruct);
  return buf;
}

static std::string BuildIdentifier() {
  return StrCat("VERSION: ", CommandLineParser::getVersionNumber(),
                "\nBUILT  : ", __DATE__, "\n");
}

void CommandLineParser::logBanner(int32_t argc, const char** argv) {
  ErrorContainer* const errors = m_session->getErrorContainer();

  std::string banners = printStringArray(banner);
  std::string copyrights = printStringArray(copyright);
  errors->printToLogFile(banners);
  errors->printToLogFile(copyrights);
  const std::string version = BuildIdentifier();
  const std::string date = "DATE   : " + currentDateTime() + "\n";
  std::string cmd = "COMMAND:";
  for (int32_t i = 1; i < argc; i++) {
    cmd += std::string(" ") + argv[i];
  }
  cmd += "\n\n";
  errors->printToLogFile(version);
  errors->printToLogFile(date);
  errors->printToLogFile(cmd);
}

void CommandLineParser::logFooter() {
  std::string footers = "\n";
  footers += printStringArray(footer);
  m_session->getErrorContainer()->printToLogFile(footers);
}

CommandLineParser::CommandLineParser(Session* session)
    : m_session(session),
      m_writePpOutput(false),
      m_filterFileLine(true),
      m_debugLevel(0),
      m_lineOffsetsAsComments(false),
      m_libOrder(false),
      m_libRescan(false),
      m_libVerbose(false),
      m_noLibCell(false),
      m_muteStdout(false),
      m_verbose(false),
      m_fileUnit(false),
      m_filterSimpleDirectives(false),
      m_filterProtectedRegions(false),
      m_filterComments(false),
      m_parse(false),
      m_parseOnly(false),
      m_compile(false),
      m_elaborate(false),
      m_parameterSubstitution(true),
      m_letExprSubstitution(true),
      m_diffCompMode(false),
      m_parseTree(false),
      m_help(false),
      m_cacheAllowed(true),
      m_writeCache(true),
      m_precompiledCacheAllowed(true),
      m_debugCache(false),
      m_debugFSConfig(false),
      m_maxTreads(0),
      m_maxProcesses(0),
      m_note(true),
      m_info(true),
      m_warning(true),
      m_pythonListener(false),
      m_debugAstModel(false),
      m_debugInstanceTree(false),
      m_debugLibraryDef(false),
      m_useTbb(false),
#ifdef SURELOG_WITH_PYTHON
      m_pythonAllowed(true),
#else
      m_pythonAllowed(false),
#endif
      m_linesForFileSplitting(kLinesForFileSplitting),
      m_pythonEvalScriptPerFile(false),
      m_pythonEvalScript(false),
      m_debugIncludeFileInfo(false),
      m_createCache(false),
      m_profile(false),
      m_parseBuiltIn(true),
      m_ppOutputFileLocation(false),
      m_ppPrintLineInfo(false),
      m_sverilog(false),
      m_dumpUhdm(false),
      m_elabUhdm(false),
      m_coverUhdm(false),
      m_showVpiIDs(false),
      m_replay(false),
      m_uhdmStats(false),
      m_lowMem(false),
      m_writeUhdm(true),
      m_nonSynthesizable(false),
      m_nonSynthesizableWithFormal(false),
      m_noCacheHash(false),
      m_sepComp(false),
      m_link(false),
      m_gc(true),
      m_disableLineMarkings(false),
      m_reduce(true) {
  m_libraryExtensions.emplace_back(
      m_session->getSymbolTable()->registerSymbol(".v"));  // default
}

// Undecorate command line arg by removing any space, single-quotes,
// and/or double-quotes at the front or at the back
static std::string_view undecorateArg(std::string_view arg) {
  // Strip out any null terminators
  while (!arg.empty() && (arg.front() == '\0')) arg.remove_prefix(1);
  while (!arg.empty() && (arg.back() == '\0')) arg.remove_suffix(1);

  // Strip out any space character at front and back
  while (!arg.empty() && std::isspace(arg.front())) arg.remove_prefix(1);
  while (!arg.empty() && std::isspace(arg.back())) arg.remove_suffix(1);

  // Remove any surrounding quotes
  if ((arg.size() > 1) && (((arg.front() == '\"') && (arg.back() == '\"')) ||
                           ((arg.front() == '\'') && (arg.back() == '\'')))) {
    arg.remove_prefix(1);
    arg.remove_suffix(1);

    arg = undecorateArg(arg);
  }

  return arg;
}

std::pair<PathId, fs::path> CommandLineParser::addWorkingDirectory_(
    const fs::path& wd, const fs::path& rcd) {
  FileSystem* const fileSystem = m_session->getFileSystem();
  SymbolTable* const symbols = m_session->getSymbolTable();

  const fs::path cwd =
      FileSystem::normalize(rcd.is_relative() ? wd / rcd : rcd);

  if (rcd.is_absolute()) {
    fileSystem->getWorkingDir(rcd.string(), symbols);
  } else {
    fs::path bwd = wd;
    for (const fs::path& p : cwd.lexically_relative(wd)) {
      if (p == "..") {
        bwd = bwd.parent_path();
      } else {
        break;
      }
    }

    if (wd != bwd) {
      fileSystem->getWorkingDir(bwd.string(), symbols);
    }
  }

  const PathId cwdId = fileSystem->toPathId(cwd.string(), symbols);
  m_workingDirs.emplace_back(cwdId);
  return {cwdId, fileSystem->toPath(cwdId)};
}

void CommandLineParser::splitPlusArg_(std::string_view s,
                                      std::string_view prefix,
                                      SymbolIdVector& container) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  std::istringstream f((std::string(s)));
  std::string tmp;
  while (std::getline(f, tmp, '+')) {
    if (!tmp.empty() && (tmp != prefix)) {
      SymbolId id = symbols->registerSymbol(tmp);
      container.push_back(id);
    }
  }
}

void CommandLineParser::splitEqArg_(
    std::string_view s,
    std::map<SymbolId, std::string, SymbolIdLessThanComparer>& container) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  std::string def;
  std::string value;
  const size_t loc = s.find('=');
  if (loc == std::string::npos) {
    def = s;
  } else {
    def = s.substr(0, loc);
    value = s.substr(loc + 1);
  }
  if (!def.empty()) {
    SymbolId id = symbols->registerSymbol(def);
    container.emplace(id, value);
  }
}

void CommandLineParser::splitPlusArg_(std::string_view s,
                                      std::string_view prefix,
                                      const fs::path& cd,
                                      PathIdVector& container) {
  std::istringstream f((std::string(s)));
  std::string tmp;
  while (std::getline(f, tmp, '+')) {
    if (!tmp.empty() && (tmp != prefix)) {
      container.emplace_back(std::get<0>(addWorkingDirectory_(cd, tmp)));
    }
  }
}

void CommandLineParser::splitPlusArg_(
    std::string_view s, std::string_view prefix,
    std::map<SymbolId, std::string, SymbolIdLessThanComparer>& container) {
  std::istringstream f((std::string(s)));
  std::string tmp;
  while (std::getline(f, tmp, '+')) {
    if (!tmp.empty() && (tmp != prefix)) {
      splitEqArg_(tmp, container);
    }
  }
}

/* Custom parser for +arguments */
bool CommandLineParser::plus_arguments_(std::string_view s,
                                        const fs::path& cd) {
  constexpr std::string_view incdir("+incdir+");
  constexpr std::string_view libext("+libext+");
  constexpr std::string_view define("+define+");
  if (s.empty()) return false;
  if (s.at(0) != '+') return false;
  if (s.compare(0, incdir.size(), incdir) == 0) {
    PathIdVector includePathIds;
    splitPlusArg_(s, "incdir", cd, includePathIds);

    for (const PathId& includeId : includePathIds) {
      if (m_includePathSet.find(includeId) == m_includePathSet.end()) {
        m_includePathSet.emplace(includeId);
        m_includePaths.emplace_back(includeId);
      }
    }

    return true;
  }
  if (s.compare(0, libext.size(), libext) == 0) {
    // Do not reset m_libraryExtensions, multiple arguments can be used
    splitPlusArg_(s, "libext", m_libraryExtensions);
    return true;
  }
  if (s.compare(0, define.size(), define) == 0) {
    splitPlusArg_(s, "define", m_defineList);
    return true;
  }
  return false;
}

void CommandLineParser::processArgs_(const std::vector<std::string>& args,
                                     fs::path& wd, fs::path& cd,
                                     std::vector<std::string>& container) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errors = m_session->getErrorContainer();

  for (const std::string& arg : args) {
    if (arg.find("-D") == 0) {
      std::string def;
      std::string value;
      const size_t loc = arg.find('=');
      if (loc == std::string::npos) {
        def = arg.substr(2);
      } else {
        def = arg.substr(2, loc - 2);
        value = arg.substr(loc + 1);
      }
      if (!def.empty()) {
        StringUtils::registerEnvVar(def, value);
        SymbolId id = symbols->registerSymbol(def);
        m_defineList.emplace(id, value);
      }
    }
  }

  for (uint32_t i = 0; i < args.size(); i++) {
    std::string arg(undecorateArg(args[i]));
    if (arg == "-cmd_ign") {
      // ignore command and drop <N> following arguments
      if (i < args.size() - 2) {
        const int32_t argcount = std::stoi(args[i + 2]);
        if (argcount < 0 || argcount > 100) {  // just a sane limit
          std::cerr << "Illegal argument count for -cmd_ign (" << args[i + 2]
                    << ")" << std::endl;
          return;
        }
        cmd_ignore[args[i + 1]] = argcount;
        i += 2;  // also skip the two arguments
      } else {
        std::cerr << "Missing arguments to -cmd_ign " << std::endl;
        return;
      }
      continue;
    } else if (arg == "-cmd_ren") {
      if (i < args.size() - 2) {
        cmd_rename[args[i + 1]] = args[i + 2];
        i += 2;  // also skip two arguments
      } else {
        std::cerr << "Missing arguments to -cmd_ren " << std::endl;
        return;
      }
      continue;
    } else if (arg == "-cmd_mrg") {
      if (i < args.size() - 2) {
        cmd_merge[args[i + 1]] = args[i + 2];
        i += 2;  // also skip two arguments
      } else {
        std::cerr << "Missing arguments to -cmd_mrg " << std::endl;
        return;
      }
      continue;
    }
    auto cmd_ignore_it = cmd_ignore.find(arg);
    if (cmd_ignore_it != cmd_ignore.end()) {
      // found arg in list of commands to be ignored
      if (i < args.size() - cmd_ignore_it->second) {
        i += cmd_ignore_it->second;
      } else {
        std::cerr << "Missing arguments to ignored command " << arg
                  << std::endl;
      }
      continue;
    }
    auto cmd_rename_it = cmd_rename.find(arg);
    if (cmd_rename_it != cmd_rename.end()) {
      // arg found in rename list
      arg = cmd_rename_it->second;
    }
    auto cmd_merge_it = cmd_merge.find(arg);
    if (cmd_merge_it != cmd_merge.end()) {
      if (i < args.size() - 1) {
        arg = cmd_merge_it->second;
        arg.append("+");
        arg.append(args[i + 1]);
        i += 1;
      } else {
        std::cerr << "Missing arguments to renamed command " << arg
                  << std::endl;
        return;
      }
    }
    if (arg == "-wd") {
      if (i == args.size() - 1) {
        Location loc(symbols->registerSymbol(args[i]));
        errors->addError(ErrorDefinition::CMD_WD_MISSING_DIR, loc);
        break;
      }
      fs::path rwd = undecorateArg(args[++i]);
      container.emplace_back(arg);
      container.emplace_back(rwd.string());
      wd = cd = rwd.is_relative() ? fileSystem->getWorkingDir() / rwd : rwd;
    } else if (arg == "-cd") {
      if (i == args.size() - 1) {
        Location loc(symbols->registerSymbol(args[i]));
        errors->addError(ErrorDefinition::CMD_CD_MISSING_DIR, loc);
        break;
      }
      std::string_view rcd = undecorateArg(args[++i]);
      container.emplace_back(arg);
      container.emplace_back(rcd);
      cd = wd / rcd;
    } else if (arg == "-f") {
      if (i == args.size() - 1) {
        Location loc(symbols->registerSymbol(args[i]));
        errors->addError(ErrorDefinition::CMD_DASH_F_FILE_DOES_NOT_EXIST, loc);
        break;
      } else {
        fs::path fp = undecorateArg(args[++i]);
        if (fp.is_relative()) fp = cd / fp;
        PathId fId = fileSystem->toPathId(fp.string(), symbols);
        std::string fileContent;
        if (fileSystem->readContent(fId, fileContent)) {
          fileContent = StringUtils::removeComments(fileContent);
          fileContent = StringUtils::evaluateEnvVars(fileContent);
          std::vector<std::string> argsInFile;
          StringUtils::tokenize(fileContent, " \n\t\r", argsInFile);
          processArgs_(argsInFile, wd, cd, container);
        } else {
          Location loc(fId);
          errors->addError(ErrorDefinition::CMD_DASH_F_FILE_DOES_NOT_EXIST,
                           loc);
          break;
        }
      }
    } else if (arg == "-link") {
      m_parse = true;
      m_compile = true;
      m_elaborate = true;
      m_writePpOutput = true;
      m_link = true;
      PathId compileDirId = fileSystem->getCompileDir(m_fileUnit, symbols);
      PathIdVector fileList;
      fileSystem->collect(compileDirId, ".sepcmd.json", symbols, fileList);
      for (const auto& fileId : fileList) {
        nlohmann::json fileContent;
        std::istream& ifs = fileSystem->openForRead(fileId);
        if (ifs.good()) ifs >> fileContent;
        fileSystem->close(ifs);

        for (const auto& entry : fileContent["sources"]) {
          const std::string baseDirectory = entry["base_directory"];
          const std::string relativeFilepath = entry["relative_filepath"];
          fileSystem->addWorkingDirectoryCacheEntry(baseDirectory,
                                                    relativeFilepath);

          std::filesystem::path absFilepath =
              std::filesystem::path(baseDirectory) / relativeFilepath;
          container.emplace_back(absFilepath.string());
        }
      }
    } else if (!arg.empty()) {
      container.emplace_back(arg);
    }
  }
}

void CommandLineParser::processOutputDirectory_(
    const std::vector<std::string>& args) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errors = m_session->getErrorContainer();

  fs::path wd = fileSystem->getWorkingDir();
  for (size_t i = 0; i < args.size(); i++) {
    std::string arg(undecorateArg(args[i]));

    if (arg == "-wd") {
      if (i == args.size() - 1) {
        Location loc(symbols->registerSymbol(args[i]));
        errors->addError(ErrorDefinition::CMD_WD_MISSING_DIR, loc);
        break;
      }
      fs::path rwd = undecorateArg(args[++i]);
      wd = rwd.is_relative() ? fileSystem->getWorkingDir() / rwd : rwd;
    } else if (arg == "-odir" || arg == "-o" || arg == "--Mdir") {
      if (i == args.size() - 1) {
        Location loc(symbols->registerSymbol(args[i]));
        errors->addError(ErrorDefinition::CMD_PP_FILE_MISSING_ODIR, loc);
        break;
      }

      fs::path outputDir = undecorateArg(args[++i]);
      if (outputDir.is_relative()) outputDir = wd / outputDir;
      m_outputDirId = fileSystem->getOutputDir(outputDir.string(), symbols);
    } else if (arg == "-l") {
      if (i == args.size() - 1) {
        Location loc(symbols->registerSymbol(arg));
        errors->addError(ErrorDefinition::CMD_LOG_FILE_MISSING_FILE, loc);
        break;
      }
      m_logFileNameId = symbols->registerSymbol(undecorateArg(args[++i]));
    }
  }
}

bool CommandLineParser::parse(int32_t argc, const char** argv,
                              bool diffCompMode /* = false */,
                              bool fileUnit /* = false */) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errors = m_session->getErrorContainer();

  m_diffCompMode = diffCompMode;
  m_fileUnit = fileUnit;
  if (m_diffCompMode) {
    m_muteStdout = true;
    m_verbose = false;
  }

  std::string pname = argv[0];
  if (pname == "read_systemverilog") {
    // When surelog is embedded as a plugin in yosys, the program name is
    // "read_systemverilog", which breaks the -lowmem option
    pname = "surelog";
    std::filesystem::path programPath = FileSystem::getProgramPath();
    programPath = programPath.parent_path();
    programPath = programPath / pname;
    m_programId = fileSystem->toPathId(programPath.string(), symbols);
  } else {
    m_programId = fileSystem->getProgramFile(pname, symbols);
  }
  std::vector<std::string> cmd_line;
  for (int32_t i = 1; i < argc; i++) {
    cmd_line.emplace_back(undecorateArg(argv[i]));
    const std::string& arg = cmd_line.back();

    if (arg.empty() || (arg[0] != '-')) {
      continue;
    } else if (arg == "-help" || arg == "-h" || arg == "--help") {
      m_help = true;
      std::string help = printStringArray(helpText);
      errors->init();
      logBanner(argc, argv);
      std::cout << help;
      return true;
    } else if (arg == "--version") {
      std::cout << BuildIdentifier() << std::flush;
      m_help = true;
      return true;
    } else if (arg == "-builtin") {
      ++i;  // Deprecated and ignored!
    } else if (arg.find("-D") == 0) {
      std::string def;
      std::string value;
      const size_t loc = arg.find('=');
      if (loc == std::string::npos) {
        def = arg.substr(2);
      } else {
        def = arg.substr(2, loc - 2);
        value = arg.substr(loc + 1);
      }
      if (!def.empty()) {
        StringUtils::registerEnvVar(def, value);
        SymbolId id = symbols->registerSymbol(def);
        m_defineList.emplace(id, value);
      }
    }
  }

  std::vector<std::string> all_arguments;
  processOutputDirectory_(cmd_line);

  // Setup a few dependent input & output directories
  if (!m_outputDirId) {
    m_outputDirId =
        fileSystem->getOutputDir(fileSystem->getWorkingDir(), symbols);
  }
  m_precompiledDirId = fileSystem->getPrecompiledDir(m_programId, symbols);
  m_compileUnitDirId = fileSystem->getCompileDir(true, symbols);
  m_compileAllDirId = fileSystem->getCompileDir(false, symbols);

  fs::path wd = fileSystem->getWorkingDir();
  fs::path cd = wd;
  processArgs_(cmd_line, wd, cd, all_arguments);

  /*
  std::string cmd = "EXPANDED CMD:";
  for (size_t i = 0; i < all_arguments.size(); i++) {
    cmd += std::string(" ") + all_arguments[i];
  }
  cmd += "\n\n";
  std::cout << cmd;
  */

  for (const auto& argument : all_arguments) {
    if (argument == "-nobuiltin") {
      m_parseBuiltIn = false;
    } else if (argument == "-fileunit") {
      if (!m_diffCompMode)  // Controlled by constructor
        m_fileUnit = true;
    } else if (argument == "-mutestdout") {
      m_muteStdout = true;
    } else if (argument == "-nopython") {
      m_pythonAllowed = false;
    } else if (argument == "-withpython") {
      withPython();
    }
  }
  bool status = prepareCompilation_(argc, argv);
  if (!status) return status;

  wd = cd = fileSystem->getWorkingDir();
  m_workingDirs.emplace_back(fileSystem->getWorkingDir(symbols));

  for (size_t i = 0; i < all_arguments.size(); i++) {
    if (all_arguments[i].empty() || plus_arguments_(all_arguments[i], cd)) {
      // handled by plus_arguments
    } else if (all_arguments[i] == "-wd") {
      if (i == all_arguments.size() - 1) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_WD_MISSING_DIR, loc);
        break;
      }
      fs::path dir = FileSystem::normalize(all_arguments[++i]);
      if (dir.is_relative()) dir = fileSystem->getWorkingDir() / dir;
      PathId dirId = fileSystem->getWorkingDir(dir.string(), symbols);
      m_workingDirs.emplace_back(dirId);
      wd = cd = fileSystem->toPath(dirId);
    } else if (all_arguments[i] == "-cd") {
      if (i == all_arguments.size() - 1) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_CD_MISSING_DIR, loc);
        break;
      }
      cd = std::get<1>(addWorkingDirectory_(wd, all_arguments[++i]));
    } else if (all_arguments[i] == "-remap") {
      Location loc(symbols->registerSymbol(all_arguments[i]));
      if ((i + 2) >= all_arguments.size()) {
        errors->addError(ErrorDefinition::CMD_REMAP_MISSING_DIRS, loc);
        break;
      }
      const fs::path what = FileSystem::normalize(all_arguments[++i]);
      const fs::path with = FileSystem::normalize(all_arguments[++i]);
      if (!what.is_absolute() || !with.is_absolute()) {
        errors->addError(ErrorDefinition::CMD_REMAP_MISSING_DIRS, loc);
        break;
      }
      fileSystem->addMapping(what.string(), with.string());
    } else if (all_arguments[i] == "-d") {
      if (i == all_arguments.size() - 1) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_DEBUG_MISSING_LEVEL, loc);
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
      } else if (all_arguments[i] == "uhdm") {
        m_dumpUhdm = true;
      } else if (all_arguments[i] == "uhdmstats") {
        m_uhdmStats = true;
      } else if (all_arguments[i] == "coveruhdm") {
        m_coverUhdm = true;
      } else if (all_arguments[i] == "cache") {
        m_debugCache = true;
      } else if (all_arguments[i] == "vpi_ids") {
        m_showVpiIDs = true;
      } else if (all_arguments[i] == "fsconfig") {
        m_debugFSConfig = true;
      } else if (all_arguments[i] == "coverelab") {
        // Ignored!
      } else if (is_number(all_arguments[i])) {
        int32_t debugLevel = std::stoi(all_arguments[i]);
        if (debugLevel < 0 || debugLevel > 4) {
          Location loc(symbols->registerSymbol(all_arguments[i]));
          errors->addError(ErrorDefinition::CMD_DEBUG_INCORRECT_LEVEL, loc);
        } else {
          m_debugLevel = debugLevel;
        }
      } else {
        std::cerr << "Option: " << all_arguments[i] << " ignored." << std::endl;
      }
    } else if (all_arguments[i].find("--enable-feature=") == 0) {
      std::string features = all_arguments[i].substr(17);
      std::istringstream f(features);
      std::string tmp;
      while (getline(f, tmp, ',')) {
        if (tmp == "parametersubstitution") {
          m_parameterSubstitution = true;
        } else if (tmp == "letexprsubstitution") {
          m_letExprSubstitution = true;
        } else {
          std::cerr << "Feature: " << tmp << " ignored." << std::endl;
        }
      }
    } else if (all_arguments[i].find("--disable-feature=") == 0) {
      std::string features = all_arguments[i].substr(18);
      std::istringstream f(features);
      std::string tmp;
      while (getline(f, tmp, ',')) {
        if (tmp == "parametersubstitution") {
          m_parameterSubstitution = false;
        } else if (tmp == "letexprsubstitution") {
          m_letExprSubstitution = false;
        } else {
          std::cerr << "Feature: " << tmp << " ignored." << std::endl;
        }
      }
    } else if (all_arguments[i].find("-timescale=") == 0) {
      std::string timescale = all_arguments[i].substr(11);
      if (timescale.empty()) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_TIMESCALE_MISSING_SETTING, loc);
        break;
      }
      m_timescale = timescale;
    } else if (all_arguments[i].find("-D") == 0) {
      std::string def;
      std::string value;
      const size_t loc = all_arguments[i].find('=');
      if (loc == std::string::npos) {
        def = all_arguments[i].substr(2);
      } else {
        def = all_arguments[i].substr(2, loc - 2);
        value = all_arguments[i].substr(loc + 1);
      }
      if (!def.empty()) {
        StringUtils::registerEnvVar(def, value);
        SymbolId id = symbols->registerSymbol(def);
        m_defineList.emplace(id, value);
      }
    } else if (all_arguments[i].find("-P") == 0) {
      std::string def;
      std::string value;
      const size_t loc = all_arguments[i].find('=');
      if (loc == std::string::npos) {
        def = all_arguments[i].substr(2);
      } else {
        def = all_arguments[i].substr(2, loc - 2);
        value = all_arguments[i].substr(loc + 1);
      }
      if (!def.empty()) {
        SymbolId id = symbols->registerSymbol(def);
        m_paramList.emplace(id, StringUtils::unquoted(value));
      }
    } else if (all_arguments[i].find("-pvalue+") == 0) {
      std::string def;
      std::string value;
      const size_t loc = all_arguments[i].find('=');
      if (loc == std::string::npos) {
        def = all_arguments[i].substr(8);
      } else {
        def = all_arguments[i].substr(8, loc - 8);
        value = all_arguments[i].substr(loc + 1);
      }
      if (!def.empty()) {
        SymbolId id = symbols->registerSymbol(def);
        m_paramList.emplace(id, StringUtils::unquoted(value));
      }
    } else if (all_arguments[i].find("-I") == 0) {
      fs::path include = undecorateArg(all_arguments[i].substr(2));
      if (include.empty()) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_INCLUDE_PATH_DOES_NOT_EXIST, loc);
        break;
      }
      PathId includeId = std::get<0>(addWorkingDirectory_(cd, include));
      if (m_includePathSet.find(includeId) == m_includePathSet.end()) {
        m_includePathSet.emplace(includeId);
        m_includePaths.emplace_back(includeId);
      }
    } else if (all_arguments[i] == "-split") {
      if (i == all_arguments.size() - 1) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_SPLIT_FILE_MISSING_SIZE, loc);
        break;
      }
      i++;
      m_linesForFileSplitting = std::stoi(all_arguments[i]);
    } else if (all_arguments[i] == "-builtin") {
      i++;
    } else if (all_arguments[i] == "-exe") {
      fs::path exeCommand = all_arguments[++i];
      if (exeCommand.is_relative()) {
        exeCommand = cd / exeCommand;
      }
      std::error_code ec;
      m_exeCommand = fs::weakly_canonical(exeCommand, ec).string();
    } else if (all_arguments[i] == "-nogc") {
      m_gc = false;
    } else if (all_arguments[i] == "-gc") {
      m_gc = true;
    } else if (all_arguments[i] == "-disable-line-markings") {
      m_disableLineMarkings = true;
    }
// No multiprocess on Windows platform, only multithreads
#if defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__)
    else if (all_arguments[i] == "-lowmem") {
      std::cerr << "Lowmem option is ignored on this platform\n";
    }
#else
    else if (all_arguments[i] == "-lowmem") {
      m_maxProcesses = 1;
      m_writePpOutput = true;
      m_lowMem = true;
    }
#endif
    else if (all_arguments[i] == "-nouhdm") {
      m_writeUhdm = false;
    } else if (all_arguments[i] == "-mt" || all_arguments[i] == "--threads" ||
               all_arguments[i] == "-mp") {
      bool mt =
          ((all_arguments[i] == "-mt") || (all_arguments[i] == "--threads"));
      if (i == all_arguments.size() - 1) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_MT_MISSING_LEVEL, loc);
        break;
      }
      i++;
      uint32_t maxMT = 0;
      if (all_arguments[i] == "max") {
        uint32_t concurentThreadsSupported =
            std::thread::hardware_concurrency();
        maxMT = concurentThreadsSupported;
      } else {
        maxMT = std::stoi(all_arguments[i]);
      }
      if (maxMT > 512) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_MT_INCORRECT_LEVEL, loc);
      } else {
        if (m_diffCompMode) {
          uint32_t concurentThreadsSupported =
              std::thread::hardware_concurrency();
          if (maxMT > (concurentThreadsSupported / 2))
            maxMT = (concurentThreadsSupported / 2);
        }

        if (maxMT == 0) {
          m_maxTreads = maxMT;

// No multiprocess on Windows platform, only multithreads
#if !(defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__))
          if (!mt) m_maxProcesses = maxMT;
#endif
        } else {
          if (mt) {
            m_maxTreads = maxMT;
            if (m_maxTreads < 2) m_maxTreads = 2;
          } else {
// No multiprocess on Windows platform, only multithreads
#if defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__)
            m_maxTreads = maxMT;
            if (m_maxTreads < 2) m_maxTreads = 2;
#else
            m_maxProcesses = maxMT;
#endif
          }

          if (profile()) {
            Location loc(symbols->registerSymbol(
                StrCat(m_maxProcesses, " processes and ", m_maxTreads)));
            errors->addError(ErrorDefinition::CMD_NUMBER_THREADS, loc);
          }
        }
      }
    } else if (all_arguments[i] == "-strictpythoncheck") {
      PythonAPI::setStrictMode(true);
    } else if (all_arguments[i] == "-tbb") {
      m_useTbb = true;
    } else if ((all_arguments[i] == "--top-module") ||
               (all_arguments[i] == "-top")) {
      i++;
      m_topLevelModules.insert(all_arguments[i]);
    } else if (all_arguments[i] == "-bb_mod") {
      i++;
      m_blackboxModules.insert(all_arguments[i]);
    } else if (all_arguments[i] == "-bb_inst") {
      i++;
      m_blackboxInstances.insert(all_arguments[i]);
    } else if (all_arguments[i] == "-createcache") {
      m_createCache = true;
      m_writeCache = true;
    } else if (all_arguments[i] == "-nowritecache") {
      m_writeCache = false;
    } else if (all_arguments[i] == "-lineoffsetascomments") {
      m_lineOffsetsAsComments = true;
    } else if (all_arguments[i] == "-v") {
      if (i == all_arguments.size() - 1) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_LIBRARY_FILE_MISSING_FILE, loc);
        break;
      }
      fs::path filepath = FileSystem::normalize(all_arguments[++i]);
      addWorkingDirectory_(cd, filepath.parent_path());
      if (filepath.is_relative()) filepath = cd / filepath;
      m_libraryFiles.emplace_back(
          fileSystem->toPathId(filepath.string(), symbols));
    } else if (all_arguments[i] == "-y") {
      if (i == all_arguments.size() - 1) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_LIBRARY_PATH_MISSING_PATH, loc);
        break;
      }
      m_libraryPaths.emplace_back(
          std::get<0>(addWorkingDirectory_(cd, all_arguments[++i])));
    } else if (all_arguments[i] == "-l") {
      ++i;
    } else if (all_arguments[i] == "-L") {
      fs::path filepath = FileSystem::normalize(all_arguments[++i]);
      addWorkingDirectory_(cd, filepath.parent_path());
      if (filepath.is_relative()) filepath = cd / filepath;
      m_orderedLibraries.emplace_back(
          fileSystem->toPathId(filepath.string(), symbols));
    } else if (all_arguments[i] == "-map") {
      fs::path filepath = FileSystem::normalize(all_arguments[++i]);
      addWorkingDirectory_(cd, filepath.parent_path());
      if (filepath.is_relative()) filepath = cd / filepath;
      m_libraryMapFiles.emplace_back(
          fileSystem->toPathId(filepath.string(), symbols));
    } else if (all_arguments[i] == "-cfgfile") {
      fs::path filepath = FileSystem::normalize(all_arguments[++i]);
      addWorkingDirectory_(cd, filepath.parent_path());
      if (filepath.is_relative()) filepath = cd / filepath;
      m_configFiles.emplace_back(
          fileSystem->toPathId(filepath.string(), symbols));
    } else if (all_arguments[i] == "-cfg") {
      i++;
      m_useConfigs.push_back(symbols->registerSymbol(all_arguments[i]));
    } else if (all_arguments[i] == "-writeppfile") {
      if (i == all_arguments.size() - 1) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_PP_FILE_MISSING_FILE, loc);
        break;
      }
      fs::path filepath = FileSystem::normalize(all_arguments[++i]);
      if (filepath.is_relative()) {
        m_writePpOutputFileId =
            fileSystem->getChild(m_outputDirId, filepath.string(), symbols);
      } else {
        m_writePpOutputFileId =
            fileSystem->toPathId(filepath.string(), symbols);
      }
    } else if (all_arguments[i] == "-nohash") {
      m_noCacheHash = true;
    } else if (all_arguments[i] == "-cache") {
      if (i == all_arguments.size() - 1) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_PP_FILE_MISSING_FILE, loc);
        break;
      }
      fs::path dirpath = FileSystem::normalize(all_arguments[++i]);
      if (dirpath.is_relative()) {
        m_cacheDirId =
            fileSystem->getChild(m_outputDirId, dirpath.string(), symbols);
      } else {
        m_cacheDirId = fileSystem->toPathId(dirpath.string(), symbols);
      }
    } else if (all_arguments[i] == "-replay") {
      m_replay = true;
    } else if (all_arguments[i] == "-writepp") {
      m_writePpOutput = true;
    } else if (all_arguments[i] == "-noinfo") {
      m_info = false;
    } else if (all_arguments[i] == "-nonote") {
      m_note = false;
    } else if (all_arguments[i] == "-nowarning") {
      m_warning = false;
    } else if (all_arguments[i] == "-synth") {
      m_nonSynthesizable = true;
    } else if (all_arguments[i] == "-formal") {
      m_nonSynthesizable = true;
      m_nonSynthesizableWithFormal = true;
    } else if (all_arguments[i] == "-profile") {
      m_profile = true;
    } else if (all_arguments[i] == "-nobuiltin") {
      m_parseBuiltIn = false;
    } else if (all_arguments[i] == "-outputlineinfo") {
      m_filterFileLine = false;
    } else if (all_arguments[i] == "+liborder") {
      m_libOrder = true;
    } else if (all_arguments[i] == "+librescan") {
      m_libRescan = true;
    } else if (all_arguments[i] == "+libverbose") {
      m_libVerbose = true;
    } else if (all_arguments[i] == "+nolibcell") {
      m_noLibCell = true;
    } else if (all_arguments[i] == "-sverilog") {
      m_sverilog = true;
    } else if (all_arguments[i] == "-fileunit") {
      Location loc(symbols->registerSymbol(all_arguments[i]));
      errors->addError(ErrorDefinition::CMD_SEPARATE_COMPILATION_UNIT_ON, loc);
    } else if (all_arguments[i] == "-diffcompunit") {
      if (m_fileUnit) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_SEPARATE_COMPILATION_UNIT_ON,
                         loc);
      }
    } else if (all_arguments[i] == "-odir") {
      i++;
    } else if (all_arguments[i] == "--Mdir") {
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
    } else if (all_arguments[i] == "-parsetree") {
      m_parseTree = true;
      m_parse = true;
      m_parseOnly = false;
      m_compile = false;
      m_elaborate = false;
      m_linesForFileSplitting = kLinesForFileSplitting;
    } else if (all_arguments[i] == "-parseonly") {
      m_writePpOutput = true;
      m_parse = true;
      m_compile = false;
      m_elaborate = false;
      m_parseOnly = true;
    } else if (all_arguments[i] == "-init") {
      m_cacheAllowed = false;
      m_writeCache = false;
      cleanCache();
    } else if (all_arguments[i] == "-sepcomp") {
      m_sepComp = true;
      m_writePpOutput = true;
      m_parse = true;
      m_compile = false;
      m_elaborate = false;
      m_elabUhdm = false;
      m_writeUhdm = false;
      m_parseBuiltIn = false;
    } else if (all_arguments[i] == "-noparse") {
      m_parse = false;
      m_compile = false;
      m_elaborate = false;
    } else if (all_arguments[i] == "-nocomp") {
      m_compile = false;
      m_elaborate = false;
    } else if (all_arguments[i] == "-noelab") {
      m_elaborate = false;
    } else if (all_arguments[i] == "-noreduce") {
      m_reduce = false;
    } else if (all_arguments[i] == "-elabuhdm") {
      m_elaborate = true;
      m_elabUhdm = true;
    } else if (all_arguments[i] == "-pploc") {
      m_ppOutputFileLocation = true;
    } else if (all_arguments[i] == "-ppextra_loc") {
      m_ppPrintLineInfo = true;
    } else if (all_arguments[i] == "-pythonlistener") {
      m_writePpOutput = true;
      m_parse = true;
      m_compile = true;
      m_elaborate = true;
      m_pythonListener = true;
      if (!m_pythonAllowed)
        std::cerr << "ERROR: No Python allowed, check your arguments!\n";
    } else if (all_arguments[i] == "-nopython") {
      m_pythonAllowed = false;
    } else if (all_arguments[i] == "-withpython") {
      withPython();
    } else if (all_arguments[i] == "-pythonevalscriptperfile") {
      if (i == all_arguments.size() - 1) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_PP_FILE_MISSING_FILE, loc);
        break;
      }
      i++;
      m_writePpOutput = true;
      m_parse = true;
      m_compile = true;
      m_elaborate = true;
      m_pythonEvalScriptPerFile = true;
      m_pythonEvalScriptPerFileId =
          fileSystem->toPathId(all_arguments[i], symbols);
      if (m_pythonAllowed)
        PythonAPI::loadScript(all_arguments[i], true);
      else
        std::cerr << "ERROR: No Python allowed, check your arguments!\n";
    } else if (all_arguments[i] == "-pythonlistenerfile") {
      if (i == all_arguments.size() - 1) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_PP_FILE_MISSING_FILE, loc);
        break;
      }
      m_writePpOutput = true;
      m_parse = true;
      m_compile = true;
      m_elaborate = true;
      m_pythonListener = true;
      fs::path filepath = FileSystem::normalize(all_arguments[++i]);
      addWorkingDirectory_(cd, filepath.parent_path());
      if (filepath.is_relative()) filepath = cd / filepath;
      m_pythonListenerFileId = fileSystem->toPathId(filepath.string(), symbols);
      PythonAPI::setListenerScript(filepath.string());
    } else if (all_arguments[i] == "-pythonevalscript") {
      if (i == all_arguments.size() - 1) {
        Location loc(symbols->registerSymbol(all_arguments[i]));
        errors->addError(ErrorDefinition::CMD_PP_FILE_MISSING_FILE, loc);
        break;
      }
      m_writePpOutput = true;
      m_parse = true;
      m_compile = true;
      m_elaborate = true;
      m_pythonEvalScript = true;
      fs::path filepath = FileSystem::normalize(all_arguments[++i]);
      addWorkingDirectory_(cd, filepath.parent_path());
      if (filepath.is_relative()) filepath = cd / filepath;
      m_pythonEvalScriptId = fileSystem->toPathId(filepath.string(), symbols);
      if (m_pythonAllowed)
        PythonAPI::loadScript(filepath, true);
      else
        std::cerr << "ERROR: No Python allowed, check your arguments!\n";
    } else if (all_arguments[i] == "-nocache") {
      m_cacheAllowed = false;
    } else if (all_arguments[i] == "-nowritecache") {
      m_writeCache = false;
    } else if (all_arguments[i] == "-noprecompiledcache") {
      m_precompiledCacheAllowed = false;
    } else if (all_arguments[i] == "-sv") {
      if (((i + 1) < all_arguments.size()) &&
          (all_arguments[i + 1][0] != '-')) {
        fs::path filepath = FileSystem::normalize(all_arguments[++i]);
        addWorkingDirectory_(cd, filepath.parent_path());
        if (filepath.is_relative()) filepath = cd / filepath;
        const PathId fileId = fileSystem->toPathId(filepath.string(), symbols);
        if (m_sourceFileSet.find(fileId) == m_sourceFileSet.end()) {
          m_sourceFiles.emplace_back(fileId);
          m_sourceFileSet.emplace(fileId);
          m_svSourceFiles.emplace(fileId);
          PathId dirId = fileSystem->getParent(fileId, symbols);
          if (m_includePathSet.find(dirId) == m_includePathSet.end()) {
            m_includePathSet.emplace(dirId);
            m_includePaths.emplace_back(dirId);
          }
        }
      } else {
        m_sverilog = true;
      }
    } else if (all_arguments[i] == "--x-assign") {
      Location loc(symbols->registerSymbol(all_arguments[i]));
      errors->addError(ErrorDefinition::CMD_PLUS_ARG_IGNORED, loc);
      i++;
    } else if (all_arguments[i] == "--x-initial") {
      Location loc(symbols->registerSymbol(all_arguments[i]));
      errors->addError(ErrorDefinition::CMD_PLUS_ARG_IGNORED, loc);
      i++;
    } else if (all_arguments[i].at(0) == '+') {
      Location loc(symbols->registerSymbol(all_arguments[i]));
      errors->addError(ErrorDefinition::CMD_PLUS_ARG_IGNORED, loc);
    } else if (all_arguments[i].at(0) == '-') {
      Location loc(symbols->registerSymbol(all_arguments[i]));
      errors->addError(ErrorDefinition::CMD_MINUS_ARG_IGNORED, loc);
    } else if ((all_arguments[i][0] == '-') || is_number(all_arguments[i]) ||
               is_c_file(all_arguments[i]) ||
               (all_arguments[i].rfind(".vlt") != std::string::npos)) {
      Location loc(symbols->registerSymbol(all_arguments[i]));
      errors->addError(ErrorDefinition::CMD_PLUS_ARG_IGNORED, loc);
    } else {
      fs::path filepath = FileSystem::normalize(all_arguments[i]);
      addWorkingDirectory_(cd, filepath.parent_path());
      if (filepath.is_relative()) filepath = cd / filepath;
      const PathId fileId = fileSystem->toPathId(filepath.string(), symbols);
      if (m_sourceFileSet.find(fileId) == m_sourceFileSet.end()) {
        m_sourceFiles.emplace_back(fileId);
        m_sourceFileSet.emplace(fileId);
        PathId dirId = fileSystem->getParent(fileId, symbols);
        if (m_includePathSet.find(dirId) == m_includePathSet.end()) {
          m_includePathSet.emplace(dirId);
          m_includePaths.emplace_back(dirId);
        }
      }
    }
  }

  // Force disable elaboration!!
  m_elaborate = m_reduce = m_elabUhdm = m_coverUhdm = false;

  if (m_debugFSConfig) {
    fileSystem->printConfiguration(std::cout);
  }

  // Parse through all files to find all include files
  findAllIncludeFiles();

  status = setupCache_();
  if (!status) return status;

  status = checkCommandLine_();
  return status;
}

bool CommandLineParser::checkCommandLine_() {
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errors = m_session->getErrorContainer();

  bool noError = true;
  for (const auto& fid : m_sourceFiles) {
    if (!fileSystem->isRegularFile(fid)) {
      Location loc(fid);
      errors->addError(ErrorDefinition::CMD_VERILOG_FILE_DOES_NOT_EXIST, loc);
      noError = false;
    }
  }
  for (const auto& did : m_libraryPaths) {
    if (!fileSystem->isDirectory(did)) {
      Location loc(did);
      errors->addError(ErrorDefinition::CMD_LIBRARY_PATH_DOES_NOT_EXIST, loc);
    }
  }
  for (const auto& fid : m_libraryFiles) {
    if (!fileSystem->isRegularFile(fid)) {
      Location loc(fid);
      errors->addError(ErrorDefinition::CMD_LIBRARY_FILE_DOES_NOT_EXIST, loc);
      noError = false;
    }
  }
  for (const auto& did : m_includePaths) {
    if (!fileSystem->isDirectory(did)) {
      Location loc(did);
      errors->addError(ErrorDefinition::CMD_INCLUDE_PATH_DOES_NOT_EXIST, loc);
    }
  }
  if (!errors->printMessages(m_muteStdout)) {
    noError = false;
  }

  return noError;
}

bool CommandLineParser::isSVFile(PathId fileId) const {
  return fileId && (m_svSourceFiles.find(fileId) != m_svSourceFiles.end());
}

bool CommandLineParser::prepareCompilation_(int32_t argc, const char** argv) {
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errors = m_session->getErrorContainer();

  bool noError = true;
  const PathId compileDirId = getCompileDirId();

  if (!m_logFileNameId) {
    m_logFileNameId = symbols->registerSymbol(FileSystem::kLogFileName);
  }

  if (!m_logFileId) {
    m_logFileId = fileSystem->getLogFile(
        m_fileUnit, symbols->getSymbol(m_logFileNameId), symbols);
  }

  if (!fileSystem->mkdirs(m_outputDirId)) {
    Location loc(m_outputDirId);
    errors->addError(ErrorDefinition::CMD_PP_CANNOT_CREATE_OUTPUT_DIR, loc);
    noError = false;
  }

  const PathId logDirId = fileSystem->getParent(m_logFileId, symbols);
  if (!fileSystem->mkdirs(logDirId)) {
    Location loc(logDirId);
    errors->addError(ErrorDefinition::CMD_PP_CANNOT_CREATE_OUTPUT_DIR, loc);
    noError = false;
  }

  if (!fileSystem->mkdirs(compileDirId)) {
    Location loc(compileDirId);
    errors->addError(ErrorDefinition::CMD_PP_CANNOT_CREATE_OUTPUT_DIR, loc);
    noError = false;
  }

  errors->init();
  logBanner(argc, argv);
  Location loc(m_logFileId);
  errors->addError(ErrorDefinition::CMD_CREATING_LOG_FILE, loc);

  if (errors->hasFatalErrors()) {
    noError = false;
  }

  return noError;
}

bool CommandLineParser::setupCache_() {
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errors = m_session->getErrorContainer();

  bool noError = true;

  if (!m_cacheDirId) {
    m_cacheDirId = fileSystem->getCacheDir(m_fileUnit, symbols);
  }

  if (m_cacheAllowed) {
    if (!fileSystem->mkdirs(m_cacheDirId)) {
      Location loc(m_cacheDirId);
      errors->addError(ErrorDefinition::CMD_PP_CANNOT_CREATE_CACHE_DIR, loc);
      noError = false;
    }
  } else {
    cleanCache();
  }

  return noError;
}

bool CommandLineParser::cleanCache() {
  SymbolTable* const symbols = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();

  bool noError = true;

  if (!m_cacheDirId) {
    m_cacheDirId = fileSystem->getCacheDir(m_fileUnit, symbols);
  }

  if (!m_cacheAllowed && !fileSystem->rmtree(m_cacheDirId)) {
    std::cerr << "ERROR: Cannot delete cache directory: "
              << PathIdPP(m_cacheDirId, fileSystem) << std::endl;
    noError = false;
  }

  return noError;
}

// Recursively finds all include files in a source file and its includes.
void CommandLineParser::findAllIncludes(const std::filesystem::path& filePath,
                                        std::set<std::string>& visited) {
  if (!std::filesystem::exists(filePath)) return;

  if (visited.count(filePath.string())) return;  // Prevent cycles
  visited.insert(filePath.string());

  std::ifstream file(filePath);
  if (!file.is_open()) return;

  const std::regex includeRegex(R"("^\\s*`include\\s+\"([^\"]+)\"")");
  std::string line;
  while (std::getline(file, line)) {
    std::smatch match;
    if (std::regex_search(line, match, includeRegex)) {
      std::string includeFile = match[1].str();
      SymbolTable* const symbols = m_session->getSymbolTable();
      FileSystem* const fileSystem = m_session->getFileSystem();
      PathId fileId = fileSystem->locate(
          includeFile, m_session->getCommandLineParser()->getIncludePaths(),
          symbols);
      if (fileId && m_sourceFileSet.find(fileId) == m_sourceFileSet.end()) {
        m_sourceFiles.emplace_back(fileId);
        m_sourceFileSet.emplace(fileId);
      }

      // Try to resolve the include path relative to the current file
      std::filesystem::path nextPath = filePath.parent_path() / includeFile;
      findAllIncludes(nextPath, visited);
    }
  }
}

void CommandLineParser::findAllIncludeFiles() {
  std::set<std::string> visited;
  if (FileSystem* const fs = m_session->getFileSystem()) {
    PathIdVector sourceFiles = m_sourceFiles;
    for (const PathId& sourceFile : sourceFiles) {
      const std::filesystem::path filePath = fs->toPlatformAbsPath(sourceFile);
      findAllIncludes(filePath, visited);
    }
  }
}
}  // namespace SURELOG
