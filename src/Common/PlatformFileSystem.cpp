/*
 Copyright 2022 chipsalliance

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
 * File:   FileSystem.cpp
 * Author: hs
 *
 * Created on June 1, 2022, 3:00 AM
 */

#include <Surelog/Common/PlatformFileSystem.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/StringUtils.h>

#include <fstream>
#include <iostream>
#include <regex>

namespace SURELOG {
static constexpr bool kEnableLogs = false;

PlatformFileSystem::PlatformFileSystem(const std::filesystem::path &workingDir)
    : m_workingDir(normalize(workingDir)), m_configurations{Configuration()} {
  // Add _wd_ as the first source directory!
  m_configurations.front().m_sourceDir = m_workingDir;
}

PlatformFileSystem::~PlatformFileSystem() {
  {
    std::scoped_lock<std::mutex> lock(m_inputStreamsMutex);

    while (!m_inputStreams.empty()) {
      close(*m_inputStreams.begin()->get());
    }
  }
  {
    std::scoped_lock<std::mutex> lock(m_outputStreamsMutex);

    while (!m_outputStreams.empty()) {
      close(*m_outputStreams.begin()->get());
    }
  }

  if (getInstance() == this) setInstance(nullptr);
}

PathId PlatformFileSystem::toPathId(std::string_view path,
                                    SymbolTable *symbolTable) {
  if (path.empty()) return BadPathId;

  std::filesystem::path normpath = normalize(path);
  if (normpath.empty() || normpath.is_relative()) return BadPathId;

  auto [symbolId, symbol] = symbolTable->add(normpath.string());
  return PathId(symbolTable, (RawSymbolId)symbolId, symbol);
}

std::filesystem::path PlatformFileSystem::toPlatformPath(PathId id) {
  return toPath(id);
}

std::filesystem::path PlatformFileSystem::toRelPath(PathId id) {
  int32_t minUpDirs = std::numeric_limits<int32_t>::max();
  std::filesystem::path bestPrefix;
  std::filesystem::path bestSuffix;
  std::filesystem::path path = toPath(id);

  for (const Configuration &configuration : m_configurations) {
    const std::filesystem::path &prefix = configuration.m_sourceDir;
    if (prefix == path) {
      bestPrefix = path;
      bestSuffix = ".";
      minUpDirs = 0;
      break;
    } else if (prefix.root_path() == path.root_path()) {
      std::filesystem::path suffix = path.lexically_relative(prefix);

      int32_t upDirs = 0;
      for (const auto &part : suffix) {
        if (part == "..")
          ++upDirs;
        else
          break;
      }

      if (upDirs < minUpDirs) {
        minUpDirs = upDirs;
        bestPrefix = prefix;
        bestSuffix = suffix;
        if (minUpDirs == 0) break;
      }
    }
  }

  return (minUpDirs == std::numeric_limits<int32_t>::max()) ? path : bestSuffix;
}

std::string PlatformFileSystem::getWorkingDir() {
  return m_workingDir.string();
}

std::set<std::string> PlatformFileSystem::getWorkingDirs() {
  std::set<std::string> workingDirs;
  std::transform(m_configurations.begin(), m_configurations.end(),
                 std::inserter(workingDirs, workingDirs.end()),
                 [](const Configuration &configuration) {
                   return configuration.m_sourceDir.string();
                 });
  return workingDirs;
}

std::istream &PlatformFileSystem::openInput(
    const std::filesystem::path &filepath, std::ios_base::openmode mode) {
  if (!filepath.is_absolute()) return m_nullInputStream;

  std::scoped_lock<std::mutex> lock(m_inputStreamsMutex);
  std::pair<InputStreams::iterator, bool> it =
      m_inputStreams.emplace(new std::ifstream);

  std::ifstream &strm = *static_cast<std::ifstream *>(it.first->get());
  strm.open(filepath, mode);
  return strm;
}

std::ostream &PlatformFileSystem::openOutput(
    const std::filesystem::path &filepath, std::ios_base::openmode mode) {
  if (!filepath.is_absolute()) return m_nullOutputStream;

  std::scoped_lock<std::mutex> lock(m_outputStreamsMutex);
  std::pair<OutputStreams::iterator, bool> it =
      m_outputStreams.emplace(new std::ofstream);

  std::ofstream &strm = *static_cast<std::ofstream *>(it.first->get());
  strm.open(filepath, mode);
  return strm;
}

std::istream &PlatformFileSystem::openInput(PathId fileId,
                                            std::ios_base::openmode mode) {
  const std::filesystem::path filepath = toPath(fileId);
  return filepath.empty() ? m_nullInputStream : openInput(filepath, mode);
}

bool PlatformFileSystem::close(std::istream &strm) {
  std::scoped_lock<std::mutex> lock(m_inputStreamsMutex);

  InputStreams::const_iterator it = m_inputStreams.find(&strm);
  if (it != m_inputStreams.end()) {
    m_inputStreams.erase(it);
    return true;
  }
  return false;
}

std::ostream &PlatformFileSystem::openOutput(PathId fileId,
                                             std::ios_base::openmode mode) {
  const std::filesystem::path filepath = toPath(fileId);
  return filepath.empty() ? m_nullOutputStream : openOutput(filepath, mode);
}

bool PlatformFileSystem::close(std::ostream &strm) {
  std::scoped_lock<std::mutex> lock(m_outputStreamsMutex);

  OutputStreams::const_iterator it = m_outputStreams.find(&strm);
  if (it != m_outputStreams.end()) {
    m_outputStreams.erase(it);
    return true;
  }
  return false;
}

bool PlatformFileSystem::saveContent(PathId fileId, const char *content,
                                     std::streamsize length, bool useTemp) {
  if (!fileId) return false;

  const std::filesystem::path filepath = toPath(fileId);
  if (filepath.empty()) return false;

  bool result = false;

  std::filesystem::path filepath2Write = filepath;
  if (useTemp) filepath2Write += ".tmp";

  std::ostream &strm =
      openOutput(filepath2Write, std::ios_base::out | std::ios_base::binary);
  if (strm.good()) {
    if (length > 0) {
      strm.write(content, length);
    }
    result = strm.good();
  }
  close(strm);

  if (useTemp) {
    std::error_code ec;
    if (result) {
      std::filesystem::rename(filepath2Write, filepath, ec);
      result = !ec;
    } else {
      std::filesystem::remove(filepath2Write, ec);
    }
  }

  return result;
}

bool PlatformFileSystem::addMapping(std::string_view what,
                                    std::string_view with) {
  std::filesystem::path original = normalize(what);
  std::filesystem::path replacement = normalize(with);

  if (!original.is_absolute() || !replacement.is_absolute()) return false;

  Mapping &mapping = m_mappings.emplace_back();
  mapping.m_what = original.string();
  mapping.m_with = replacement.string();
  return true;
}

std::string PlatformFileSystem::remap(std::string_view what) {
  for (const Mapping &mapping : m_mappings) {
    if (mapping.m_what == what) {
      return mapping.m_with;
    } else if ((mapping.m_what.length() < what.length()) &&
               (what.compare(0, mapping.m_what.length(), mapping.m_what) ==
                0)) {
      return std::string(mapping.m_with)
          .append(what.substr(mapping.m_what.length()));
    }
  }
  return std::string(what);
}

struct ConfigurationComparer final {
  bool operator()(const PlatformFileSystem::Configuration &lhs,
                  const PlatformFileSystem::Configuration &rhs) const {
    const std::string lhs_s = lhs.m_sourceDir.string();
    const std::string rhs_s = rhs.m_sourceDir.string();
    int32_t r = lhs_s.length() - rhs_s.length();
    return (r == 0) ? (lhs_s.compare(rhs_s) < 0) : (r < 0);
  }
};

void PlatformFileSystem::addConfiguration(
    const std::filesystem::path &sourceDir) {
  int32_t editCount = 0;
  for (Configuration &configuration : m_configurations) {
    if (is_subpath(configuration.m_sourceDir, sourceDir)) {
      return;
    } else if (is_subpath(sourceDir, configuration.m_sourceDir)) {
      ++editCount;
      configuration.m_sourceDir = sourceDir;
    }
  }

  if (editCount == 1) return;

  if (editCount == 0) {
    m_configurations.emplace_back(Configuration{sourceDir, ""});
  }

  std::stable_sort(m_configurations.begin(), m_configurations.end(),
                   ConfigurationComparer());

  size_t count = 1;
  for (size_t i = 1, n = m_configurations.size(); i < n; ++i) {
    const Configuration &cc = m_configurations[count - 1];
    const Configuration &ci = m_configurations[i];
    if ((cc.m_sourceDir != ci.m_sourceDir) ||
        (cc.m_cacheDir != ci.m_cacheDir)) {
      m_configurations[count].m_sourceDir = m_configurations[i].m_sourceDir;
      m_configurations[count].m_cacheDir = m_configurations[i].m_cacheDir;
      ++count;
    }
  }

  if (count != m_configurations.size()) {
    m_configurations.resize(count);
  }
}

PathId PlatformFileSystem::getProgramFile(std::string_view hint,
                                          SymbolTable *symbolTable) {
  const std::filesystem::path programPath = getProgramPath();
  if (!programPath.empty()) {
    addConfiguration(normalize(programPath.parent_path()));
    return toPathId(programPath.string(), symbolTable);
  }

  std::error_code ec;
  const std::filesystem::path hintPath = hint;
  if (!hintPath.empty() && std::filesystem::exists(hintPath, ec) && !ec) {
    addConfiguration(normalize(hintPath.parent_path()));
    return toPathId(hintPath.string(), symbolTable);
  }

#if defined(_MSC_VER) || defined(__MINGW32__) || defined(__CYGWIN__)
  const char PATH_DELIMITER = ';';
#else
  const char PATH_DELIMITER = ':';
#endif

  // Still not found, let's go through the $PATH and see what comes up first.
  const char *const path = std::getenv("PATH");
  if (path != nullptr) {
    std::stringstream searchPath(path);
    std::string pathElement;
    while (std::getline(searchPath, pathElement, PATH_DELIMITER)) {
      const std::filesystem::path programPath =
          std::filesystem::path(pathElement) / hintPath;
      if (std::filesystem::exists(programPath, ec) && !ec) {
        addConfiguration(normalize(programPath.parent_path()));
        return toPathId(programPath.string(), symbolTable);
      }
    }
  }

  return BadPathId;  // Didn't find anything.
}

PathId PlatformFileSystem::getWorkingDir(std::string_view dir,
                                         SymbolTable *symbolTable) {
  const std::filesystem::path dirpath(dir);
  if (dir.empty() || !dirpath.is_absolute()) return BadPathId;

  PathId sourceDirId = toPathId(dirpath.string(), symbolTable);
  addConfiguration(toPath(sourceDirId));
  return sourceDirId;
}

PathId PlatformFileSystem::getOutputDir(std::string_view dir,
                                        SymbolTable *symbolTable) {
  const std::filesystem::path dirpath(dir);
  if (dir.empty() || !dirpath.is_absolute()) return BadPathId;

  PathId outputDirId = toPathId(dirpath.string(), symbolTable);
  m_outputDir = toPath(outputDirId);
  if (kEnableLogs) {
    std::cerr << "getOutputDir: " << dir << " => " << PathIdPP(outputDirId)
              << std::endl;
  }
  return outputDirId;
}

PathId PlatformFileSystem::getPrecompiledDir(PathId programId,
                                             SymbolTable *symbolTable) {
  if (!programId) return BadPathId;

  const std::filesystem::path programFile = toPath(programId);
  if (programFile.empty() || !programFile.has_parent_path()) return BadPathId;

  const std::filesystem::path programPath = programFile.parent_path();
  const std::vector<std::filesystem::path> search_path = {
      programPath,                     // Build path
      programPath / "lib" / "surelog"  // Installation path
  };

  std::error_code ec;
  for (const std::filesystem::path &dir : search_path) {
    const std::filesystem::path pkgDir = dir / kPrecompiledDirName;
    if ((std::filesystem::exists(dir, ec) && !ec) &&
        (std::filesystem::is_directory(pkgDir, ec) && !ec)) {
      PathId precompiledDirId = toPathId(pkgDir.string(), symbolTable);
      if (kEnableLogs) {
        std::cerr << "getPrecompiledDir: " << PathIdPP(programId) << " => "
                  << PathIdPP(precompiledDirId) << std::endl;
      }
      return precompiledDirId;
    }
  }

  return toPathId((programPath / kPrecompiledDirName).string(), symbolTable);
}

PathId PlatformFileSystem::getLogFile(bool isUnitCompilation,
                                      std::string_view filename,
                                      SymbolTable *symbolTable) {
  if (filename.empty()) return BadPathId;

  std::filesystem::path logFile = m_outputDir;
  logFile /= isUnitCompilation ? kUnitCompileDirName : kAllCompileDirName;
  logFile /= filename;
  PathId logFileId = toPathId(logFile.string(), symbolTable);
  if (kEnableLogs) {
    std::cerr << "getLogFile: " << filename << " => " << PathIdPP(logFileId)
              << std::endl;
  }
  return logFileId;
}

PathId PlatformFileSystem::getCacheDir(bool isUnitCompilation,
                                       std::string_view dirname,
                                       SymbolTable *symbolTable) {
  if (dirname.empty()) return BadPathId;

  std::filesystem::path cacheDir = m_outputDir;
  cacheDir /= isUnitCompilation ? kUnitCompileDirName : kAllCompileDirName;
  cacheDir /= dirname;
  PathId cacheDirId = toPathId(cacheDir.string(), symbolTable);
  if (kEnableLogs) {
    std::cerr << "getCacheDir: " << dirname << " => " << PathIdPP(cacheDirId)
              << std::endl;
  }
  return cacheDirId;
}

PathId PlatformFileSystem::getCompileDir(bool isUnitCompilation,
                                         SymbolTable *symbolTable) {
  std::filesystem::path cacheDir = m_outputDir;
  cacheDir /= isUnitCompilation ? kUnitCompileDirName : kAllCompileDirName;
  PathId compileDirId = toPathId(cacheDir.string(), symbolTable);
  if (kEnableLogs) {
    std::cerr << "getCompileDir: " << PathIdPP(compileDirId) << std::endl;
  }
  return compileDirId;
}

PathId PlatformFileSystem::getPpOutputFile(bool isUnitCompilation,
                                           PathId sourceFileId,
                                           std::string_view libraryName,
                                           SymbolTable *symbolTable) {
  if (!sourceFileId || libraryName.empty()) return BadPathId;

  std::filesystem::path ppOutputFilepath = m_outputDir;
  ppOutputFilepath /=
      isUnitCompilation ? kUnitCompileDirName : kAllCompileDirName;
  ppOutputFilepath /= kPreprocessLibraryDirName;
  ppOutputFilepath /= libraryName;
  ppOutputFilepath /= toRelPath(sourceFileId);
  PathId ppFileId = toPathId(ppOutputFilepath.string(), symbolTable);
  if (kEnableLogs) {
    std::cerr << "getPpOutputFile: " << PathIdPP(sourceFileId) << " => "
              << PathIdPP(ppFileId) << std::endl;
  }
  return ppFileId;
}

PathId PlatformFileSystem::getPpCacheFile(bool isUnitCompilation,
                                          PathId sourceFileId,
                                          std::string_view libraryName,
                                          bool isPrecompiled,
                                          SymbolTable *symbolTable) {
  if (!sourceFileId || libraryName.empty()) return BadPathId;

  std::filesystem::path ppCacheFile;
  if (isPrecompiled) {
    ppCacheFile = getProgramPath().parent_path();
    ppCacheFile /= kPrecompiledDirName;
    ppCacheFile /= libraryName;
    ppCacheFile /= toPlatformPath(sourceFileId).filename();
  } else {
    ppCacheFile = m_outputDir;
    ppCacheFile /= isUnitCompilation ? kUnitCompileDirName : kAllCompileDirName;
    ppCacheFile /= kPreprocessCacheDirName;
    ppCacheFile /= libraryName;
    ppCacheFile /= toRelPath(sourceFileId);
  }
  ppCacheFile += ".slpp";
  const PathId ppCacheFileId = toPathId(ppCacheFile.string(), symbolTable);
  if (kEnableLogs) {
    std::cerr << "getPpCacheFile: " << PathIdPP(sourceFileId) << " => "
              << PathIdPP(ppCacheFileId) << std::endl;
  }
  return ppCacheFileId;
}

PathId PlatformFileSystem::getParseCacheFile(bool isUnitCompilation,
                                             PathId ppFileId,
                                             std::string_view libraryName,
                                             bool isPrecompiled,
                                             SymbolTable *symbolTable) {
  if (!ppFileId || libraryName.empty()) return BadPathId;

  const std::filesystem::path ppFile = toPath(ppFileId);

  std::filesystem::path parseCacheFile;
  if (isPrecompiled) {
    parseCacheFile = getProgramPath().parent_path();
    parseCacheFile /= kPrecompiledDirName;
    parseCacheFile /= libraryName;
    parseCacheFile /= ppFile.filename();
  } else {
    std::filesystem::path ppOutputDir = m_outputDir;
    ppOutputDir /= isUnitCompilation ? kUnitCompileDirName : kAllCompileDirName;
    ppOutputDir /= kPreprocessLibraryDirName;

    parseCacheFile = m_outputDir;
    parseCacheFile /=
        isUnitCompilation ? kUnitCompileDirName : kAllCompileDirName;
    parseCacheFile /= kParserCacheDirName;
    parseCacheFile /= ppFile.lexically_relative(ppOutputDir);
  }
  parseCacheFile += ".slpa";
  const PathId parseCacheFileId =
      toPathId(parseCacheFile.string(), symbolTable);
  if (kEnableLogs) {
    std::cerr << "getParseCacheFile: " << PathIdPP(ppFileId) << " => "
              << PathIdPP(parseCacheFileId) << std::endl;
  }
  return parseCacheFileId;
}

PathId PlatformFileSystem::getPythonCacheFile(bool isUnitCompilation,
                                              PathId sourceFileId,
                                              std::string_view libraryName,
                                              SymbolTable *symbolTable) {
  if (!sourceFileId || libraryName.empty()) return BadPathId;

  std::filesystem::path pythonCacheFile = m_outputDir;
  pythonCacheFile /=
      isUnitCompilation ? kUnitCompileDirName : kAllCompileDirName;
  pythonCacheFile /= kPythonCacheDirName;
  pythonCacheFile /= libraryName;
  pythonCacheFile /= toRelPath(sourceFileId);
  pythonCacheFile += ".slpy";
  PathId pyCacheFileId = toPathId(pythonCacheFile.string(), symbolTable);
  if (kEnableLogs) {
    std::cerr << "getPythonCacheFile: " << PathIdPP(sourceFileId) << " => "
              << PathIdPP(pyCacheFileId) << std::endl;
  }
  return pyCacheFileId;
}

PathId PlatformFileSystem::getPpMultiprocessingDir(bool isUnitCompilation,
                                                   SymbolTable *symbolTable) {
  std::filesystem::path ppMultiprocessingDir = m_outputDir;
  ppMultiprocessingDir /=
      isUnitCompilation ? kUnitCompileDirName : kAllCompileDirName;
  ppMultiprocessingDir /= kMultiprocessingPpDirName;
  PathId ppMultiprocessingDirId =
      toPathId(ppMultiprocessingDir.string(), symbolTable);
  if (kEnableLogs) {
    std::cerr << "getPpMultiprocessingDir: " << PathIdPP(ppMultiprocessingDirId)
              << std::endl;
  }
  return ppMultiprocessingDirId;
}

PathId PlatformFileSystem::getParserMultiprocessingDir(
    bool isUnitCompilation, SymbolTable *symbolTable) {
  std::filesystem::path parserMultiprocessingDir = m_outputDir;
  parserMultiprocessingDir /=
      isUnitCompilation ? kUnitCompileDirName : kAllCompileDirName;
  parserMultiprocessingDir /= kMultiprocessingParserDirName;
  return toPathId(parserMultiprocessingDir.string(), symbolTable);
}

PathId PlatformFileSystem::getChunkFile(PathId ppFileId, int32_t chunkIndex,
                                        SymbolTable *symbolTable) {
  std::filesystem::path ppFile = toPath(ppFileId);
  if (ppFile.empty()) return BadPathId;

  std::ostringstream strm;
  const char filler = strm.fill();
  const std::streamsize width = strm.width();

  strm << "." << std::setfill('0') << std::setw(4) << chunkIndex
       << std::setfill(filler) << std::setw(width)
       << ppFile.extension().string();

  std::filesystem::path chunkFile = ppFile;
  chunkFile.replace_extension(strm.str());
  PathId chunkFileId = toPathId(chunkFile.string(), symbolTable);
  if (kEnableLogs) {
    std::cerr << "getChunkFile: " << PathIdPP(ppFileId) << " => "
              << PathIdPP(chunkFileId) << std::endl;
  }
  return chunkFileId;
}

PathId PlatformFileSystem::getCheckerDir(bool isUnitCompilation,
                                         SymbolTable *symbolTable) {
  std::filesystem::path checkerDir = m_outputDir;
  checkerDir /= isUnitCompilation ? kUnitCompileDirName : kAllCompileDirName;
  checkerDir /= kCheckerDirName;
  PathId checkerDirId = toPathId(checkerDir.string(), symbolTable);
  if (kEnableLogs) {
    std::cerr << "getCheckerDir: " << PathIdPP(checkerDirId) << std::endl;
  }
  return checkerDirId;
}

PathId PlatformFileSystem::getCheckerFile(PathId uhdmFileId,
                                          SymbolTable *symbolTable) {
  std::filesystem::path uhdmFile = toPath(uhdmFileId);
  if (uhdmFile.empty()) return BadPathId;

  std::filesystem::path checkerFile = uhdmFile.parent_path();
  checkerFile /= kCheckerDirName;
  checkerFile /= uhdmFile.filename().replace_extension(".chk");
  PathId checkerFileId = toPathId(checkerFile.string(), symbolTable);
  if (kEnableLogs) {
    std::cerr << "getCheckerFile: " << PathIdPP(uhdmFileId) << " => "
              << PathIdPP(checkerFileId) << std::endl;
  }
  return checkerFileId;
}

PathId PlatformFileSystem::getCheckerHtmlFile(PathId uhdmFileId,
                                              SymbolTable *symbolTable) {
  const std::filesystem::path uhdmFile = toPath(uhdmFileId);
  if (uhdmFile.empty()) return BadPathId;

  std::filesystem::path checkerHtmlFile = uhdmFile.parent_path();
  checkerHtmlFile /= kCheckerDirName;
  checkerHtmlFile /= uhdmFile.filename().replace_extension(".chk");
  checkerHtmlFile += ".html";
  PathId checkerHtmlFileId = toPathId(checkerHtmlFile.string(), symbolTable);
  if (kEnableLogs) {
    std::cerr << "getCheckerHtmlFile: " << PathIdPP(uhdmFileId) << " => "
              << PathIdPP(checkerHtmlFileId) << std::endl;
  }
  return checkerHtmlFileId;
}

PathId PlatformFileSystem::getCheckerHtmlFile(PathId uhdmFileId, int32_t index,
                                              SymbolTable *symbolTable) {
  std::filesystem::path uhdmFile = toPath(uhdmFileId);
  if (uhdmFile.empty()) return BadPathId;

  std::ostringstream strm;
  const char filler = strm.fill();
  const std::streamsize width = strm.width();

  strm << uhdmFile.stem().string() << "_" << std::setfill('0') << std::setw(4)
       << index << std::setfill(filler) << std::setw(width) << ".chk.html";

  std::filesystem::path checkerHtmlFile = uhdmFile.parent_path();
  checkerHtmlFile /= kCheckerDirName;
  checkerHtmlFile /= strm.str();
  PathId checkerHtmlFileId = toPathId(checkerHtmlFile.string(), symbolTable);
  if (kEnableLogs) {
    std::cerr << "getCheckerHtmlFile: " << PathIdPP(uhdmFileId) << ", " << index
              << " => " << PathIdPP(checkerHtmlFileId) << std::endl;
  }
  return checkerHtmlFileId;
}

bool PlatformFileSystem::rename(PathId whatId, PathId toId) {
  if (!whatId || !toId) return false;

  const std::filesystem::path what = toPath(whatId);
  const std::filesystem::path to = toPath(toId);

  if (what.empty() || to.empty()) return false;

  std::error_code ec;
  std::filesystem::rename(what, to, ec);
  return !ec;
}

bool PlatformFileSystem::remove(PathId fileId) {
  if (!fileId) return false;

  const std::filesystem::path file = toPath(fileId);
  if (file.empty()) return false;

  std::error_code ec;
  if (!std::filesystem::exists(file) && !ec) {
    return true;
  }

  if (!std::filesystem::remove(file, ec) && ec) {
    return false;
  }

  return !std::filesystem::exists(file, ec) && !ec;
}

bool PlatformFileSystem::mkdir(PathId dirId) {
  if (!dirId) return false;

  const std::filesystem::path dir = toPath(dirId);
  if (dir.empty()) return false;

  std::error_code ec;
  if ((std::filesystem::exists(dir, ec) && !ec) &&
      (std::filesystem::is_directory(dir, ec) && !ec)) {
    return true;
  }

  if (!std::filesystem::create_directory(dir, ec) || ec) {
    return false;
  }

  return std::filesystem::is_directory(dir, ec) && !ec;
}

bool PlatformFileSystem::rmdir(PathId dirId) {
  if (!dirId) return false;

  const std::filesystem::path dir = toPath(dirId);
  if (dir.empty()) return false;

  std::error_code ec;
  if ((!std::filesystem::exists(dir, ec) && !ec) ||
      (!std::filesystem::is_directory(dir, ec) && !ec)) {
    return true;
  }

  if (!std::filesystem::remove(dir, ec) || ec) {
    return false;
  }

  return !std::filesystem::exists(dir, ec) && !ec;
}

bool PlatformFileSystem::mkdirs(PathId dirId) {
  if (!dirId) return false;

  const std::filesystem::path dir = toPath(dirId);
  if (dir.empty()) return false;

  std::error_code ec;
  if ((std::filesystem::exists(dir, ec) && !ec) &&
      (std::filesystem::is_directory(dir, ec) && !ec)) {
    return true;
  }

  // CAUTION: There is a known bug in VC compiler where a trailing
  // slash in the path will cause a false return from a call to
  // fs::create_directories.
  // if (!std::filesystem::create_directories(dir, ec) || ec) {
  std::filesystem::create_directories(dir, ec);
  if (ec) return false;

  return std::filesystem::is_directory(dir, ec) && !ec;
}

bool PlatformFileSystem::rmtree(PathId dirId) {
  if (!dirId) return false;

  const std::filesystem::path dir = toPath(dirId);
  if (dir.empty()) return false;

  std::error_code ec;
  if ((!std::filesystem::exists(dir, ec) && !ec) ||
      (!std::filesystem::is_directory(dir, ec) && !ec)) {
    return true;
  }

  if (!std::filesystem::remove_all(dir, ec) || ec) {
    return false;
  }

  return !std::filesystem::exists(dir, ec) && !ec;
}

bool PlatformFileSystem::exists(PathId id) {
  if (!id) return false;

  const std::filesystem::path filepath = toPath(id);

  std::error_code ec;
  return !filepath.empty() && std::filesystem::exists(filepath, ec) && !ec;
}

bool PlatformFileSystem::exists(PathId dirId, std::string_view descendant) {
  if (!dirId || descendant.empty()) return false;

  std::filesystem::path filepath = toPath(dirId);
  filepath /= descendant;

  std::error_code ec;
  return !filepath.empty() && std::filesystem::exists(filepath, ec) && !ec;
}

bool PlatformFileSystem::isDirectory(PathId id) {
  if (!id) return false;

  const std::filesystem::path dirpath = toPath(id);

  std::error_code ec;
  return !dirpath.empty() && std::filesystem::exists(dirpath, ec) && !ec &&
         std::filesystem::is_directory(dirpath, ec) && !ec;
}

bool PlatformFileSystem::isRegularFile(PathId id) {
  if (!id) return false;

  const std::filesystem::path filepath = toPath(id);

  std::error_code ec;
  return !filepath.empty() && std::filesystem::exists(filepath, ec) && !ec &&
         std::filesystem::is_regular_file(filepath, ec) && !ec;
}

bool PlatformFileSystem::filesize(PathId fileId, std::streamsize *result) {
  if (!fileId) return false;

  const std::filesystem::path filepath = toPath(fileId);
  if (filepath.empty()) return false;

  std::error_code ec;
  std::streamsize length = std::filesystem::file_size(filepath, ec);
  if (!ec) {
    if (result != nullptr) {
      *result = length;
    }
    return true;
  }
  return false;
}

std::filesystem::file_time_type PlatformFileSystem::modtime(
    PathId fileId, std::filesystem::file_time_type defaultOnFail) {
  if (!fileId) return defaultOnFail;

  const std::filesystem::path filepath = toPath(fileId);
  if (filepath.empty()) return defaultOnFail;

  std::error_code ec;
  if (!std::filesystem::exists(filepath) || ec) {
    return defaultOnFail;
  }

  std::filesystem::file_time_type lmt =
      std::filesystem::last_write_time(filepath, ec);
  return ec ? defaultOnFail : lmt;
}

PathId PlatformFileSystem::locate(std::string_view name,
                                  const PathIdVector &directories,
                                  SymbolTable *symbolTable) {
  if (name.empty()) return BadPathId;

  std::error_code ec;
  for (const PathId &dirId : directories) {
    if (dirId) {
      const std::filesystem::path filepath =
          normalize(std::filesystem::path(toPath(dirId)) / name);
      if (!filepath.empty() && std::filesystem::exists(filepath, ec) && !ec) {
        return toPathId(filepath.string(), symbolTable);
      }
    }
  }

  return BadPathId;
}

PathIdVector &PlatformFileSystem::collect(PathId dirId,
                                          std::string_view extension,
                                          SymbolTable *symbolTable,
                                          PathIdVector &container) {
  if (!dirId) return container;

  const std::filesystem::path dirpath = toPath(dirId);
  if (dirpath.empty()) return container;

  std::error_code ec;
  if (std::filesystem::is_directory(dirpath, ec) && !ec) {
    for (const std::filesystem::directory_entry &entry :
         std::filesystem::directory_iterator(dirpath)) {
      const std::filesystem::path &filepath = entry.path();
      if (extension.empty() || (filepath.extension() == extension)) {
        if (std::filesystem::is_regular_file(filepath, ec) && !ec) {
          container.emplace_back(toPathId(filepath.string(), symbolTable));
        }
      }
    }
  }

  return container;
}

PathIdVector &PlatformFileSystem::collect(PathId dirId,
                                          SymbolTable *symbolTable,
                                          PathIdVector &container) {
  return dirId ? collect(dirId, "", symbolTable, container) : container;
}

PathIdVector &PlatformFileSystem::matching(PathId dirId,
                                           std::string_view pattern,
                                           SymbolTable *symbolTable,
                                           PathIdVector &container) {
  if (!dirId) return container;

  // ?   single character wildcard (matches any single character)
  // *   multiple character wildcard (matches any number of characters in a
  // directory/file name)
  // ... hierarchical wildcard (matches any number of hierarchical directories)
  // ..  specifies the parent directory
  // .   specifies the directory containing the lib.map
  // Paths that end in / shall include all files in the specified directory.
  // Identical to / * Paths that do not begin with / are relative to the
  // directory in which the current lib.map file is located.

  std::error_code ec;
  std::filesystem::path prefix = toPath(dirId);
  if (prefix.empty()) return container;

  std::filesystem::path suffix;
  for (const std::filesystem::path &part : std::filesystem::path(pattern)) {
    if (part == ".") {
      continue;
    } else if (!suffix.empty()) {
      suffix /= part;
    } else if (part.string().find_first_of(".?*") == std::string::npos) {
      prefix /= part;
    } else {
      suffix /= part;
    }
  }

  if (suffix.empty()) {
    return collect(toPathId(prefix.string(), symbolTable), symbolTable,
                   container);
  }

  prefix = std::filesystem::weakly_canonical(prefix, ec);
  if (ec) return container;

  const std::string separator(1, std::filesystem::path::preferred_separator);
  const std::string escaped = "\\" + separator;

  std::string regexp = suffix.string();
  regexp = StringUtils::replaceAll(regexp, separator,
                                   escaped);  // escape separators
  regexp = StringUtils::replaceAll(regexp, StrCat("...", escaped),
                                   StrCat(R"([a-zA-Z0-9_\-.)", escaped, R"(]+)",
                                          escaped));  // separator allowed
  regexp = StringUtils::replaceAll(
      regexp, StrCat("..", escaped),
      StrCat(R"([a-zA-Z0-9_\-.]+)", escaped, R"([a-zA-Z0-9_\-.]+)",
             escaped));  // separator NOT allowed
  regexp = StringUtils::replaceAll(regexp, ".", "\\.");  // escape it
  regexp = StringUtils::replaceAll(regexp, "?",
                                   R"([a-zA-Z0-9_\-\.])");  // at most one
  regexp = StringUtils::replaceAll(
      regexp, "*", StrCat("[^", escaped, "]*"));  // free for all

  const std::regex regex(regexp);
  const std::filesystem::directory_options options =
      std::filesystem::directory_options::skip_permission_denied |
      std::filesystem::directory_options::follow_directory_symlink;

  for (const std::filesystem::directory_entry &entry :
       std::filesystem::recursive_directory_iterator(prefix, options)) {
    const std::filesystem::path &absolute = entry.path();
    if (std::filesystem::is_regular_file(absolute, ec) && !ec) {
      const std::string relative =
          std::filesystem::relative(absolute, prefix, ec).string();
      std::smatch match;
      if (!ec && std::regex_match(relative, match, regex)) {
        if (std::filesystem::is_regular_file(absolute, ec) && !ec) {
          container.emplace_back(toPathId(absolute.string(), symbolTable));
        }
      }
    }
  }

  return container;
}

PathId PlatformFileSystem::getChild(PathId id, std::string_view name,
                                    SymbolTable *symbolTable) {
  if (!id) return BadPathId;

  std::filesystem::path filepath = toPath(id);
  if (filepath.empty()) return BadPathId;

  return toPathId((filepath / name).string(), symbolTable);
}

PathId PlatformFileSystem::getSibling(PathId id, std::string_view name,
                                      SymbolTable *symbolTable) {
  if (!id) return BadPathId;

  std::filesystem::path filepath = toPath(id);
  if (filepath.empty()) return BadPathId;

  return filepath.has_parent_path()
             ? toPathId((filepath.parent_path() / name).string(), symbolTable)
             : toPathId(name, symbolTable);
}

PathId PlatformFileSystem::getParent(PathId id, SymbolTable *symbolTable) {
  if (!id) return BadPathId;

  std::filesystem::path filepath = toPath(id);
  if (filepath.empty()) return BadPathId;

  return filepath.has_parent_path()
             ? toPathId(filepath.parent_path().string(), symbolTable)
             : toPathId(".", symbolTable);
}

std::pair<SymbolId, std::string_view> PlatformFileSystem::getLeaf(
    PathId id, SymbolTable *symbolTable) {
  if (!id) return {BadSymbolId, BadRawSymbol};

  const std::filesystem::path filepath = toPath(id);
  if (!filepath.has_filename()) {
    return {BadSymbolId, BadRawSymbol};
  }

  return symbolTable->add(filepath.filename().string());
}

std::pair<SymbolId, std::string_view> PlatformFileSystem::getType(
    PathId id, SymbolTable *symbolTable) {
  if (!id) return {BadSymbolId, BadRawSymbol};

  const std::filesystem::path filepath = toPath(id);
  if (!filepath.has_extension()) {
    return {BadSymbolId, BadRawSymbol};
  }

  return symbolTable->add(filepath.extension().string());
}

void PlatformFileSystem::printConfiguration(std::ostream &out) {
  out << "=== FileSystem Configuration ===" << std::endl;
  for (const Configuration &configuration : m_configurations) {
    out << configuration.m_sourceDir << " => " << configuration.m_cacheDir
        << std::endl;
  }
  out << "=== === ===" << std::endl;
}
}  // namespace SURELOG
