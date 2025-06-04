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
 * File:   UhdmWriter.h
 * Author: alain
 *
 * Created on January 17, 2020, 9:12 PM
 */

#ifndef SURELOG_UHDMCHECKER_H
#define SURELOG_UHDMCHECKER_H
#pragma once

#include <Surelog/Common/PathId.h>

#include <cstdint>
#include <map>
#include <set>
#include <string_view>
#include <utility>
#include <vector>

namespace SURELOG {
class CompileDesign;
class Design;
class FileContent;
class Session;

class UhdmChecker final {
 public:
  UhdmChecker(Session* session, CompileDesign* compileDesign, Design* design)
      : m_session(session), m_compileDesign(compileDesign), m_design(design) {}

  // Technically not a const method as it modifies some static values.
  bool check(PathId uhdmFileId);

 private:
  bool registerFile(const FileContent* fC,
                    std::set<std::string_view>& moduleNames);
  bool reportHtml(PathId uhdmFileId, float overallCoverage);
  float reportCoverage(PathId uhdmFileId);
  void annotate();
  void mergeColumnCoverage();

  Session* const m_session = nullptr;
  CompileDesign* const m_compileDesign = nullptr;
  Design* const m_design = nullptr;
  using LineNb = uint32_t;
  enum Status { EXIST, COVERED, UNSUPPORTED };
  class ColRange {
   public:
    uint16_t from;
    uint16_t to;
    Status covered;
  };
  using Ranges = std::vector<ColRange>;
  using RangesMap = std::map<LineNb, Ranges>;
  using FileNodeCoverMap = std::map<const FileContent*, RangesMap>;
  FileNodeCoverMap m_fileNodeCoverMap;
  std::map<PathId, const FileContent*, PathIdLessThanComparer> m_fileMap;
  std::multimap<float, std::pair<PathId, float>> m_coverageMap;
  std::map<PathId, float, PathIdLessThanComparer> m_fileCoverageMap;
};

}  // namespace SURELOG

#endif /* SURELOG_UHDMCHECKER_H */
