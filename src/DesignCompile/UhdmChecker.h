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

#ifndef UHDMCHECKER_H
#define UHDMCHECKER_H

#include <map>
#include <set>
#include <string>
#include <vector>

#include "Design/Design.h"
#include "Design/FileContent.h"
#include "DesignCompile/CompileDesign.h"

namespace SURELOG {

class UhdmChecker final {
 public:
  UhdmChecker(CompileDesign* compiler, Design* design)
      : m_compileDesign(compiler), m_design(design) {}

  // Technically not a const method as it modifies some static values.
  bool check(const std::string& reportFile);

 private:
  bool registerFile(const FileContent* fC, std::set<std::string>& moduleNames);
  bool reportHtml(CompileDesign* compileDesign, const std::string& reportFile,
                  float overallCoverage);
  float reportCoverage(const std::string& reportFile);
  void annotate(CompileDesign* m_compileDesign);
  void mergeColumnCoverage();
  CompileDesign* const m_compileDesign;
  Design* const m_design;
  typedef unsigned int LineNb;
  enum Status { EXIST, COVERED, UNSUPPORTED };
  class ColRange {
   public:
    unsigned short from;
    unsigned short to;
    Status covered;
  };
  typedef std::vector<ColRange> Ranges;
  typedef std::map<LineNb, Ranges> RangesMap;
  typedef std::map<const FileContent*, RangesMap> FileNodeCoverMap;
  FileNodeCoverMap fileNodeCoverMap;
  std::map<std::string, const FileContent*, std::less<>> fileMap;
  std::multimap<float, std::pair<std::string, float>, std::less<>> coverageMap;
  std::map<std::string, float, std::less<>> fileCoverageMap;
};

}  // namespace SURELOG

#endif /* UHDMCHECKER_H */
