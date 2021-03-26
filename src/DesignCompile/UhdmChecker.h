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

#include <string>

namespace SURELOG {

class UhdmChecker final {
public:
  UhdmChecker(CompileDesign* compiler, Design* design)
    : m_compileDesign(compiler), m_design(design) {}

  // Technically not a const method as it modifies some static values.
  bool check(const std::string& reportFile);

private:
    bool registerFile(const FileContent* fC, std::set<std::string>& moduleNames);
    bool reportHtml(CompileDesign* compileDesign, const std::string& reportFile, float overallCoverage);
    float reportCoverage(const std::string& reportFile);
    void annotate(CompileDesign* m_compileDesign);

    CompileDesign* const m_compileDesign;
    Design* const m_design;

    typedef std::map<const FileContent*, std::map<unsigned int, int>> FileNodeCoverMap;  
    FileNodeCoverMap fileNodeCoverMap;
    std::map<std::string, const FileContent*> fileMap;
    std::multimap<float, std::pair<std::string, float>> coverageMap;
    std::map<std::string, float> fileCoverageMap;

};

} // namespace SURELOG

#endif /* UHDMCHECKER_H */
