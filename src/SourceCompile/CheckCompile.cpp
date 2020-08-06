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
 * File:   CheckCompile.cpp
 * Author: alain
 *
 * Created on June 10, 2017, 10:15 PM
 */
#include <iostream>
#include <set>
#include "SourceCompile/SymbolTable.h"
#include "Design/TimeInfo.h"
#include "Design/DesignElement.h"
#include "Design/FileContent.h"
#include "ErrorReporting/Location.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/ParseFile.h"
#include "CommandLine/CommandLineParser.h"
#include "SourceCompile/CheckCompile.h"

using namespace SURELOG;

CheckCompile::~CheckCompile() {}

bool CheckCompile::check() {
  if (!checkSyntaxErrors_()) return false;
  if (!mergeSymbolTables_()) return false;
  if (!checkTimescale_()) return false;
  return true;
}

bool CheckCompile::checkSyntaxErrors_() {
  ErrorContainer* errors = m_compiler->getErrorContainer();
  const SURELOG::ErrorContainer::Stats& stats = errors->getErrorStats();
  if (stats.nbSyntax)
    return false;
  return true;
}

bool CheckCompile::mergeSymbolTables_() {
  Design::FileIdDesignContentMap& all_files =
      m_compiler->getDesign()->getAllFileContents();
  for (auto fitr = all_files.begin(); fitr != all_files.end(); fitr++) {
    auto fileContent = (*fitr).second;
    m_compiler->getSymbolTable()->registerSymbol(fileContent->getFileName());
    for (NodeId id : fileContent->getNodeIds()) {
      *fileContent->getMutableFileId(id) =
        m_compiler->getSymbolTable()->registerSymbol(
          fileContent->getSymbolTable()->getSymbol(fileContent->getFileId(id)));
    }
    for (DesignElement& elem : fileContent->getDesignElements()) {
      elem.m_name = m_compiler->getSymbolTable()->registerSymbol(
          fileContent->getSymbolTable()->getSymbol(elem.m_name));
      elem.m_fileId = m_compiler->getSymbolTable()->registerSymbol(
          fileContent->getSymbolTable()->getSymbol(
              fileContent->getFileId(elem.m_node)));
    }
  }
  return true;
}

bool CheckCompile::checkTimescale_() {
  std::string globaltimescale =
      m_compiler->getCommandLineParser()->getTimeScale();
  if (!globaltimescale.empty()) {
    Location loc(0, 0, 0,
                 m_compiler->getSymbolTable()->registerSymbol(globaltimescale));
    Error err(ErrorDefinition::CMD_USING_GLOBAL_TIMESCALE, loc);
    m_compiler->getErrorContainer()->addError(err);
    return true;
  }

  bool timeUnitUsed = false;
  bool timeScaleUsed = false;
  std::vector<Location> noTimeUnitLocs;
  Design::FileIdDesignContentMap& all_files =
      m_compiler->getDesign()->getAllFileContents();
  std::unordered_set<SymbolId> reportedMissingTimescale;
  std::unordered_set<SymbolId> reportedMissingTimeunit;
  for (auto fitr = all_files.begin(); fitr != all_files.end(); fitr++) {
    auto fileContent = (*fitr).second;
    for (auto elem : fileContent->getDesignElements()) {
      if (elem.m_type == DesignElement::Module ||
          elem.m_type == DesignElement::Interface ||
          elem.m_type == DesignElement::Package ||
          elem.m_type == DesignElement::Primitive ||
          elem.m_type == DesignElement::Program) {
        if (elem.m_timeInfo.m_type == TimeInfo::Type::TimeUnitTimePrecision) {
          timeUnitUsed = true;
        } else if (elem.m_timeInfo.m_type == TimeInfo::Type::Timescale) {
          timeScaleUsed = true;
          Location loc(m_compiler->getSymbolTable()->registerSymbol(
                           fileContent->getSymbolTable()->getSymbol(
                               fileContent->getFileId(elem.m_node))),
                       elem.m_line, 0, elem.m_name);
          noTimeUnitLocs.push_back(loc);
        } else {
          Location loc(m_compiler->getSymbolTable()->registerSymbol(
                           fileContent->getSymbolTable()->getSymbol(
                               fileContent->getFileId(elem.m_node))),
                       elem.m_line, 0, elem.m_name);
          noTimeUnitLocs.push_back(loc);
          if (reportedMissingTimescale.find(elem.m_name) ==
              reportedMissingTimescale.end()) {
            reportedMissingTimescale.insert(elem.m_name);
            Error err(ErrorDefinition::PA_NOTIMESCALE_INFO, loc);
            m_compiler->getErrorContainer()->addError(err);
          }
        }
      }
    }
  }
  if (timeUnitUsed && timeScaleUsed) {
    for (auto loc : noTimeUnitLocs) {
      if (reportedMissingTimeunit.find(loc.m_object) ==
          reportedMissingTimeunit.end()) {
        reportedMissingTimeunit.insert(loc.m_object);
        Error err(ErrorDefinition::PA_MISSING_TIMEUNIT, loc);
        m_compiler->getErrorContainer()->addError(err);
      }
    }
  }

  return true;
}
