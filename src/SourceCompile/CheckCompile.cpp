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

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Design/Design.h>
#include <Surelog/Design/DesignElement.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/SourceCompile/CheckCompile.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>

#include <iostream>
#include <set>

namespace SURELOG {

bool CheckCompile::check() {
  if (!checkSyntaxErrors_()) return false;
  if (!mergeSymbolTables_()) return false;
  if (!checkTimescale_()) return false;
  return true;
}

bool CheckCompile::checkSyntaxErrors_() {
  ErrorContainer* errors = m_compiler->getErrorContainer();
  const SURELOG::ErrorContainer::Stats& stats = errors->getErrorStats();
  if (stats.nbSyntax) return false;
  return true;
}

bool CheckCompile::mergeSymbolTables_() {
  const Design::FileIdDesignContentMap& all_files =
      m_compiler->getDesign()->getAllFileContents();
  for (const auto& sym_file : all_files) {
    const auto fileContent = sym_file.second;
    m_compiler->getSymbolTable()->registerSymbol(
        fileContent->getFileName().string());
    for (NodeId id : fileContent->getNodeIds()) {
      *fileContent->getMutableFileId(id) =
          m_compiler->getSymbolTable()->registerSymbol(
              fileContent->getSymbolTable()->getSymbol(
                  fileContent->getFileId(id)));
    }
    for (DesignElement* elem : fileContent->getDesignElements()) {
      elem->m_name = m_compiler->getSymbolTable()->registerSymbol(
          fileContent->getSymbolTable()->getSymbol(elem->m_name));
      elem->m_fileId = m_compiler->getSymbolTable()->registerSymbol(
          fileContent->getSymbolTable()->getSymbol(
              fileContent->getFileId(elem->m_node)));
    }
  }
  return true;
}

bool CheckCompile::checkTimescale_() {
  std::string globaltimescale =
      m_compiler->getCommandLineParser()->getTimeScale();
  if (!globaltimescale.empty()) {
    Location loc(m_compiler->getSymbolTable()->registerSymbol(globaltimescale));
    Error err(ErrorDefinition::CMD_USING_GLOBAL_TIMESCALE, loc);
    m_compiler->getErrorContainer()->addError(err);
    return true;
  }

  bool timeUnitUsed = false;
  bool timeScaleUsed = false;
  std::vector<Location> noTimeUnitLocs;
  Design::FileIdDesignContentMap& all_files =
      m_compiler->getDesign()->getAllFileContents();
  SymbolIdUnorderedSet reportedMissingTimescale;
  SymbolIdUnorderedSet reportedMissingTimeunit;
  for (const auto& sym_file : all_files) {
    const auto fileContent = sym_file.second;
    for (auto elem : fileContent->getDesignElements()) {
      if (elem->m_type == DesignElement::Module ||
          elem->m_type == DesignElement::Interface ||
          elem->m_type == DesignElement::Package ||
          elem->m_type == DesignElement::Primitive ||
          elem->m_type == DesignElement::Program) {
        if (elem->m_timeInfo.m_type == TimeInfo::Type::TimeUnitTimePrecision) {
          timeUnitUsed = true;
        } else if (elem->m_timeInfo.m_type == TimeInfo::Type::Timescale) {
          timeScaleUsed = true;
          Location loc(m_compiler->getSymbolTable()->registerSymbol(
                           fileContent->getSymbolTable()->getSymbol(
                               fileContent->getFileId(elem->m_node))),
                       elem->m_line, elem->m_column, elem->m_name);
          noTimeUnitLocs.push_back(loc);
        } else {
          Location loc(m_compiler->getSymbolTable()->registerSymbol(
                           fileContent->getSymbolTable()->getSymbol(
                               fileContent->getFileId(elem->m_node))),
                       elem->m_line, elem->m_column, elem->m_name);
          noTimeUnitLocs.push_back(loc);
          if (reportedMissingTimescale.find(elem->m_name) ==
              reportedMissingTimescale.end()) {
            reportedMissingTimescale.insert(elem->m_name);
            Error err(ErrorDefinition::PA_NOTIMESCALE_INFO, loc);
            m_compiler->getErrorContainer()->addError(err);
          }
        }
      }
    }
  }
  if (timeUnitUsed && timeScaleUsed) {
    for (const auto& loc : noTimeUnitLocs) {
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
}  // namespace SURELOG
