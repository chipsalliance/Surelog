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
 * File:   UhdmChecker.cpp
 * Author: alain
 *
 * Created on January 17, 2020, 9:13 PM
 */

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/ModuleInstance.h>
#include <Surelog/Design/VObject.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/UhdmChecker.h>
#include <Surelog/Library/Library.h>
#include <Surelog/Package/Package.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/FileUtils.h>
#include <Surelog/Utils/StringUtils.h>

// UHDM
#include <uhdm/Serializer.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_visitor.h>

#include <fstream>
#include <iomanip>
#include <sstream>
#include <stack>

namespace SURELOG {

namespace fs = std::filesystem;

using UHDM::BaseClass;
using UHDM::begin;
using UHDM::Serializer;
using UHDM::UHDM_OBJECT_TYPE;
using UHDM::uhdmunsupported_expr;
using UHDM::uhdmunsupported_stmt;
using UHDM::uhdmunsupported_typespec;

bool UhdmChecker::registerFile(const FileContent* fC,
                               std::set<std::string>& moduleNames) {
  VObject current = fC->Object(fC->getSize() - 2);
  NodeId id = current.m_child;
  SymbolId fileId = fC->getSymbolId();
  if (!id) id = current.m_sibling;
  if (!id) return false;
  std::stack<NodeId> stack;
  stack.push(id);

  FileNodeCoverMap::iterator fileItr = fileNodeCoverMap.find(fC);
  if (fileItr == fileNodeCoverMap.end()) {
    RangesMap uhdmCover;
    fileNodeCoverMap.insert(std::make_pair(fC, uhdmCover));
    fileItr = fileNodeCoverMap.find(fC);
  }
  RangesMap& uhdmCover = (*fileItr).second;
  bool skipModule = false;
  NodeId endModuleNode = 0;
  while (!stack.empty()) {
    id = stack.top();
    stack.pop();
    current = fC->Object(id);
    bool skip = false;
    VObjectType type = (VObjectType)current.m_type;
    if (type == VObjectType::slEnd) skip = true;

    // Skip macro expansion which resides in another file (header)
    SymbolId fid = fC->getFileId(id);
    if (fid != fileId) {
      if (current.m_sibling) stack.push(current.m_sibling);
      continue;
    }

    if (type == VObjectType::slModule_declaration) {
      NodeId stId = fC->sl_collect(id, VObjectType::slStringConst,
                                   VObjectType::slAttr_spec);
      if (stId != InvalidNodeId) {
        std::string name =
            fC->getLibrary()->getName() + "@" + fC->SymName(stId);
        if (moduleNames.find(name) == moduleNames.end()) {
          skipModule = true;
        }
      }
      endModuleNode = fC->Parent(id);
      endModuleNode = fC->Sibling(endModuleNode);
    }
    if (type == VObjectType::slDescription || type == VObjectType::slEndcase ||
        type == VObjectType::slEndtask || type == VObjectType::slEndfunction ||
        type == VObjectType::slEndmodule ||
        type == VObjectType::slEndinterface ||
        type == VObjectType::slEndpackage ||
        type == VObjectType::slEndclocking || type == VObjectType::slEndclass ||
        type == VObjectType::slEndgenerate ||
        type == VObjectType::slEndconfig ||
        type == VObjectType::slEndcelldefine_directive ||
        type == VObjectType::slEndgroup ||
        type == VObjectType::slEndprimitive ||
        type == VObjectType::slEndtable || type == VObjectType::slEndprogram ||
        type == VObjectType::slEndchecker ||
        type == VObjectType::slEndproperty ||
        type == VObjectType::slEndspecify ||
        type == VObjectType::slEndsequence ||
        type == VObjectType::slPort_declaration ||
        type == VObjectType::slList_of_ports ||
        type == VObjectType::slList_of_port_declarations ||
        type == VObjectType::slPort ||
        type == VObjectType::slConditional_generate_construct ||
        type == VObjectType::slGenerate_module_conditional_statement ||
        type == VObjectType::slGenerate_interface_conditional_statement ||
        type == VObjectType::slLoop_generate_construct ||
        type == VObjectType::slGenerate_module_loop_statement ||
        type == VObjectType::slGenerate_interface_loop_statement ||
        ((type == VObjectType::slPackage_or_generate_item_declaration) &&
         (current.m_child == 0)) ||  // SEMICOLUMN ALONE ;
        type == VObjectType::slGenerate_block) {
      RangesMap::iterator lineItr = uhdmCover.find(current.m_line);
      if (lineItr != uhdmCover.end()) {
        uhdmCover.erase(lineItr);
      }
      skip = true;  // Only skip the item itself
    }

    if (((type == VObjectType::slStringConst) &&
         (fC->Type(current.m_parent) ==
          slModule_declaration)) ||  // endmodule : name
        ((type == VObjectType::slStringConst) &&
         (fC->Type(current.m_parent) ==
          slPackage_declaration)) ||  // endpackage : name
        ((type == VObjectType::slStringConst) &&
         (fC->Type(current.m_parent) ==
          slFunction_body_declaration)) ||  // endfunction  : name
        ((type == VObjectType::slStringConst) &&
         (fC->Type(current.m_parent) ==
          slTask_declaration)) ||  // endtask : name
        ((type == VObjectType::slStringConst) &&
         (fC->Type(current.m_parent) ==
          slClass_declaration)) ||  // endclass : name
        ((type == VObjectType::slStringConst) &&
         (fC->Type(current.m_parent) ==
          slName_of_instance)) ||  // instance name
        ((type == VObjectType::slStringConst) &&
         (fC->Type(current.m_parent) == slType_declaration))  // struct name
    ) {
      RangesMap::iterator lineItr = uhdmCover.find(current.m_line);
      if (skipModule == false) {
        unsigned short from = fC->Column(id);
        unsigned short to = fC->EndColumn(id);
        if (lineItr != uhdmCover.end()) {
          bool found = false;
          for (ColRange& crange : (*lineItr).second) {
            if ((crange.from >= from) && (crange.to <= to)) {
              found = true;
              crange.from = from;
              crange.to = to;
              crange.covered = Status::COVERED;
              break;
            }
          }
          if (found == false) {
            ColRange crange;
            crange.from = from;
            crange.to = to;
            crange.covered = Status::COVERED;
            (*lineItr).second.push_back(crange);
          }
        } else {
          Ranges ranges;
          ColRange crange;
          crange.from = from;
          crange.to = to;
          crange.covered = Status::COVERED;
          ranges.push_back(crange);
          uhdmCover.insert(std::make_pair(current.m_line, ranges));
        }
      }
      skip = true;  // Only skip the item itself
    }

    if (current.m_sibling) stack.push(current.m_sibling);
    if (current.m_child) stack.push(current.m_child);
    if (skip == false && skipModule == false) {
      unsigned short from = fC->Column(id);
      unsigned short to = fC->EndColumn(id);
      RangesMap::iterator lineItr = uhdmCover.find(current.m_line);
      if (lineItr != uhdmCover.end()) {
        bool found = false;
        for (ColRange& crange : (*lineItr).second) {
          if ((crange.from >= from) && (crange.to <= to)) {
            found = true;
            crange.from = from;
            crange.to = to;
            crange.covered = Status::EXIST;
            break;
          }
        }
        if (found == false) {
          ColRange crange;
          crange.from = from;
          crange.to = to;
          crange.covered = Status::EXIST;
          (*lineItr).second.push_back(crange);
        }
      } else {
        Ranges ranges;
        ColRange crange;
        crange.from = from;
        crange.to = to;
        crange.covered = Status::EXIST;
        ranges.push_back(crange);
        uhdmCover.insert(std::make_pair(current.m_line, ranges));
      }
    }
    if (id == endModuleNode) {
      skipModule = false;
    }
  }
  return true;
}

bool UhdmChecker::reportHtml(CompileDesign* compileDesign,
                             const fs::path& reportFile,
                             float overallCoverage) {
  ErrorContainer* errors = compileDesign->getCompiler()->getErrorContainer();
  SymbolTable* symbols = compileDesign->getCompiler()->getSymbolTable();
  std::ofstream report;
  report.open(reportFile.string() + ".html");
  if (report.bad()) return false;
  report << "\n<!DOCTYPE html>\n<html>\n<head>\n<style>\nbody {\n\n}\np "
            "{\nfont-size: 14px;\n}</style>\n";
  report << "<h2 style=\"text-decoration: underline\">"
         << "Overall Coverage: " << std::setprecision(3) << overallCoverage
         << "%</h2>\n";
  unsigned int fileIndex = 1;
  std::string allUncovered;
  static std::multimap<int, std::string> orderedCoverageMap;
  for (FileNodeCoverMap::iterator fileItr = fileNodeCoverMap.begin();
       fileItr != fileNodeCoverMap.end(); fileItr++) {
    const FileContent* fC = (*fileItr).first;

    std::string fileContent = FileUtils::getFileContent(fC->getFileName());
    std::ofstream reportF;
    std::string fname = "chk" + std::to_string(fileIndex) + ".html";
    fs::path f = FileUtils::getPathName(reportFile) / fname;
    reportF.open(f);
    if (reportF.bad()) return false;
    reportF << "\n<!DOCTYPE html>\n<html>\n<head>\n<style>\nbody {\n\n}\np "
               "{\nfont-size: 14px;\n}</style>\n";
    unsigned int size = fileContent.size();
    const char* str = fileContent.c_str();
    unsigned int count = 1;
    for (unsigned int i = 0; i < size; i++) {
      if (str[i] == '\n') count++;
    }

    RangesMap& uhdmCover = (*fileItr).second;
    float cov = 0.0f;
    std::map<fs::path, float>::iterator itr =
        fileCoverageMap.find(fC->getFileName());
    cov = (*itr).second;
    std::stringstream strst;
    strst << std::setprecision(3) << cov;

    std::string coverage = std::string(" Cov: ") + strst.str() + "% ";
    std::string fileStatGreen =
        "<div style=\"overflow: hidden;\"> <h3 style=\"background-color: "
        "#82E0AA; margin:0; min-width: 110px; padding:10; float: left; \">" +
        coverage +
        "</h3> <h3 style=\"margin:0; padding:10; float: left; \"> <a href=" +
        fname + "> " + fC->getFileName().string() + "</a></h3></div>\n";
    std::string fileStatPink =
        "<div style=\"overflow: hidden;\"> <h3 style=\"background-color: "
        "#FFB6C1; margin:0; min-width: 110px; padding:10; float: left; \">" +
        coverage +
        "</h3> <h3 style=\"margin:0; padding:10; float: left; \"> <a href=" +
        fname + "> " + fC->getFileName().string() + "</a></h3></div>\n";
    std::string fileStatRed =
        "<div style=\"overflow: hidden;\"> <h3 style=\"background-color: "
        "#FF0000; margin:0; min-width: 110px; padding:10; float: left; \">" +
        coverage +
        "</h3> <h3 style=\"margin:0; padding:10; float: left; \"> <a href=" +
        fname + "> " + fC->getFileName().string() + "</a></h3></div>\n";
    std::string fileStatWhite =
        "<h3 style=\"margin:0; padding:0 \"> <a href=" + fname + ">" +
        fC->getFileName().string() + "</a> " + coverage + "</h3>\n";

    reportF << "<h3>" << fC->getFileName() << coverage << "</h3>\n";
    bool uncovered = false;
    std::string pinkCoverage;
    std::string redCoverage;
    for (unsigned int line = 1; line <= count; line++) {
      std::string lineText = StringUtils::getLineInString(fileContent, line);
      lineText = StringUtils::replaceAll(lineText, "\r\n", "");
      lineText = StringUtils::replaceAll(lineText, "\n", "");
      RangesMap::iterator cItr = uhdmCover.find(line);

      if (cItr == uhdmCover.end()) {
        reportF << "<pre style=\"margin:0; padding:0 \">" << std::setw(4)
                << std::to_string(line) << ": " << lineText
                << "</pre>\n";  // white
      } else {
        Ranges& ranges = (*cItr).second;
        bool covered = false;
        bool exist = false;
        bool unsupported = false;
        for (ColRange& crange : ranges) {
          switch (crange.covered) {
            case EXIST:
              exist = true;
              break;
            case COVERED:
              covered = true;
              break;
            case UNSUPPORTED:
              unsupported = true;
              break;
          }
        }

        if (lineText.empty()) {
          Location loc(symbols->registerSymbol(fC->getFileName().string()),
                       line, 0, 0);
          Error err(ErrorDefinition::UHDM_WRONG_COVERAGE_LINE, loc);
          errors->addError(err);
        }
        if (exist && covered && (!unsupported)) {
          // reportF << "<pre style=\"background-color: #FFFFE0; margin:0;
          // padding:0; display: inline-block\">" << std::setw (4) <<
          // std::to_string(line) << ": " << "</pre> <pre
          // style=\"background-color: #C0C0C0; margin:0; padding:0; display:
          // inline-block \">" << lineText << "</pre>\n";  // grey
          reportF << "<pre style=\"background-color: #C0C0C0; margin:0; "
                     "padding:0 \">"
                  << std::setw(4) << std::to_string(line) << ": " << lineText
                  << "</pre>\n";  // grey
        } else if (exist && (!unsupported)) {
          reportF
              << "<pre id=\"id" << line
              << "\" style=\"background-color: #FFB6C1; margin:0; padding:0 \">"
              << std::setw(4) << std::to_string(line) << ": " << lineText
              << "</pre>\n";  // pink
          if (uncovered == false) {
            allUncovered += "<pre></pre>\n";
            allUncovered += fileStatWhite;
            allUncovered += "<pre></pre>\n";
            uncovered = true;
          }
          pinkCoverage = fileStatPink;
          allUncovered +=
              "<pre style=\"background-color: #FFB6C1; margin:0; padding:0 \"> "
              "<a href=" +
              fname + "#id" + std::to_string(line) + ">" + lineText +
              "</a></pre>\n";
        } else if (unsupported) {
          reportF
              << "<pre id=\"id" << line
              << "\" style=\"background-color: #FF0000; margin:0; padding:0 \">"
              << std::setw(4) << std::to_string(line) << ": " << lineText
              << "</pre>\n";  // red
          if (uncovered == false) {
            allUncovered += "<pre></pre>\n";
            allUncovered += fileStatWhite;
            allUncovered += "<pre></pre>\n";
            uncovered = true;
          }
          redCoverage = fileStatRed;
          allUncovered +=
              "<pre style=\"background-color: #FF0000; margin:0; padding:0 \"> "
              "<a href=" +
              fname + "#id" + std::to_string(line) + ">" + lineText +
              "</a></pre>\n";
        } else {
          reportF << "<pre style=\"background-color: #C0C0C0; margin:0; "
                     "padding:0 \">"
                  << std::setw(4) << std::to_string(line) << ": " << lineText
                  << "</pre>\n";  // grey
        }
      }
    }
    if (!redCoverage.empty()) {
      orderedCoverageMap.insert(
          std::make_pair(static_cast<int>(cov), redCoverage));
    } else {
      if (!pinkCoverage.empty()) {
        orderedCoverageMap.insert(
            std::make_pair(static_cast<int>(cov), pinkCoverage));
      }
    }
    if (uncovered == false) {
      orderedCoverageMap.insert(
          std::make_pair(static_cast<int>(cov), fileStatGreen));
    }
    reportF << "</body>\n</html>\n";
    reportF.close();
    fileIndex++;
  }
  for (const auto& covFile : orderedCoverageMap) {
    report << covFile.second << "\n";
  }

  report << "<h2 style=\"text-decoration: underline\">"
         << "All Uncovered: "
         << "</h2>\n";
  report << allUncovered << "\n";
  report << "</body>\n</html>\n";
  report.close();
  return true;
}

void UhdmChecker::mergeColumnCoverage() {
  for (FileNodeCoverMap::iterator fileItr = fileNodeCoverMap.begin();
       fileItr != fileNodeCoverMap.end(); fileItr++) {
    RangesMap& uhdmCover = (*fileItr).second;
    for (RangesMap::iterator cItr = uhdmCover.begin(); cItr != uhdmCover.end();
         cItr++) {
      Ranges& ranges = (*cItr).second;
      Ranges merged;
      for (ColRange& crange : ranges) {
        if (crange.from >= crange.to) {
        } else {
          merged.push_back(crange);
        }
      }
      (*cItr).second = merged;
    }
  }
}

float UhdmChecker::reportCoverage(const fs::path& reportFile) {
  std::ofstream report;
  report.open(reportFile);
  if (report.bad()) return false;
  int overallUncovered = 0;
  int overallLineNb = 0;
  for (FileNodeCoverMap::iterator fileItr = fileNodeCoverMap.begin();
       fileItr != fileNodeCoverMap.end(); fileItr++) {
    const FileContent* fC = (*fileItr).first;
    RangesMap& uhdmCover = (*fileItr).second;
    bool fileNamePrinted = false;
    int lineNb = 0;
    int uncovered = 0;
    int firstUncoveredLine = 0;
    for (RangesMap::iterator cItr = uhdmCover.begin(); cItr != uhdmCover.end();
         cItr++) {
      Ranges& ranges = (*cItr).second;
      bool exist = false;
      bool covered = false;
      bool unsupported = false;
      for (ColRange& crange : ranges) {
        switch (crange.covered) {
          case EXIST:
            exist = true;
            break;
          case COVERED:
            covered = true;
            break;
          case UNSUPPORTED:
            unsupported = true;
            break;
        }
      }

      lineNb++;
      overallLineNb++;
      if ((exist && (!covered)) || unsupported) {
        if (fileNamePrinted == false) {
          firstUncoveredLine = (*cItr).first;
          report << "\n\n"
                 << fC->getFileName() << ":" << (*cItr).first << ": "
                 << " Missing models\n";
          fileNamePrinted = true;
        }
        report << "Line: " << (*cItr).first << "\n";
        uncovered++;
        overallUncovered++;
      }
    }
    float coverage = 0;
    if (lineNb == 0)
      coverage = 100.0f;
    else
      coverage = (lineNb - uncovered) * 100.0f / lineNb;
    if (uncovered) {
      report << "File coverage: " << std::setprecision(3) << coverage << "%\n";
      coverageMap.insert(std::make_pair(
          coverage, std::make_pair(fC->getFileName(), firstUncoveredLine)));
    }
    fileCoverageMap.insert(std::make_pair(fC->getFileName(), coverage));
  }
  float overallCoverage = 0.0f;
  if (overallLineNb == 0)
    overallCoverage = 100.0f;
  else
    overallCoverage =
        (overallLineNb - overallUncovered) * 100.0f / overallLineNb;
  report << "\nOverall coverage: " << std::setprecision(3) << overallCoverage
         << "%\n";
  report << "\nOrdered coverage:\n";
  for (const auto& covFile : coverageMap) {
    report << covFile.second.first << ":" << covFile.second.second << ": "
           << std::setprecision(3) << covFile.first << "% "
           << "\n";
  }
  report.close();
  return overallCoverage;
}

void UhdmChecker::annotate(CompileDesign* m_compileDesign) {
  Serializer& s = m_compileDesign->getSerializer();
  std::unordered_map<const BaseClass*, unsigned long>& objects = s.AllObjects();
  for (auto& obj : objects) {
    const BaseClass* bc = obj.first;
    if (!bc) continue;
    bool unsupported = false;
    UHDM_OBJECT_TYPE ot = bc->UhdmType();
    if ((ot == uhdmunsupported_expr) || (ot == uhdmunsupported_stmt) ||
        (ot == uhdmunsupported_typespec))
      unsupported = true;
    const fs::path& fn = bc->VpiFile();
    const auto& fItr = fileMap.find(fn);
    if (fItr != fileMap.end()) {
      const FileContent* fC = (*fItr).second;
      FileNodeCoverMap::iterator fileItr = fileNodeCoverMap.find(fC);
      if (fileItr != fileNodeCoverMap.end()) {
        RangesMap& uhdmCover = (*fileItr).second;
        RangesMap::iterator cItr = uhdmCover.find(bc->VpiLineNo());

        // unsigned short from = bc->VpiColumnNo();
        // unsigned short to = bc->VpiEndColumnNo();

        if (cItr != uhdmCover.end()) {
          // bool found = false;

          for (ColRange& crange : (*cItr).second) {
            //  if ((crange.from >= from) && (crange.to <= to)) {
            //    found = true;
            //    crange.from = from;
            //    crange.to = to;
            if (unsupported)
              crange.covered = Status::UNSUPPORTED;
            else
              crange.covered = Status::COVERED;
            /*    } else if ((crange.from <= from) && (crange.to >= to)) {
                  if (crange.from < from) {
                    ColRange crange1;
                    crange1.from = crange.from;
                    crange1.to = from;
                    crange1.covered = Status::EXIST;
                    (*cItr).second.push_back(crange1);
                  }
                  if (crange.to > to) {
                    ColRange crange1;
                    crange1.from = to;
                    crange1.to = crange.to;
                    crange1.covered = Status::EXIST;
                    (*cItr).second.push_back(crange1);
                  }
                  found = true;
                  crange.from = from;
                  crange.to = to;
                  if (unsupported)
                    crange.covered = Status::UNSUPPORTED;
                  else
                    crange.covered = Status::COVERED;
                } else if ((from < crange.from) && (to > crange.from) && (to <
               crange.to)) { crange.from = to; ColRange crange1; crange1.from =
               from; crange1.to = to; crange1.covered = Status::COVERED;
                  (*cItr).second.push_back(crange1);
                } else if ((from < crange.to) && (from > crange.from) && (to >
               crange.to)) { crange.to = from; ColRange crange1; crange1.from =
               from; crange1.to = to; crange1.covered = Status::COVERED;
                  (*cItr).second.push_back(crange1);
                } */
          }
          /*
                    if (found == false) {
                      ColRange crange;
                      crange.from = from;
                      crange.to = to;
                      if (unsupported)
                        crange.covered = Status::UNSUPPORTED;
                      else
                        crange.covered = Status::COVERED;
                      (*cItr).second.push_back(crange);
                    }
          */
        }
      }
    }
  }
}

void collectUsedFileContents(std::set<const FileContent*>& files,
                             std::set<std::string>& moduleNames,
                             ModuleInstance* instance) {
  if (instance) {
    DesignComponent* def = instance->getDefinition();
    if (def) {
      moduleNames.insert(def->getName());
      for (auto file : def->getFileContents()) {
        if (file) files.insert(file);
      }
    }
    for (unsigned int index = 0; index < instance->getNbChildren(); index++) {
      collectUsedFileContents(files, moduleNames, instance->getChildren(index));
    }
  }
}

bool UhdmChecker::check(const std::string& reportFile) {
  // Register all objects location in file content
  CommandLineParser* clp =
      m_compileDesign->getCompiler()->getCommandLineParser();
  std::set<const FileContent*> files;
  std::set<std::string> moduleNames;
  for (ModuleInstance* top : m_design->getTopLevelModuleInstances()) {
    collectUsedFileContents(files, moduleNames, top);
  }
  for (const auto& packInfo : m_design->getPackageDefinitions()) {
    Package* pack = packInfo.second;
    for (auto file : pack->getFileContents()) {
      if (file) files.insert(file);
    }
  }

  for (const FileContent* fC : files) {
    const fs::path fileName = fC->getFileName();
    if (!clp->createCache()) {
      if ((fileName.filename().compare("uvm_pkg.sv") == 0) ||
          (fileName.filename().compare("ovm_pkg.sv") == 0)) {
        continue;
      }
    }
    fileMap.insert(std::make_pair(fileName, fC));
    registerFile(fC, moduleNames);
  }

  // Annotate UHDM object coverage
  annotate(m_compileDesign);

  mergeColumnCoverage();

  // Report uncovered objects
  float overallCoverage = reportCoverage(reportFile);
  reportHtml(m_compileDesign, reportFile, overallCoverage);
  return true;
}

}  // namespace SURELOG
