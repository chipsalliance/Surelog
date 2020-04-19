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
#include <map>
#include "uhdm.h"
#include "SourceCompile/SymbolTable.h"
#include "Utils/StringUtils.h"
#include "Library/Library.h"
#include "Design/FileContent.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/Location.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "CommandLine/CommandLineParser.h"
#include "SourceCompile/ParseFile.h"
#include "Testbench/ClassDefinition.h"
#include "SourceCompile/Compiler.h"
#include "DesignCompile/CompileDesign.h"
#include "DesignCompile/ResolveSymbols.h"
#include "DesignCompile/DesignElaboration.h"
#include "DesignCompile/UVMElaboration.h"
#include "DesignCompile/CompilePackage.h"
#include "DesignCompile/CompileModule.h"
#include "DesignCompile/CompileFileContent.h"
#include "DesignCompile/CompileProgram.h"
#include "DesignCompile/CompileClass.h"
#include "DesignCompile/Builtin.h"
#include "DesignCompile/PackageAndRootElaboration.h"
#include "Design/ModuleInstance.h" 
#include "Design/Netlist.h"
#include "surelog.h"
#include "UhdmChecker.h"
#include "vpi_visitor.h"
#include "Serializer.h"
#include "module.h"

using namespace SURELOG;
using namespace UHDM;

UhdmChecker::~UhdmChecker() {
}

typedef std::map<FileContent*, std::map<unsigned int, bool>> FileNodeCoverMap;
static FileNodeCoverMap fileNodeCoverMap;
static std::map<std::string, FileContent*> fileMap;

bool registerFile(FileContent* fC) {
  VObject current = fC->Object(fC->getSize() - 2);
  NodeId id = current.m_child;
  if (!id) id = current.m_sibling;
  if (!id) return false;
  std::stack<NodeId> stack;
  stack.push(id);

  FileNodeCoverMap::iterator fileItr = fileNodeCoverMap.find(fC);
  if (fileItr == fileNodeCoverMap.end()) {
    std::map<unsigned int, bool> uhdmCover;
    fileNodeCoverMap.insert(std::make_pair(fC, uhdmCover));
    fileItr = fileNodeCoverMap.find(fC);
  } 
  std::map<unsigned int, bool>& uhdmCover = (*fileItr).second; 

  while (stack.size()) {
    id = stack.top();
    stack.pop();
    current = fC->Object(id);
    if (current.m_sibling) 
      stack.push(current.m_sibling);
    if (current.m_child) 
       stack.push(current.m_child);
    if (current.m_type == VObjectType::slEnd ||
        current.m_type == VObjectType::slEndcase)
      continue;  
    uhdmCover.insert(std::make_pair(current.m_line, false));
  }
  return true;
}

bool report(std::string reportFile) {
  std::ofstream report;
  report.open(reportFile);
  if (report.bad())
    return false;

  for (FileNodeCoverMap::iterator fileItr = fileNodeCoverMap.begin(); fileItr != fileNodeCoverMap.end(); fileItr++) {
    FileContent* fC = (*fileItr).first;
    std::map<NodeId, bool>& uhdmCover = (*fileItr).second; 
    bool fileNamePrinted = false;
    for (std::map<NodeId, bool>::iterator cItr = uhdmCover.begin(); cItr != uhdmCover.end(); cItr++) {
      if ((*cItr).second == false) { 
        if (fileNamePrinted == false) {
          report << "\n\nMissing models in : " << fC->getFileName() << ":" << (*cItr).first << ":\n\n";
          fileNamePrinted = true;
        }
        report << "Line: " <<(*cItr).first << "\n"; 
      }
    }
  }

  report.close();
  return true;
}

void annotate(CompileDesign* m_compileDesign) {
  Serializer& s = m_compileDesign->getSerializer();
  std::unordered_map<const BaseClass*, unsigned long>& objects = s.AllObjects();
  for (auto& obj : objects) {
    const BaseClass* bc = obj.first;
    if (!bc)
      continue;
    const std::string& fn = bc->VpiFile();
    std::map<std::string, FileContent*>::iterator fItr =  fileMap.find(fn);
    if (fItr != fileMap.end()) {
      FileContent* fC = (*fItr).second;
      FileNodeCoverMap::iterator fileItr = fileNodeCoverMap.find(fC);
      if (fileItr != fileNodeCoverMap.end()) {
        std::map<unsigned int, bool>& uhdmCover = (*fileItr).second;
        std::map<unsigned int, bool>::iterator lineItr =  uhdmCover.find(bc->VpiLineNo());
        if (lineItr != uhdmCover.end()) {
          (*lineItr).second = true;
        }
      }
    }
  }
}

bool UhdmChecker::check(std::string reportFile) {
  // Register all objects location in file content
  for (auto idContent : m_design->getAllFileContents()) {
    SymbolId fid = idContent.first;
    FileContent* fC = idContent.second;
    SymbolTable* symbols = m_compileDesign->getCompiler()->getSymbolTable();
    std::string fileName = symbols->getSymbol(fid);
    if (strstr(fileName.c_str(), "builtin.sv")
     || strstr(fileName.c_str(), "uvm_pkg.sv")
     || strstr(fileName.c_str(), "ovm_pkg.sv")) {
      continue;
    }

    fileMap.insert(std::make_pair(fileName, fC));
    registerFile(fC);
  }

  // Annotate UHDM object coverage
  annotate(m_compileDesign);

  // Report uncovered objects
  report(reportFile);

  return true;
}
