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
 * File:   main.cpp
 * Author: alain
 *
 * Created on January 15, 2017, 12:15 AM
 */

#include <cstdlib>
#include <iostream>
#include <string>
#include<stdio.h>
#include<sys/types.h>
#include <unistd.h>
#include "CommandLine/CommandLineParser.h"
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "ErrorReporting/ErrorContainer.h"
#include "ErrorReporting/Report.h"
#include "ErrorReporting/Waiver.h"
#include "antlr4-runtime.h"
using namespace antlr4;
#include "API/PythonAPI.h"

std::pair<bool, bool> executeCompilation(int argc, const char ** argv, bool diff_comp_mode, bool fileunit)
{
  bool success = true;
  bool noFatalErrors = true;
  SURELOG::SymbolTable* symbolTable = new SURELOG::SymbolTable ();
  SURELOG::ErrorContainer* errors = new SURELOG::ErrorContainer (symbolTable);
  SURELOG::CommandLineParser* clp = new SURELOG::CommandLineParser (errors, symbolTable, diff_comp_mode, fileunit);
  success = clp->parseCommandLine (argc, argv);
  errors->printMessages (clp->muteStdout ());
  if (success && (!clp->help()))
    {
      SURELOG::Compiler* compiler = new SURELOG::Compiler (clp, errors, symbolTable);
      success = compiler->compile ();
      delete compiler;
    }
  SURELOG::ErrorContainer::Stats stats;
  if (!clp->help()) 
    stats = errors->getErrorStats ();
  bool noFErrors = true;
  if (!clp->help())
     noFErrors = errors->printStats (stats,clp->muteStdout ());
  if (noFErrors == false)
    {
      noFatalErrors = false;
    }
  clp->logFooter();
  if (diff_comp_mode && fileunit) 
    {
       SURELOG::Report* report = new SURELOG::Report();
       std::pair<bool, bool> results = report->makeDiffCompUnitReport(clp, symbolTable );
       success = results.first;
       noFatalErrors = results.second;   
       delete report;
    }
  delete clp;
  delete symbolTable;
  delete errors;
  return std::make_pair (success, noFatalErrors);  
}

int
main (int argc, const char ** argv)
{
 
  SURELOG::Waiver::initWaivers();
   
  bool success       = false;
  bool noFatalErrors = true;
  bool diff_comp_mode = false;
  bool python_mode = true;
  std::string diff_unit_opt = "-diffcompunit";
  std::string nopython_opt = "-nopython";
 
  for (int i = 1; i < argc; i++)
    {
      if (diff_unit_opt == argv[i])
        {
          diff_comp_mode = true;
        }
      if (nopython_opt == argv[i])
        {
          python_mode = false;
        }   
    }
  
  if (python_mode)
    SURELOG::PythonAPI::init(argc, argv);
  
  if (diff_comp_mode == true)
    {

      pid_t pid = fork ();
      if (pid == 0)
        {
          // child process
          executeCompilation (argc, argv, true, false);
        }
      else if (pid > 0)
        {
          // parent process
          std::pair<bool, bool> results = executeCompilation (argc, argv, true, true);
          success = results.first;
          noFatalErrors = results.second;
        }
      else
        {
          // fork failed
          printf ("fork() failed!\n");
          return 1;
        }
           
    }
  else 
    {
      std::pair<bool, bool> results = executeCompilation(argc, argv, false, false);
      success = results.first;
      noFatalErrors = results.second;
    }
  if (python_mode)
    SURELOG::PythonAPI::shutdown();
  return ((!success) || (!noFatalErrors));
}


