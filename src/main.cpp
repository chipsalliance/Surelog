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

#include <iostream>
#include <string>

#include "surelog.h"
#include "ErrorReporting/Report.h"
#include "API/PythonAPI.h"

unsigned int executeCompilation(int argc, const char ** argv, bool diff_comp_mode, bool fileunit)
{
  bool success = true;
  bool noFatalErrors = true;
  unsigned int codedReturn = 0;
  SURELOG::SymbolTable* symbolTable = new SURELOG::SymbolTable ();
  SURELOG::ErrorContainer* errors = new SURELOG::ErrorContainer (symbolTable);
  SURELOG::CommandLineParser* clp = new SURELOG::CommandLineParser (errors, symbolTable, diff_comp_mode, fileunit);
  success = clp->parseCommandLine (argc, argv);
  bool parseOnly = clp->parseOnly();
  errors->printMessages (clp->muteStdout ());
  if (success && (!clp->help()))
    {
      SURELOG::scompiler* compiler = SURELOG::start_compiler(clp);  
      if (!compiler)
        codedReturn |= 1;
      SURELOG::shutdown_compiler(compiler);
    }
  SURELOG::ErrorContainer::Stats stats;
  if (!clp->help()) {
    stats = errors->getErrorStats ();
    if (stats.nbFatal)
      codedReturn |= 1;
    if (stats.nbSyntax)
      codedReturn |= 2;
    if (stats.nbError)
      codedReturn |= 4;
  }
  bool noFErrors = true;
  if (!clp->help())
     noFErrors = errors->printStats (stats,clp->muteStdout ());
  if (noFErrors == false) {
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
  if ((!noFatalErrors) || (!success))
    codedReturn |= 1;
  if (parseOnly)
    return 0;
  else 
    return codedReturn;  
}

int
main (int argc, const char ** argv)
{
 
  SURELOG::Waiver::initWaivers();
   
  unsigned int codedReturn = 0;
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
          codedReturn = executeCompilation (argc, argv, true, true);
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
      codedReturn = executeCompilation(argc, argv, false, false);
    }
  if (python_mode)
    SURELOG::PythonAPI::shutdown();
  return codedReturn;
}


