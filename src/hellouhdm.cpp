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
 * File:   hellouhdm.cpp
 * Author: alain
 *
 * Created on April 13, 2020, 08:07 PM
 */

// Example of usage:
// cd tests/UnitElabBlock
// hellouhdm top.v -parse -mutestdout

#include <functional>
#include <iostream>

#include "surelog.h"

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_listener.h>

int main(int argc, const char** argv) {
  // Read command line, compile a design, use -parse argument
  unsigned int code = 0;
  SURELOG::SymbolTable* symbolTable = new SURELOG::SymbolTable();
  SURELOG::ErrorContainer* errors = new SURELOG::ErrorContainer(symbolTable);
  SURELOG::CommandLineParser* clp =
      new SURELOG::CommandLineParser(errors, symbolTable, false, false);
  clp->noPython();
  clp->setParse(true);
  clp->setwritePpOutput(true);
  clp->setCompile(true);
  clp->setElaborate(true);  // Request Surelog instance tree Elaboration
  // clp->setElabUhdm(true);  // Request UHDM Uniquification/Elaboration
  bool success = clp->parseCommandLine(argc, argv);
  errors->printMessages(clp->muteStdout());
  vpiHandle the_design = 0;
  SURELOG::scompiler* compiler = nullptr;
  if (success && (!clp->help())) {
    compiler = SURELOG::start_compiler(clp);
    the_design = SURELOG::get_uhdm_design(compiler);
    auto stats = errors->getErrorStats();
    code = (!success) | stats.nbFatal | stats.nbSyntax | stats.nbError;
  }

  std::string result;

  // If UHDM is not already elaborated/uniquified (uhdm db was saved by a
  // different process pre-elaboration), then optionally elaborate it:
  if (the_design && (!vpi_get(vpiElaborated, the_design))) {
    std::cout << "UHDM Elaboration...\n";
    UHDM::Serializer serializer;
    UHDM::ElaboratorListener* listener =
        new UHDM::ElaboratorListener(&serializer, true);
    listen_designs({the_design}, listener);
  }

  // Browse the UHDM Data Model using the IEEE VPI API.
  // See third_party/Verilog_Object_Model.pdf

  // Either use the
  // - C IEEE API, (See third_party/UHDM/tests/test_helper.h)
  // - or C++ UHDM API (See third_party/UHDM/headers/*.h)
  // - Listener design pattern (See third_party/UHDM/tests/test_listener.cpp)
  // - Walker design pattern (See third_party/UHDM/src/vpi_visitor.cpp)

  if (the_design) {
    UHDM::design* udesign = nullptr;
    if (vpi_get(vpiType, the_design) == vpiDesign) {
      // C++ top handle from which the entire design can be traversed using the
      // C++ API
      udesign = UhdmDesignFromVpiHandle(the_design);
      result += "Design name (C++): " + udesign->VpiName() + "\n";
    }
    // Example demonstrating the classic VPI API traversal of the folded model
    // of the design Flat non-elaborated module/interface/packages/classes list
    // contains ports/nets/statements (No ranges or sizes here, see elaborated
    // section below)
    result +=
        "Design name (VPI): " + std::string(vpi_get_str(vpiName, the_design)) +
        "\n";
    // Flat Module list:
    result += "Module List:\n";
    vpiHandle modItr = vpi_iterate(UHDM::uhdmallModules, the_design);
    while (vpiHandle obj_h = vpi_scan(modItr)) {
      if (vpi_get(vpiType, obj_h) != vpiModule) {
        result += "ERROR: this is not a module\n";
      }
      std::string defName;
      std::string objectName;
      if (const char* s = vpi_get_str(vpiDefName, obj_h)) {
        defName = s;
      }
      if (const char* s = vpi_get_str(vpiName, obj_h)) {
        if (!defName.empty()) {
          defName += " ";
        }
        objectName = std::string("(") + s + std::string(")");
      }
      // ...
      // Iterate thru statements
      // ...
      result += "+ module: " + defName + objectName +
                ", file:" + std::string(vpi_get_str(vpiFile, obj_h)) +
                ", line:" + std::to_string(vpi_get(vpiLineNo, obj_h));
      vpiHandle processItr = vpi_iterate(vpiProcess, obj_h);
      while (vpiHandle sub_h = vpi_scan(processItr)) {
        result += "\n    \\_ process stmt, file:" +
                  std::string(vpi_get_str(vpiFile, sub_h)) +
                  ", line:" + std::to_string(vpi_get(vpiLineNo, sub_h));
        vpi_release_handle(sub_h);
      }
      vpiHandle assignItr = vpi_iterate(vpiContAssign, obj_h);
      while (vpiHandle sub_h = vpi_scan(assignItr)) {
        result += "\n    \\_ assign stmt, file:" +
                  std::string(vpi_get_str(vpiFile, sub_h)) +
                  ", line:" + std::to_string(vpi_get(vpiLineNo, sub_h));
      }
      vpi_release_handle(assignItr);
      // ...
      // Iterate thru ports
      // ...
      result += "\n";
      vpi_release_handle(obj_h);
    }
    vpi_release_handle(modItr);

    // Instance tree:
    // Elaborated Instance tree
    result += "Instance Tree:\n";
    vpiHandle instItr = vpi_iterate(UHDM::uhdmtopModules, the_design);
    while (vpiHandle obj_h = vpi_scan(instItr)) {
      std::function<std::string(vpiHandle, std::string)> inst_visit =
          [&inst_visit](vpiHandle obj_h, std::string margin) {
            std::string res;
            std::string defName;
            std::string objectName;
            if (const char* s = vpi_get_str(vpiDefName, obj_h)) {
              defName = s;
            }
            if (const char* s = vpi_get_str(vpiName, obj_h)) {
              if (!defName.empty()) {
                defName += " ";
              }
              objectName = std::string("(") + s + std::string(")");
            }
            std::string f;
            if (const char* s = vpi_get_str(vpiFile, obj_h)) {
              f = s;
            }
            res += margin + "+ module: " + defName + objectName +
                   ", file:" + f +
                   ", line:" + std::to_string(vpi_get(vpiLineNo, obj_h)) + "\n";

            // Recursive tree traversal
            margin = "  " + margin;
            if (vpi_get(vpiType, obj_h) == vpiModule ||
                vpi_get(vpiType, obj_h) == vpiGenScope) {
              vpiHandle subItr = vpi_iterate(vpiModule, obj_h);
              while (vpiHandle sub_h = vpi_scan(subItr)) {
                res += inst_visit(sub_h, margin);
                vpi_release_handle(sub_h);
              }
              vpi_release_handle(subItr);
            }
            if (vpi_get(vpiType, obj_h) == vpiModule ||
                vpi_get(vpiType, obj_h) == vpiGenScope) {
              vpiHandle subItr = vpi_iterate(vpiGenScopeArray, obj_h);
              while (vpiHandle sub_h = vpi_scan(subItr)) {
                res += inst_visit(sub_h, margin);
                vpi_release_handle(sub_h);
              }
              vpi_release_handle(subItr);
            }
            if (vpi_get(vpiType, obj_h) == vpiGenScopeArray) {
              vpiHandle subItr = vpi_iterate(vpiGenScope, obj_h);
              while (vpiHandle sub_h = vpi_scan(subItr)) {
                res += inst_visit(sub_h, margin);
                vpi_release_handle(sub_h);
              }
              vpi_release_handle(subItr);
            }
            return res;
          };
      result += inst_visit(obj_h, "");
    }
  }
  std::cout << result << std::endl;

  // Do not delete these objects until you are done with UHDM
  SURELOG::shutdown_compiler(compiler);
  delete clp;
  delete symbolTable;
  delete errors;
  return code;
}
