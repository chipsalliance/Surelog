/*
 Copyright 2021 Alain Dargelas & Bsp13

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
 * File:   hellodesign.cpp
 * Author: alain & bsp13
 *
 * Created on April 18, 2021, 08:07 PM
 */

// Example of usage:
// cd tests/UnitElabBlock
// hellodesign top.v -parse -mutestdout

#include <Surelog/surelog.h>

#include <functional>
#include <iostream>

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/VpiListener.h>
#include <uhdm/uhdm.h>

class DesignListener final : public UHDM::VpiListener {
  void enterModule(const UHDM::module *const object, vpiHandle handle) final {
    const std::string &instName = object->VpiName();
    m_flatTraversal =
        (instName.empty()) && ((object->VpiParent() == 0) ||
                               ((object->VpiParent() != 0) &&
                                (object->VpiParent()->VpiType() != vpiModule)));
    if (m_flatTraversal)
      std::cout << "Entering Module Definition: " << object->VpiDefName() << " "
                << intptr_t(object) << " " << object->UhdmId() << std::endl;
    else
      std::cout << "Entering Module Instance: " << object->VpiFullName() << " "
                << intptr_t(object) << " " << object->UhdmId() << std::endl;
  }

  void enterCont_assign(const UHDM::cont_assign *object,
                        vpiHandle handle) final {
    if (m_flatTraversal) {
      std::cout << "  Let's skip the cont assigns in the flat traversal and "
                   "only navigate the ones in the hierarchical tree!"
                << std::endl;
    } else {
      std::cout << "  enterCont_assign " << intptr_t(object) << " "
                << object->UhdmId() << std::endl;
    }
  }

 private:
  bool m_flatTraversal = false;
};

static bool Build(const vpiHandle &design_handle) {
  DesignListener listener;
  listener.listenDesigns({design_handle});
  std::cout << "End design traversal" << std::endl;
  return true;
}

int main(int argc, const char **argv) {
  if (argc < 2) return 0;

  // Read command line, compile a design, use -parse argument
  int code = 0;
  SURELOG::SymbolTable *const symbolTable = new SURELOG::SymbolTable();
  SURELOG::ErrorContainer *const errors =
      new SURELOG::ErrorContainer(symbolTable);
  SURELOG::CommandLineParser *const clp =
      new SURELOG::CommandLineParser(errors, symbolTable, false, false);
  clp->noPython();
  clp->setwritePpOutput(true);
  clp->setParse(true);
  clp->setCompile(true);
  clp->setElaborate(true);  // Request Surelog instance tree elaboration
  clp->setElabUhdm(true);   // Request UHDM Uniquification/Elaboration
  bool success = clp->parseCommandLine(argc, argv);
  errors->printMessages(clp->muteStdout());

  vpiHandle vpi_design = nullptr;
  SURELOG::scompiler *compiler = nullptr;
  if (success && (!clp->help())) {
    compiler = SURELOG::start_compiler(clp);
    vpi_design = SURELOG::get_uhdm_design(compiler);
    auto stats = errors->getErrorStats();
    code = (!success) | stats.nbFatal | stats.nbSyntax | stats.nbError;
  }

  SURELOG::ErrorContainer::Stats stats = errors->getErrorStats();
  errors->printStats(stats, false);

  if (vpi_design == nullptr) return code;

  if (!Build(vpi_design)) return -1;

  // Do not delete these objects until you are done with UHDM
  SURELOG::shutdown_compiler(compiler);
  delete clp;
  delete symbolTable;
  delete errors;
  return 0;
}
