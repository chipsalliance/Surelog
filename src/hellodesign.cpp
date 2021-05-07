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
#include <functional>
#include <iostream>
#include "ElaboratorListener.h"
#include "headers/vpi_listener.h"
#include "surelog.h"
#include "uhdm.h"

class DesignListener final : public UHDM::VpiListener {
  virtual void enterModule(const UHDM::module *const object,
                           const UHDM::any *const parent, vpiHandle handle,
                           vpiHandle parentHandle) override {
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

  virtual void enterCont_assign(const UHDM::cont_assign *object,
                                const UHDM::BaseClass *parent, vpiHandle handle,
                                vpiHandle parentHandle) {
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

bool Build(vpiHandle design_handle) {
  DesignListener listener;
  UHDM::listen_designs({design_handle}, &listener);
  std::cout << "End design traversal" << std::endl;
  return true;
}

int main(int argc, char *argv[]) {
  if (argc < 2) return 0;

  // Read command line, compile a design, use -parse argument
  int code = 0;
  SURELOG::SymbolTable *const symbolTable = new SURELOG::SymbolTable();
  SURELOG::ErrorContainer *const errors =
      new SURELOG::ErrorContainer(symbolTable);
  SURELOG::CommandLineParser *const clp =
      new SURELOG::CommandLineParser(errors, symbolTable, false, false);
  clp->setParse(true);
  clp->setCompile(true);
  clp->setElaborate(true);  // Request Surelog instance tree elaboration
  clp->setElabUhdm(true);   // Request UHDM Uniquification/Elaboration
  bool success = clp->parseCommandLine(argc, const_cast<const char **>(argv));
  errors->printMessages(clp->muteStdout());

  vpiHandle the_design = nullptr;
  if (success && (!clp->help())) {
    SURELOG::scompiler *compiler = SURELOG::start_compiler(clp);
    the_design = SURELOG::get_uhdm_design(compiler);
    SURELOG::shutdown_compiler(compiler);
    auto stats = errors->getErrorStats();
    code = (!success) | stats.nbFatal | stats.nbSyntax | stats.nbError;
  }

  SURELOG::ErrorContainer::Stats stats = errors->getErrorStats();
  errors->printStats(stats, false);

  delete clp;
  delete symbolTable;
  delete errors;

  if (the_design == nullptr) return code;

  if (!Build(the_design)) return -1;
}
