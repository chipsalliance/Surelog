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

#include <cstdint>
#include <functional>
#include <iostream>
#include <string_view>

#include "Surelog/API/Surelog.h"
#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/Session.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/SourceCompile/SymbolTable.h"

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/VpiListener.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_user.h>

#include <functional>
#include <iostream>

namespace fs = std::filesystem;

class DesignListener final : public uhdm::VpiListener {
  void enterModule(const uhdm::Module *object, vpiHandle handle) final {
    std::string_view instName = object->getName();
    m_flatTraversal = (instName.empty()) &&
                      ((object->getParent() == 0) ||
                       ((object->getParent() != 0) &&
                        (object->getParent()->getVpiType() != vpiModule)));
    if (m_flatTraversal)
      std::cout << "Entering Module Definition: " << object->getDefName() << " "
                << intptr_t(object) << " " << object->getUhdmId() << std::endl;
    else
      std::cout << "Entering Module Instance: " << object->getFullName() << " "
                << intptr_t(object) << " " << object->getUhdmId() << std::endl;
  }

  void enterContAssign(const uhdm::ContAssign *object, vpiHandle handle) final {
    if (m_flatTraversal) {
      std::cout << "  Let's skip the cont assigns in the flat traversal and "
                   "only navigate the ones in the hierarchical tree!"
                << std::endl;
    } else {
      std::cout << "  enterCont_assign " << intptr_t(object) << " "
                << object->getUhdmId() << std::endl;
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
  int32_t code = 0;
  SURELOG::Session session;
  SURELOG::ErrorContainer *const errors = session.getErrorContainer();
  SURELOG::CommandLineParser *const clp = session.getCommandLineParser();

  clp->noPython();
  clp->setwritePpOutput(true);
  clp->setParse(true);
  clp->setCompile(true);
  clp->setElaborate(true);  // Request Surelog instance tree elaboration
  clp->setElabUhdm(true);   // Request UHDM Uniquification/Elaboration
  bool success = session.parseCommandLine(argc, argv, false, false);
  errors->printMessages(clp->muteStdout());

  vpiHandle vpi_design = nullptr;
  SURELOG::scompiler *compiler = nullptr;
  if (success && (!clp->help())) {
    compiler = SURELOG::start_compiler(&session);
    vpi_design = SURELOG::get_vpi_design(compiler);
    auto stats = errors->getErrorStats();
    code = (!success) | stats.nbFatal | stats.nbSyntax | stats.nbError;
  }

  SURELOG::ErrorContainer::Stats stats = errors->getErrorStats();
  errors->printStats(stats, false);

  if (vpi_design == nullptr) return code;

  if (!Build(vpi_design)) return -1;

  // Do not delete these objects until you are done with UHDM
  SURELOG::shutdown_compiler(compiler);
  return 0;
}
