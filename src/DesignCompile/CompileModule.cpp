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
 * File:   CompileModule.cpp
 * Author: alain
 *
 * Created on March 22, 2018, 9:43 PM
 */

#include "SourceCompile/VObjectTypes.h"
#include "Design/VObject.h"
#include "Library/Library.h"
#include "Design/Signal.h"
#include "Design/FileContent.h"
#include "Design/ClockingBlock.h"
#include "SourceCompile/SymbolTable.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/Location.h"
#include "ErrorReporting/Error.h"
#include "CommandLine/CommandLineParser.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/ParseFile.h"
#include "SourceCompile/Compiler.h"
#include "Testbench/ClassDefinition.h"
#include "DesignCompile/CompileHelper.h"
#include "DesignCompile/CompileDesign.h"
#include "DesignCompile/CompileModule.h"

using namespace SURELOG;

CompileModule::~CompileModule() {}

int FunctorCompileModule::operator()() const {
  CompileModule* instance = new CompileModule(m_compileDesign, m_module,
                                              m_design, m_symbols, m_errors);
  instance->compile();
  delete instance;
  return true;
}

bool CompileModule::compile() {
  FileContent* fC = m_module->m_fileContents[0];
  NodeId nodeId = m_module->m_nodeIds[0];
  Location loc(m_symbols->registerSymbol(fC->getFileName(nodeId)),
               fC->Line(nodeId), 0,
               m_symbols->registerSymbol(m_module->getName()));
  VObjectType moduleType = fC->Type(nodeId);
  ErrorDefinition::ErrorType errType = ErrorDefinition::COMP_COMPILE_MODULE;
  switch (moduleType) {
    case VObjectType::slInterface_declaration:
      errType = ErrorDefinition::COMP_COMPILE_INTERFACE;
      break;
    case VObjectType::slUdp_declaration:
      errType = ErrorDefinition::COMP_COMPILE_UDP;
      break;
    case VObjectType::slChecker_declaration:
      errType = ErrorDefinition::COMP_COMPILE_CHECKER;
      break;
    default:
      break;
  }

  Error err(errType, loc);
  ErrorContainer* errors = new ErrorContainer(m_symbols);
  errors->regiterCmdLine(
      m_compileDesign->getCompiler()->getCommandLineParser());
  errors->addError(err);
  errors->printMessage(
      err,
      m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());
  delete errors;

  switch (moduleType) {
    case VObjectType::slModule_declaration:
      if (!collectModuleObjects_()) return false;
      if (!checkModule_()) return false;
      break;
    case VObjectType::slConditional_generate_construct:
      if (!collectModuleObjects_()) return false;
      if (!checkModule_()) return false;
      break;
    case VObjectType::slInterface_declaration:
      if (!collectInterfaceObjects_()) return false;
      if (!checkInterface_()) return false;
      break;
    case VObjectType::slUdp_declaration:
      break;
    case VObjectType::slChecker_declaration:
      break;
    default:
      break;
  }

  return true;
}


bool CompileModule::collectModuleObjects_() {
  std::vector<VObjectType> stopPoints = {
      VObjectType::slConditional_generate_construct,
      VObjectType::slGenerate_module_conditional_statement,
      VObjectType::slLoop_generate_construct,
      VObjectType::slGenerate_module_loop_statement,
      VObjectType::slPar_block,
      VObjectType::slSeq_block,
      VObjectType::slModule_declaration,
      VObjectType::slClass_declaration};

  for (unsigned int i = 0; i < m_module->m_fileContents.size(); i++) {
    FileContent* fC = m_module->m_fileContents[i];
    std::string libName = fC->getLibrary()->getName();
    VObject current = fC->Object(m_module->m_nodeIds[i]);
    NodeId id = current.m_child;
    
    NodeId endOfBlockId = 0;
    if (m_module->getGenBlockId()) {
      id = m_module->getGenBlockId();
      endOfBlockId = fC->Sibling(id);
    }
    if (!id) id = current.m_sibling;
    if (!id) return false;

    // Package imports
    std::vector<FileCNodeId> pack_imports;
    // - Local file imports
    for (auto import : fC->getObjects(VObjectType::slPackage_import_item)) {
      pack_imports.push_back(import);
    }

    for (auto pack_import : pack_imports) {
      FileContent* pack_fC = pack_import.fC;
      NodeId pack_id = pack_import.nodeId;
      m_helper.importPackage(m_module, m_design, pack_fC, pack_id);
    }

    std::stack<NodeId> stack;
    stack.push(id);
    VObjectType port_direction = VObjectType::slNoType;
    while (stack.size()) {
      id = stack.top();
      if (endOfBlockId && (id == endOfBlockId)) {
        break;
      }
      stack.pop();
      current = fC->Object(id);
      VObjectType type = fC->Type(id);
      switch (type) {
        case VObjectType::slPackage_import_item: {
          m_helper.importPackage(m_module, m_design, fC, id);
          break;
        }
        case VObjectType::slAnsi_port_declaration: {
          m_helper.compileAnsiPortDeclaration(m_module, fC, id, port_direction);
          break;
        }
        case VObjectType::slPort: {
          m_helper.compilePortDeclaration(m_module, fC, id, port_direction);
          break;  
        }
        case VObjectType::slInput_declaration:
        case VObjectType::slOutput_declaration:
        case VObjectType::slInout_declaration: {
          m_helper.compilePortDeclaration(m_module, fC, id, port_direction);
          break;
        }
        case VObjectType::slClocking_declaration:
          compileClockingBlock_(fC, id);
          break;
        case VObjectType::slNet_declaration: {
          m_helper.compileNetDeclaration(m_module, fC, id, false);
          break;
        }
        case VObjectType::slData_declaration: {
          m_helper.compileDataDeclaration(m_module, m_module, fC,id, false, m_compileDesign);
          break;
        }
        case VObjectType::slPort_declaration: {
          m_helper.compilePortDeclaration(m_module, fC, id, port_direction);
          break;
        }
        case VObjectType::slContinuous_assign:
        {
          m_helper.compileContinuousAssignment(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slAlways_construct:
        {
          m_helper.compileAlwaysBlock(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slParameter_declaration: {
          m_helper.compileParameterDeclaration(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slLocal_parameter_declaration: {
          m_helper.compileParameterDeclaration(m_module, fC, id, m_compileDesign, true);
          break;
        }
        case VObjectType::slTask_declaration: {
          m_helper.compileTask(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slFunction_declaration: {
          m_helper.compileFunction(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slParam_assignment: 
        case VObjectType::slHierarchical_instance:
        case VObjectType::slN_input_gate_instance:
        case VObjectType::slN_output_gate_instance:
        case VObjectType::slUdp_instance:
        case VObjectType::slUdp_instantiation:
        case VObjectType::slModule_instantiation:
        case VObjectType::slInterface_instantiation:
        case VObjectType::slGate_instantiation:
        case VObjectType::slConditional_generate_construct:
        case VObjectType::slGenerate_module_conditional_statement:
        case VObjectType::slLoop_generate_construct:
        case VObjectType::slGenerate_module_loop_statement:
        case VObjectType::slPar_block:
        case VObjectType::slSeq_block:
        case VObjectType::slDefparam_assignment: {
          FileCNodeId fnid(fC, id);
          m_module->addObject(type, fnid);
          break;
        }
        case VObjectType::slInitial_construct:
          m_helper.compileInitialBlock(m_module, fC, id, m_compileDesign);
          break;
        default:
          break;
      }

      if (current.m_sibling) stack.push(current.m_sibling);
      if (current.m_child) {
        if (stopPoints.size()) {
          bool stop = false;
          for (auto t : stopPoints) {
            if (t == current.m_type) {
              stop = true;
              break;
            }
          }
          if (!stop)
            if (current.m_child) stack.push(current.m_child);
        } else {
          if (current.m_child) stack.push(current.m_child);
        }
      }
    }
  }

  for (Signal* port : m_module->getPorts()) {
    bool found = false;
    for (Signal* sig : m_module->getSignals()) {
      if (sig->getName() == port->getName()) {
        found = true;
        break;
      }
    }
    if (found == false) {
      m_module->getSignals().push_back(port);
    }
  }

  return true;
}

bool CompileModule::collectInterfaceObjects_() {
  for (unsigned int i = 0; i < m_module->m_fileContents.size(); i++) {
    FileContent* fC = m_module->m_fileContents[i];
    std::string libName = fC->getLibrary()->getName();
    VObject current = fC->Object(m_module->m_nodeIds[i]);
    NodeId id = current.m_child;
    if (!id) id = current.m_sibling;
    if (!id) return false;

    // Package imports
    std::vector<FileCNodeId> pack_imports;
    // - Local file imports
    for (auto import : fC->getObjects(VObjectType::slPackage_import_item)) {
      pack_imports.push_back(import);
    }

    for (auto pack_import : pack_imports) {
      FileContent* pack_fC = pack_import.fC;
      NodeId pack_id = pack_import.nodeId;
      m_helper.importPackage(m_module, m_design, pack_fC, pack_id);
    }

    std::stack<NodeId> stack;
    stack.push(id);
    VObjectType port_direction = VObjectType::slNoType;
    while (stack.size()) {
      id = stack.top();
      stack.pop();
      current = fC->Object(id);
      VObjectType type = fC->Type(id);
      switch (type) {
      case VObjectType::slPackage_import_item:
      {
        m_helper.importPackage(m_module, m_design, fC, id);
        break;
      }
      case VObjectType::slAnsi_port_declaration:
      {
        m_helper.compileAnsiPortDeclaration(m_module, fC, id, port_direction);
        break;
      }
      case VObjectType::slNet_declaration:
      {
        m_helper.compileNetDeclaration(m_module, fC, id, true);
        break;
      }
      case VObjectType::slData_declaration:
      {
        m_helper.compileDataDeclaration(m_module, m_module, fC,id, true, m_compileDesign);
        break;
      }
      case VObjectType::slContinuous_assign:
      {
        m_helper.compileContinuousAssignment(m_module, fC, id, m_compileDesign);
        break;
      }
      case VObjectType::slTask_declaration: {
        m_helper.compileTask(m_module, fC, id, m_compileDesign);
        break;
      }
      case VObjectType::slFunction_declaration: {
        m_helper.compileFunction(m_module, fC, id, m_compileDesign);
        break;
      }
      case VObjectType::slClocking_declaration:
        compileClockingBlock_(fC, id);
        break;
      case VObjectType::slGenerate_interface_item:
      {
        // TODO: rewrite this rough implementation
        std::vector<VObjectType> types = {VObjectType::slModport_item};
        std::vector<NodeId> items = fC->sl_collect_all(id, types);
        for (auto nodeId : items) {
          Location loc(m_symbols->registerSymbol(fC->getFileName(nodeId)),
                  fC->Line(nodeId), 0, 0);
          Error err(ErrorDefinition::COMP_NO_MODPORT_IN_GENERATE, loc);
          m_errors->addError(err);
        }
        break;
      }
      case VObjectType::slModport_item:
        /*
         n<tb> u<45> t<StringConst> p<56> s<50> l<43>
         n<> u<46> t<PortDir_Inp> p<49> s<48> l<43>
         n<clk> u<47> t<StringConst> p<48> l<43>
         n<> u<48> t<Modport_simple_port> p<49> c<47> l<43>
         n<> u<49> t<Modport_simple_ports_declaration> p<50> c<46> l<43>
         n<> u<50> t<Modport_ports_declaration> p<56> c<49> s<55> l<43>
         n<> u<51> t<PortDir_Out> p<54> s<53> l<43>
         n<reset> u<52> t<StringConst> p<53> l<43>
         n<> u<53> t<Modport_simple_port> p<54> c<52> l<43>
         n<> u<54> t<Modport_simple_ports_declaration> p<55> c<51> l<43>
         n<> u<55> t<Modport_ports_declaration> p<56> c<54> l<43>
         n<> u<56> t<Modport_item> p<57> c<45> l<43>
         */
      {
        NodeId modportname = fC->Child(id);
        const std::string& modportsymb = fC->SymName(modportname);
        NodeId modport_ports_declaration = fC->Sibling(modportname);
        VObjectType port_direction_type = VObjectType::slNoType;
        while (modport_ports_declaration) {
          NodeId port_declaration = fC->Child(modport_ports_declaration);
          VObjectType port_declaration_type = fC->Type(port_declaration);
          if (port_declaration_type ==
                  VObjectType::slModport_simple_ports_declaration) {
            NodeId port_direction = fC->Child(port_declaration);
            port_direction_type = fC->Type(port_direction);
            NodeId modport_simple_port = fC->Sibling(port_direction);
            while (modport_simple_port) {
              NodeId simple_port_name = fC->Child(modport_simple_port);
              SymbolId port_symbol = fC->Name(simple_port_name);
              bool port_exists = false;
              for (auto& port : m_module->m_signals) {
                if (fC->Name(port->getNodeId()) == port_symbol) {
                  port_exists = true;
                  break;
                }
              }
              if (!port_exists) {
                Location loc(m_symbols->registerSymbol(
                        fC->getFileName(simple_port_name)),
                        fC->Line(simple_port_name), 0,
                        m_symbols->registerSymbol(
                        fC->SymName(simple_port_name)));
                Error err(ErrorDefinition::COMP_MODPORT_UNDEFINED_PORT,
                        loc);
                m_errors->addError(err);
              }
              Signal signal(fC, simple_port_name,
                      VObjectType::slData_type_or_implicit,
                      port_direction_type);
              m_module->insertModPort(modportsymb, signal);
              modport_simple_port = fC->Sibling(modport_simple_port);
            }
          } else if (port_declaration_type ==
                  VObjectType::
                  slModport_hierarchical_ports_declaration) {
          } else if (port_declaration_type ==
                  VObjectType::slModport_tf_ports_declaration) {
          } else {
            // CLOCKING
            NodeId clocking_block_name = port_declaration;
            SymbolId clocking_block_symbol =
                    m_symbols->registerSymbol(fC->SymName(clocking_block_name));
            ClockingBlock* cb =
                    m_module->getClockingBlock(clocking_block_symbol);
            if (cb == NULL) {
              Location loc(m_symbols->registerSymbol(
                      fC->getFileName(clocking_block_name)),
                      fC->Line(clocking_block_name), 0,
                      clocking_block_symbol);
              Error err(
                      ErrorDefinition::COMP_MODPORT_UNDEFINED_CLOCKING_BLOCK,
                      loc);
              m_errors->addError(err);
            } else {
              m_module->insertModPort(modportsymb, *cb);
            }
          }
          modport_ports_declaration =
                  fC->Sibling(modport_ports_declaration);
        }
      }
      case VObjectType::slInitial_construct:
        m_helper.compileInitialBlock(m_module, fC, id, m_compileDesign);
        break;
      case VObjectType::slParameter_declaration: {
        m_helper.compileParameterDeclaration(m_module, fC, id, m_compileDesign);
        break;
      }
      case VObjectType::slLocal_parameter_declaration: {
        m_helper.compileParameterDeclaration(m_module, fC, id, m_compileDesign, true);
        break;
      }
      case VObjectType::slParam_assignment:
      case VObjectType::slDefparam_assignment: {
        FileCNodeId fnid(fC, id);
       m_module->addObject(type, fnid);
        break;
      }  
      default:
        break;
      }

      if (current.m_sibling) stack.push(current.m_sibling);
      if (current.m_child) stack.push(current.m_child);
    }
  }

  for (Signal* port : m_module->getPorts()) {
    bool found = false;
    for (Signal* sig : m_module->getSignals()) {
      if (sig->getName() == port->getName()) {
        found = true;
        break;
      }
    }
    if (found == false) {
      m_module->getSignals().push_back(port);
    }
  }
  return true;
}

bool CompileModule::checkModule_() {
  int countMissingType = 0;
  int countMissingDirection = 0;
  Location* missingTypeLoc = NULL;
  Location* missingDirectionLoc = NULL;
  for (Signal* port : m_module->m_ports) {
    if (port->isInterface()) continue;
    if (port->getType() == VObjectType::slData_type_or_implicit) {
      if (port->getDirection() == VObjectType::slPortDir_Out ||
          port->getDirection() == VObjectType::slPortDir_Inout) {
        if (countMissingType == 0)
          missingTypeLoc = new Location(
              m_symbols->registerSymbol(
                  port->getFileContent()->getFileName(port->getNodeId())),
              port->getFileContent()->Line(port->getNodeId()), 0,
              m_symbols->registerSymbol(port->getName()));
        countMissingType++;
      }
    }
    if (port->getDirection() == VObjectType::slNoType) {
      if (countMissingDirection == 0)
        missingDirectionLoc = new Location(
            m_symbols->registerSymbol(
                port->getFileContent()->getFileName(port->getNodeId())),
            port->getFileContent()->Line(port->getNodeId()), 0,
            m_symbols->registerSymbol(port->getName()));
      countMissingDirection++;
    }
  }
  if (countMissingType) {
    Location countLoc(
        0, 0, 0,
        m_symbols->registerSymbol(std::to_string(countMissingType - 1)));
    if (countMissingType - 1 > 0) {
      Error err(ErrorDefinition::COMP_PORT_MISSING_TYPE, *missingTypeLoc,
                countLoc);
      m_errors->addError(err);
    } else {
      Error err(ErrorDefinition::COMP_PORT_MISSING_TYPE, *missingTypeLoc);
      m_errors->addError(err);
    }
    delete missingTypeLoc;
  }
  if (countMissingDirection) {
    Location countLoc(
        0, 0, 0,
        m_symbols->registerSymbol(std::to_string(countMissingDirection - 1)));
    if (countMissingDirection - 1 > 0) {
      Error err(ErrorDefinition::COMP_PORT_MISSING_DIRECTION,
                *missingDirectionLoc, countLoc);
      m_errors->addError(err);
    } else {
      Error err(ErrorDefinition::COMP_PORT_MISSING_DIRECTION,
                *missingDirectionLoc);
      m_errors->addError(err);
    }
    delete missingDirectionLoc;
  }

  return true;
}

bool CompileModule::checkInterface_() {
  int countMissingType = 0;
  Location* missingTypeLoc = NULL;
  for (auto& port : m_module->m_ports) {
    if (port->getType() == VObjectType::slData_type_or_implicit) {
      if (port->getDirection() == VObjectType::slPortDir_Out ||
          port->getDirection() == VObjectType::slPortDir_Inout) {
        if (countMissingType == 0)
          missingTypeLoc = new Location(
              m_symbols->registerSymbol(
                  port->getFileContent()->getFileName(port->getNodeId())),
              port->getFileContent()->Line(port->getNodeId()), 0,
              m_symbols->registerSymbol(port->getName()));
        countMissingType++;
      }
    }
  }
  if (countMissingType) {
    Location countLoc(
        0, 0, 0,
        m_symbols->registerSymbol(std::to_string(countMissingType - 1)));
    if (countMissingType - 1 > 0) {
      Error err(ErrorDefinition::COMP_PORT_MISSING_TYPE, *missingTypeLoc,
                countLoc);
      m_errors->addError(err);
    } else {
      Error err(ErrorDefinition::COMP_PORT_MISSING_TYPE, *missingTypeLoc);
      m_errors->addError(err);
    }
    delete missingTypeLoc;
  }
  return true;
}

void CompileModule::compileClockingBlock_(FileContent* fC, NodeId id) {
  /*
    n<cb> u<12> t<StringConst> p<21> s<20> l<39>
    n<> u<13> t<Edge_Posedge> p<19> s<18> l<39>
    n<clk> u<14> t<StringConst> p<17> s<16> l<39>
    n<> u<15> t<Bit_select> p<16> l<39>
    n<> u<16> t<Select> p<17> c<15> l<39>
    n<> u<17> t<Primary> p<18> c<14> l<39>
    n<> u<18> t<Expression> p<19> c<17> l<39>
    n<> u<19> t<Event_expression> p<20> c<13> l<39>
    n<> u<20> t<Clocking_event> p<21> c<19> l<39>
    n<> u<21> t<Clocking_declaration> p<22> c<12> l<39>
   */

  NodeId clocking_block_name = fC->Child(id);
  SymbolId clocking_block_symbol =
      m_symbols->registerSymbol(fC->SymName(clocking_block_name));
  NodeId clocking_event = fC->Sibling(clocking_block_name);
  ClockingBlock cb(fC, clocking_block_name, clocking_event);
  m_module->addClockingBlock(clocking_block_symbol, cb);
}

