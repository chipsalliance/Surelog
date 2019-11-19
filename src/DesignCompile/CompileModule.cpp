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
#include "CommandLine/CommandLineParser.hpp"
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
    case VObjectType::slInterface_declaration:
      if (!collectInterfaceObjects_()) return false;
      if (!checkInterface_()) return false;
      break;
    case VObjectType::slUdp_declaration:

      break;
    case VObjectType::slChecker_declaration:

      break;
    case VObjectType::slProgram_declaration:

      break;
    default:
      break;
  }

  return true;
}

VObjectType getSignalType(FileContent* fC, NodeId net_port_type) {
  VObjectType signal_type = VObjectType::slData_type_or_implicit;
  if (net_port_type) {
    NodeId data_type_or_implicit = fC->Child(net_port_type);
    if (fC->Type(data_type_or_implicit) == VObjectType::slNetType_Wire) {
      signal_type = VObjectType::slNetType_Wire;
    } else {
      NodeId data_type = fC->Child(data_type_or_implicit);
      if (data_type) {
        VObjectType the_type = fC->Type(data_type);
        if (the_type == VObjectType::slData_type) {
          NodeId integer_vector_type = fC->Child(data_type);
          the_type = fC->Type(integer_vector_type);
          if (the_type == VObjectType::slIntVec_TypeBit ||
              the_type == VObjectType::slIntVec_TypeLogic ||
              the_type == VObjectType::slIntVec_TypeReg) {
            signal_type = the_type;
          }
        }
      }
    }
  }
  return signal_type;
}

void setDirectionAndType(ModuleDefinition* module, FileContent* fC,
                         NodeId signal, VObjectType type,
                         VObjectType signal_type) {
  while (signal) {
    for (auto& port : module->getPorts()) {
      if (port.getName() == fC->SymName(signal)) {
        VObjectType dir_type = slNoType;
        if (type == VObjectType::slInput_declaration)
          dir_type = slPortDir_Inp;
        else if (type == VObjectType::slOutput_declaration)
          dir_type = slPortDir_Out;
        else if (type == VObjectType::slInout_declaration)
          dir_type = slPortDir_Inout;

        port.setDirection(dir_type);
        if (signal_type != VObjectType::slData_type_or_implicit)
          port.setType(signal_type);
        break;
      }
    }
    signal = fC->Sibling(signal);
  }
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
        case VObjectType::slPackage_import_item: {
          m_helper.importPackage(m_module, m_design, fC, id);
          break;
        }
        case VObjectType::slAnsi_port_declaration: {
          NodeId net_port_header = fC->Child(id);
          NodeId identifier = fC->Sibling(net_port_header);
          NodeId net_port_type = fC->Child(net_port_header);
          VObjectType dir_type = fC->Type(net_port_type);
          if (dir_type == VObjectType::slPortDir_Out ||
              dir_type == VObjectType::slPortDir_Inp ||
              dir_type == VObjectType::slPortDir_Inout ||
              dir_type == VObjectType::slPortDir_Ref) {
            port_direction = dir_type;
            net_port_type = fC->Sibling(net_port_type);
            VObjectType signal_type = getSignalType(fC, net_port_type);
            Signal signal(fC, identifier, signal_type, port_direction);
            m_module->m_ports.push_back(signal);
          } else {
            NodeId data_type_or_implicit = fC->Child(net_port_type);
            NodeId data_type = fC->Child(data_type_or_implicit);
            if (data_type) {
              NodeId if_type_name_s = fC->Child(data_type);
              if (fC->Type(if_type_name_s) == VObjectType::slIntVec_TypeReg ||
                  fC->Type(if_type_name_s) == VObjectType::slIntVec_TypeLogic) {
                Signal signal(fC, identifier, fC->Type(if_type_name_s),
                              VObjectType::slNoType);
                m_module->m_ports.push_back(signal);
              } else {
                std::string interfaceName =
                    libName + "@" + fC->SymName(if_type_name_s);
                Signal signal(fC, if_type_name_s, identifier);
                ModuleDefinition* interface =
                    m_design->getModuleDefinition(interfaceName);
                if (interface) {
                  signal.setInterfaceDef(interface);
                } else {
                  Location loc(m_symbols->registerSymbol(
                                   fC->getFileName(if_type_name_s)),
                               fC->Line(if_type_name_s), 0,
                               m_symbols->registerSymbol(interfaceName));
                  Error err(ErrorDefinition::COMP_UNDEFINED_INTERFACE, loc);
                  m_errors->addError(err);
                }
              }
            } else {
              Signal signal(fC, identifier,
                            VObjectType::slData_type_or_implicit,
                            port_direction);
              m_module->m_ports.push_back(signal);
            }
          }
          break;
        }
        case VObjectType::slPort:
          /*
            n<mem_if> u<3> t<StringConst> p<6> s<5> l<1>
            n<> u<4> t<Constant_bit_select> p<5> l<1>
            n<> u<5> t<Constant_select> p<6> c<4> l<1>
            n<> u<6> t<Port_reference> p<11> c<3> s<10> l<1>
            n<mif> u<7> t<StringConst> p<10> s<9> l<1>
            n<> u<8> t<Constant_bit_select> p<9> l<1>
            n<> u<9> t<Constant_select> p<10> c<8> l<1>
            n<> u<10> t<Port_reference> p<11> c<7> l<1>
            n<> u<11> t<Port_expression> p<12> c<6> l<1>
            n<> u<12> t<Port> p<13> c<11> l<1>
          */
          {
            NodeId Port_expression = fC->Child(id);
            if (Port_expression &&
                (fC->Type(Port_expression) == VObjectType::slPort_expression)) {
              NodeId if_type = fC->Child(Port_expression);
              if (fC->Type(if_type) == VObjectType::slPort_reference) {
                NodeId if_type_name_s = fC->Child(if_type);
                NodeId if_name = fC->Sibling(if_type);
                if (if_name) {
                  NodeId if_name_s = fC->Child(if_name);
                  std::string interfaceName =
                      libName + "@" + fC->SymName(if_type_name_s);
                  Signal signal(fC, if_type_name_s, if_name_s);
                  ModuleDefinition* interface =
                      m_design->getModuleDefinition(interfaceName);
                  if (interface) {
                    signal.setInterfaceDef(interface);
                  } else {
                    Location loc(m_symbols->registerSymbol(
                                     fC->getFileName(if_type_name_s)),
                                 fC->Line(if_type_name_s), 0,
                                 m_symbols->registerSymbol(interfaceName));
                    Error err(ErrorDefinition::COMP_UNDEFINED_INTERFACE, loc);
                    m_errors->addError(err);
                  }
                  m_module->m_ports.push_back(signal);
                } else {
                  Signal signal(fC, if_type_name_s,
                                VObjectType::slData_type_or_implicit,
                                port_direction);
                  m_module->m_ports.push_back(signal);
                }
              }
            }
            break;
          }
        case VObjectType::slInput_declaration:
        case VObjectType::slOutput_declaration:
        case VObjectType::slInout_declaration: {
          /*
            n<> u<24> t<Data_type_or_implicit> p<25> l<7>
            n<> u<25> t<Net_port_type> p<28> c<24> s<27> l<7>
            n<c0> u<26> t<StringConst> p<27> l<7>
            n<> u<27> t<List_of_port_identifiers> p<28> c<26> l<7>
            n<> u<28> t<Output_declaration> p<29> c<25> l<7>
          */
          NodeId net_port_type = fC->Child(id);
          VObjectType signal_type = getSignalType(fC, net_port_type);
          NodeId list_of_port_identifiers = fC->Sibling(net_port_type);
          if (fC->Type(list_of_port_identifiers) ==
              VObjectType::slPacked_dimension) {
            list_of_port_identifiers = fC->Sibling(list_of_port_identifiers);
          }
          NodeId signal = fC->Child(list_of_port_identifiers);
          setDirectionAndType(m_module, fC, signal, type, signal_type);
          break;
        }
        case VObjectType::slClocking_declaration:
          compileClockingBlock_(fC, id);
          break;
        case VObjectType::slNet_declaration: {
          /*
           n<> u<17> t<NetType_Wire> p<18> l<27>
           n<> u<18> t<NetTypeOrTrireg_Net> p<22> c<17> s<21> l<27>
           n<a> u<19> t<StringConst> p<20> l<27>
           n<> u<20> t<Net_decl_assignment> p<21> c<19> l<27>
           n<> u<21> t<List_of_net_decl_assignments> p<22> c<20> l<27>
           n<> u<22> t<Net_declaration> p<23> c<18> l<27>
          */
          NodeId netTypeOrTrireg_Net = fC->Child(id);
          NodeId netType_Wire = fC->Child(netTypeOrTrireg_Net);
          NodeId list_of_net_decl_assignments =
              fC->Sibling(netTypeOrTrireg_Net);
          if (fC->Type(list_of_net_decl_assignments) ==
              VObjectType::slPacked_dimension) {
            list_of_net_decl_assignments =
                fC->Sibling(list_of_net_decl_assignments);
          }
          NodeId net_decl_assignment = fC->Child(list_of_net_decl_assignments);
          while (net_decl_assignment) {
            NodeId signal = fC->Child(net_decl_assignment);
            for (auto& port : m_module->m_ports) {
              if (port.getName() == fC->SymName(signal)) {
                port.setType(fC->Type(netType_Wire));
                break;
              }
            }
            net_decl_assignment = fC->Sibling(net_decl_assignment);
          }
          break;
        }
        case VObjectType::slData_declaration: {
          NodeId subNode = fC->Child(id);
          VObjectType subType = fC->Type(subNode);
          switch (subType) {
            case VObjectType::slType_declaration: {
              /*
                n<> u<15> t<Data_type> p<17> c<8> s<16> l<13>
                n<fsm_t> u<16> t<StringConst> p<17> l<13>
                n<> u<17> t<Type_declaration> p<18> c<15> l<13>
                n<> u<18> t<Data_declaration> p<19> c<17> l<13>
               */
              m_helper.compileTypeDef(m_module, fC, id);
              break;
            }
            case VObjectType::slVariable_declaration: {
              /*
                n<> u<29> t<IntVec_TypeReg> p<30> l<29>
                n<> u<30> t<Data_type> p<34> c<29> s<33> l<29>
                n<b> u<31> t<StringConst> p<32> l<29>
                n<> u<32> t<Variable_decl_assignment> p<33> c<31> l<29>
                n<> u<33> t<List_of_variable_decl_assignments> p<34> c<32> l<29>
                n<> u<34> t<Variable_declaration> p<35> c<30> l<29>
                n<> u<35> t<Data_declaration> p<36> c<34> l<29>
               */
              NodeId variable_declaration = fC->Child(id);
              NodeId data_type = fC->Child(variable_declaration);
              NodeId intVec_TypeReg = fC->Child(data_type);
              NodeId list_of_variable_decl_assignments = fC->Sibling(data_type);
              if (fC->Type(list_of_variable_decl_assignments) ==
                  VObjectType::slPacked_dimension) {
                list_of_variable_decl_assignments =
                    fC->Sibling(list_of_variable_decl_assignments);
              }
              NodeId variable_decl_assignment =
                  fC->Child(list_of_variable_decl_assignments);
              while (variable_decl_assignment) {
                NodeId signal = fC->Child(variable_decl_assignment);
                for (auto& port : m_module->m_ports) {
                  if (port.getName() == fC->SymName(signal)) {
                    port.setType(fC->Type(intVec_TypeReg));
                    break;
                  }
                }
                variable_decl_assignment =
                    fC->Sibling(variable_decl_assignment);
              }
              break;
            }
            default:
              break;
          }
          break;
        }
        case VObjectType::slPort_declaration: {
          /*
           n<Configuration> u<21> t<StringConst> p<22> l<7>
           n<> u<22> t<Interface_identifier> p<26> c<21> s<25> l<7>
           n<cfg> u<23> t<StringConst> p<24> l<7>
           n<> u<24> t<Interface_identifier> p<25> c<23> l<7>
           n<> u<25> t<List_of_interface_identifiers> p<26> c<24> l<7>
           n<> u<26> t<Interface_port_declaration> p<27> c<22> l<7>
           n<> u<27> t<Port_declaration> p<28> c<26> l<7>
           */
          NodeId subNode = fC->Child(id);
          VObjectType subType = fC->Type(subNode);
          switch (subType) {
            case VObjectType::slInterface_port_declaration: {
              NodeId interface_identifier = fC->Child(subNode);
              NodeId interfIdName = fC->Child(interface_identifier);
              std::string interfName = fC->SymName(interfIdName);

              DesignComponent* def = NULL;
              DataType* type = NULL;

              std::pair<FileCNodeId, DesignComponent*>* datatype =
                  m_module->getNamedObject(interfName);
              if (!datatype) {
                def = m_module->getClassDefinition(m_module->getName() +
                                                   "::" + interfName);
              }
              if (datatype) {
                def = datatype->second;
              }
              if (def == NULL) {
                def = m_design->getComponentDefinition(libName + "@" +
                                                       interfName);
              }
              if (def == NULL) {
                type = m_module->getDataType(interfName);
              }
              if (def == NULL && type == NULL && (interfName != "logic") &&
                  (interfName != "byte") && (interfName != "bit") &&
                  (interfName != "new") && (interfName != "expect") &&
                  (interfName != "var") && (interfName != "signed") &&
                  (interfName != "unsigned") && (interfName != "do") &&
                  (interfName != "final") && (interfName != "global") &&
                  (interfName != "soft")) {
                Location loc(m_symbols->registerSymbol(fC->getFileName(id)),
                             fC->Line(id), 0,
                             m_symbols->registerSymbol(interfName));
                Error err(ErrorDefinition::COMP_UNDEFINED_TYPE, loc);
                m_errors->addError(err);
              }

              NodeId list_of_interface_identifiers =
                  fC->Sibling(interface_identifier);
              NodeId identifier = fC->Child(list_of_interface_identifiers);
              while (identifier) {
                std::string name = fC->SymName(identifier);
                identifier = fC->Sibling(identifier);
                // TODO
              }

              break;
            }
            case VObjectType::slInput_declaration:
            case VObjectType::slOutput_declaration:
            case VObjectType::slInout_declaration: {
              /*
                n<> u<24> t<Data_type_or_implicit> p<25> l<7>
                n<> u<25> t<Net_port_type> p<28> c<24> s<27> l<7>
                n<c0> u<26> t<StringConst> p<27> l<7>
                n<> u<27> t<List_of_port_identifiers> p<28> c<26> l<7>
                n<> u<28> t<Output_declaration> p<29> c<25> l<7>
               */
              NodeId net_port_type = fC->Child(subNode);
              VObjectType signal_type = getSignalType(fC, net_port_type);
              NodeId list_of_port_identifiers = fC->Sibling(net_port_type);
              if (fC->Type(list_of_port_identifiers) ==
                  VObjectType::slPacked_dimension) {
                list_of_port_identifiers =
                    fC->Sibling(list_of_port_identifiers);
              }
              NodeId signal = fC->Child(list_of_port_identifiers);
              setDirectionAndType(m_module, fC, signal, subType, signal_type);
              break;
            }
            default:
              break;
          }
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
  return true;
}

bool CompileModule::collectInterfaceObjects_() {
  for (unsigned int i = 0; i < m_module->m_fileContents.size(); i++) {
    FileContent* fC = m_module->m_fileContents[i];
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
    while (stack.size()) {
      id = stack.top();
      stack.pop();
      current = fC->Object(id);
      VObjectType type = fC->Type(id);
      switch (type) {
        case VObjectType::slPackage_import_item: {
          m_helper.importPackage(m_module, m_design, fC, id);
          break;
        }
        case VObjectType::slAnsi_port_declaration: {
          NodeId Net_port_header = fC->Child(id);
          NodeId net = fC->Sibling(Net_port_header);
          NodeId Direction = fC->Child(Net_port_header);
          VObjectType direction = fC->Type(Direction);
          NodeId Net_port_type = fC->Sibling(Direction);
          NodeId NetType = fC->Child(Net_port_type);
          VObjectType nettype = fC->Type(NetType);
          Signal signal(fC, net, nettype, direction);
          m_module->m_ports.push_back(signal);
          break;
        }
        case VObjectType::slNet_declaration: {
          NodeId NetTypeOrTrireg_Net = fC->Child(id);
          NodeId NetType = fC->Child(NetTypeOrTrireg_Net);
          VObjectType nettype = fC->Type(NetType);
          NodeId net = fC->Sibling(NetTypeOrTrireg_Net);
          NodeId List_of_net_decl_assignments;
          if (fC->Type(net) == slPacked_dimension) {
            List_of_net_decl_assignments = fC->Sibling(net);
          } else {
            List_of_net_decl_assignments = net;
          }
          NodeId Net_decl_assignment = fC->Child(List_of_net_decl_assignments);
          net = fC->Child(Net_decl_assignment);
          bool existing = false;
          for (auto& port : m_module->m_ports) {
            if (port.getName() == fC->SymName(net)) {
              existing = true;
              port.setType(nettype);
              break;
            }
          }
          if (!existing) {
            Signal signal(fC, net, nettype, VObjectType::slNoType);
            m_module->m_ports.push_back(signal);
          }
          break;
        }
        case VObjectType::slData_declaration: {
          /*
           n<> u<29> t<IntVec_TypeReg> p<30> l<29>
           n<> u<30> t<Data_type> p<34> c<29> s<33> l<29>
           n<b> u<31> t<StringConst> p<32> l<29>
           n<> u<32> t<Variable_decl_assignment> p<33> c<31> l<29>
           n<> u<33> t<List_of_variable_decl_assignments> p<34> c<32> l<29>
           n<> u<34> t<Variable_declaration> p<35> c<30> l<29>
           n<> u<35> t<Data_declaration> p<36> c<34> l<29>
          */
          NodeId variable_declaration = fC->Child(id);
          NodeId data_type = fC->Child(variable_declaration);
          NodeId intVec_TypeReg = fC->Child(data_type);
          NodeId list_of_variable_decl_assignments = fC->Sibling(data_type);
          if (fC->Type(list_of_variable_decl_assignments) ==
              VObjectType::slPacked_dimension) {
            list_of_variable_decl_assignments =
                fC->Sibling(list_of_variable_decl_assignments);
          }
          NodeId variable_decl_assignment =
              fC->Child(list_of_variable_decl_assignments);
          while (variable_decl_assignment) {
            NodeId signal = fC->Child(variable_decl_assignment);
            bool port_exist = false;
            for (auto& port : m_module->m_ports) {
              if (port.getName() == fC->SymName(signal)) {
                port_exist = true;
                port.setType(fC->Type(intVec_TypeReg));
                break;
              }
            }
            if (!port_exist) {
              Signal sig(fC, signal, fC->Type(intVec_TypeReg),
                         VObjectType::slNoType);
              m_module->m_ports.push_back(sig);
            }
            variable_decl_assignment = fC->Sibling(variable_decl_assignment);
          }
          break;
        }
        case VObjectType::slClocking_declaration:
          compileClockingBlock_(fC, id);
          break;
        case VObjectType::slGenerate_interface_item: {
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
            SymbolId modportsymb = fC->Name(modportname);
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
                  for (auto& port : m_module->m_ports) {
                    if (fC->Name(port.getNodeId()) == port_symbol) {
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
        default:
          break;
      }

      if (current.m_sibling) stack.push(current.m_sibling);
      if (current.m_child) stack.push(current.m_child);
    }
  }

  return true;
}

bool CompileModule::checkModule_() {
  int countMissingType = 0;
  int countMissingDirection = 0;
  Location* missingTypeLoc = NULL;
  Location* missingDirectionLoc = NULL;
  for (auto& port : m_module->m_ports) {
    if (port.isInterface()) continue;
    if (port.getType() == VObjectType::slData_type_or_implicit) {
      if (port.getDirection() == VObjectType::slPortDir_Out ||
          port.getDirection() == VObjectType::slPortDir_Inout) {
        if (countMissingType == 0)
          missingTypeLoc = new Location(
              m_symbols->registerSymbol(
                  port.getFileContent()->getFileName(port.getNodeId())),
              port.getFileContent()->Line(port.getNodeId()), 0,
              m_symbols->registerSymbol(port.getName()));
        countMissingType++;
      }
    }
    if (port.getDirection() == VObjectType::slNoType) {
      if (countMissingDirection == 0)
        missingDirectionLoc = new Location(
            m_symbols->registerSymbol(
                port.getFileContent()->getFileName(port.getNodeId())),
            port.getFileContent()->Line(port.getNodeId()), 0,
            m_symbols->registerSymbol(port.getName()));
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
    if (port.getType() == VObjectType::slData_type_or_implicit) {
      if (port.getDirection() == VObjectType::slPortDir_Out ||
          port.getDirection() == VObjectType::slPortDir_Inout) {
        if (countMissingType == 0)
          missingTypeLoc = new Location(
              m_symbols->registerSymbol(
                  port.getFileContent()->getFileName(port.getNodeId())),
              port.getFileContent()->Line(port.getNodeId()), 0,
              m_symbols->registerSymbol(port.getName()));
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
