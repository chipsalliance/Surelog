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

#include <Surelog/CommandLine/CommandLineParser.h>
#include <Surelog/Common/FileSystem.h>
#include <Surelog/Design/FileContent.h>
#include <Surelog/Design/ModuleDefinition.h>
#include <Surelog/Design/ModuleInstance.h>
#include <Surelog/DesignCompile/CompileDesign.h>
#include <Surelog/DesignCompile/CompileModule.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/Library/Library.h>
#include <Surelog/SourceCompile/Compiler.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/StringUtils.h>

// UHDM
#include <uhdm/assign_stmt.h>
#include <uhdm/constant.h>
#include <uhdm/initial.h>
#include <uhdm/io_decl.h>
#include <uhdm/logic_net.h>
#include <uhdm/ref_obj.h>
#include <uhdm/table_entry.h>
#include <uhdm/udp_defn.h>

#include <stack>

namespace SURELOG {

int32_t FunctorCompileModule::operator()() const {
  if (CompileModule* instance =
          new CompileModule(m_compileDesign, m_module->getUnelabMmodule(),
                            m_design, m_symbols, m_errors, nullptr)) {
    instance->compile(false, Reduce::No);
    delete instance;
  }

  if (CompileModule* instance = new CompileModule(
          m_compileDesign, m_module, m_design, m_symbols, m_errors, nullptr)) {
    instance->compile(true, Reduce::Yes);
    delete instance;
  }

  return 0;
}

int32_t FunctorGenerateModule::operator()() const {
  if (CompileModule* instance =
          new CompileModule(m_compileDesign, m_module->getUnelabMmodule(),
                            m_design, m_symbols, m_errors, nullptr)) {
    instance->compile(false, Reduce::No);
    delete instance;
  }

  if (CompileModule* instance =
          new CompileModule(m_compileDesign, m_module, m_design, m_symbols,
                            m_errors, m_instance)) {
    instance->compile(true, Reduce::Yes);
    delete instance;
  }

  return 0;
}

bool CompileModule::compile(bool elabMode, Reduce reduce) {
  const FileContent* const fC = m_module->m_fileContents[0];
  NodeId nodeId = m_module->m_nodeIds[0];
  Location loc(fC->getFileId(nodeId), fC->Line(nodeId), fC->Column(nodeId),
               m_symbols->registerSymbol(m_module->getName()));
  VObjectType moduleType = fC->Type(nodeId);
  ErrorDefinition::ErrorType errType = ErrorDefinition::COMP_COMPILE_MODULE;
  switch (moduleType) {
    case VObjectType::slLoop_generate_construct:
    case VObjectType::slConditional_generate_construct:
    case VObjectType::slGenerate_block:
    case VObjectType::slGenerate_item:
    case VObjectType::slGenerate_module_conditional_statement:
    case VObjectType::slGenerate_module_loop_statement:
    case VObjectType::slGenerate_module_block:
    case VObjectType::slGenerate_module_item:
    case VObjectType::slGenerate_module_named_block:
    case VObjectType::slGenerate_interface_conditional_statement:
    case VObjectType::slGenerate_interface_loop_statement:
    case VObjectType::slGenerate_interface_block:
    case VObjectType::slGenerate_interface_item:
    case VObjectType::slGenerate_interface_named_block:
    case VObjectType::slGenerate_region:
      errType = ErrorDefinition::COMP_COMPILE_GENERATE_BLOCK;
      break;
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

  m_module->setDesignElement(fC->getDesignElement(m_module->getName()));
  m_helper.setElabMode(elabMode);
  m_helper.setReduce(reduce);

  CommandLineParser* clp =
      m_compileDesign->getCompiler()->getCommandLineParser();
  auto& blackboxModules = clp->getBlackBoxModules();
  bool skipModule = false;
  std::string libName;
  if (!m_module->getFileContents().empty())
    libName = m_module->getFileContents()[0]->getLibrary()->getName();
  const std::string_view modName = m_module->getName();
  if (blackboxModules.find(modName) != blackboxModules.end()) {
    errType = ErrorDefinition::COMP_SKIPPING_BLACKBOX_MODULE;
    skipModule = true;
  }
  auto& blackboxInstances = clp->getBlackBoxInstances();
  std::string instanceName;
  if (m_instance) {
    if (ModuleInstance* inst =
            valuedcomponenti_cast<ModuleInstance*>(m_instance)) {
      instanceName = inst->getFullPathName();
    }
  }
  if (blackboxInstances.find(instanceName) != blackboxInstances.end()) {
    errType = ErrorDefinition::COMP_SKIPPING_BLACKBOX_INSTANCE;
    skipModule = true;
  }
  if (blackboxInstances.find(modName) != blackboxInstances.end()) {
    errType = ErrorDefinition::COMP_SKIPPING_BLACKBOX_INSTANCE;
    skipModule = true;
  }

  Error err(errType, loc);
  m_errors->addError(err);

  if (skipModule) {
    return true;
  }

  switch (moduleType) {
    case VObjectType::slModule_declaration:
      if (!collectModuleObjects_(CollectType::FUNCTION)) return false;
      if (!collectModuleObjects_(CollectType::DEFINITION)) return false;
      if (!collectModuleObjects_(CollectType::OTHER)) return false;
      if (!checkModule_()) return false;
      break;
    case VObjectType::slLoop_generate_construct:
    case VObjectType::slConditional_generate_construct:
    case VObjectType::slGenerate_item:
    case VObjectType::slGenerate_block:
    case VObjectType::slGenerate_module_conditional_statement:
    case VObjectType::slGenerate_module_loop_statement:
    case VObjectType::slGenerate_module_block:
    case VObjectType::slGenerate_module_item:
    case VObjectType::slGenerate_module_named_block:
    case VObjectType::slGenerate_region:
      if (!collectModuleObjects_(CollectType::FUNCTION)) return false;
      if (!collectModuleObjects_(CollectType::DEFINITION)) return false;
      if (!collectModuleObjects_(CollectType::OTHER)) return false;
      if (!checkModule_()) return false;
      break;
    case VObjectType::slInterface_declaration:
      if (!collectInterfaceObjects_(CollectType::FUNCTION)) return false;
      if (!collectInterfaceObjects_(CollectType::DEFINITION)) return false;
      if (!collectInterfaceObjects_(CollectType::OTHER)) return false;
      if (!checkInterface_()) return false;
      break;
    case VObjectType::slGenerate_interface_conditional_statement:
    case VObjectType::slGenerate_interface_loop_statement:
    case VObjectType::slGenerate_interface_block:
    case VObjectType::slGenerate_interface_item:
    case VObjectType::slGenerate_interface_named_block:
      if (!collectInterfaceObjects_(CollectType::FUNCTION)) return false;
      if (!collectInterfaceObjects_(CollectType::DEFINITION)) return false;
      if (!collectInterfaceObjects_(CollectType::OTHER)) return false;
      if (!checkInterface_()) return false;
      break;
    case VObjectType::slUdp_declaration:
      if (!collectUdpObjects_()) return false;
      break;
    case VObjectType::slChecker_declaration:
      break;
    default:
      break;
  }

  switch (moduleType) {
    case VObjectType::slModule_declaration:
    case VObjectType::slInterface_declaration:
    case VObjectType::slUdp_declaration:
      do {
        VObject current = fC->Object(nodeId);
        nodeId = current.m_child;
      } while (nodeId &&
               (fC->Type(nodeId) != VObjectType::slAttribute_instance));
      if (nodeId) {
        UHDM::VectorOfattribute* attributes =
            m_helper.compileAttributes(m_module, fC, nodeId, m_compileDesign);
        m_module->Attributes(attributes);
      }

      break;
    default:
      break;
  }

  return true;
}

bool CompileModule::collectUdpObjects_() {
  UHDM::Serializer& s = m_compileDesign->getSerializer();
  const FileContent* const fC = m_module->m_fileContents[0];
  NodeId id = m_module->m_nodeIds[0];
  VObject current = fC->Object(id);
  std::stack<NodeId> stack;
  stack.push(id);
  m_module->m_udpDefn = s.MakeUdp_defn();
  UHDM::udp_defn* defn = m_module->m_udpDefn;
  while (!stack.empty()) {
    id = stack.top();
    stack.pop();
    current = fC->Object(id);
    VObjectType type = fC->Type(id);
    switch (type) {
      case VObjectType::slUdp_declaration:
      case VObjectType::slUdp_nonansi_declaration:
      case VObjectType::slUdp_ansi_declaration: {
        UHDM::VectorOfattribute* attributes = nullptr;
        NodeId Attributes = fC->Child(id);
        if (fC->Type(Attributes) == VObjectType::slAttribute_instance) {
          attributes = m_helper.compileAttributes(m_module, fC, Attributes,
                                                  m_compileDesign);
          defn->Attributes(attributes);
        }
        break;
      }
      case VObjectType::slUdp_port_list: {
        std::vector<UHDM::io_decl*>* ios = defn->Io_decls();
        if (ios == nullptr) {
          defn->Io_decls(s.MakeIo_declVec());
          ios = defn->Io_decls();
        }
        NodeId port = fC->Child(id);
        while (port) {
          UHDM::io_decl* io = s.MakeIo_decl();
          const std::string_view name = fC->SymName(port);
          fC->populateCoreMembers(port, port, io);
          io->VpiName(name);
          io->VpiParent(defn);
          ios->push_back(io);
          port = fC->Sibling(port);
        }
        break;
      }
      case VObjectType::slUdp_output_declaration:
      case VObjectType::slUdp_reg_declaration: {
        NodeId Output = fC->Child(id);
        UHDM::VectorOfattribute* attributes = nullptr;
        if (fC->Type(Output) == VObjectType::slAttribute_instance) {
          attributes =
              m_helper.compileAttributes(m_module, fC, Output, m_compileDesign);
          while (fC->Type(Output) == VObjectType::slAttribute_instance)
            Output = fC->Sibling(Output);
        }

        const std::string_view outputname = fC->SymName(Output);
        std::vector<UHDM::io_decl*>* ios = defn->Io_decls();
        UHDM::logic_net* net = s.MakeLogic_net();
        fC->populateCoreMembers(id, id, net);
        net->Attributes(attributes);
        net->VpiParent(defn);
        if (ios) {
          for (auto io : *ios) {
            if (io->VpiName() == outputname) {
              if (io->Expr() == nullptr)
                io->Expr(net);  // reg def do not override output def
              net->VpiName(io->VpiName());
              io->VpiDirection(vpiOutput);
              break;
            }
          }
        }
        break;
      }
      case VObjectType::slUdp_input_declaration: {
        NodeId Indentifier_list = fC->Child(id);
        UHDM::VectorOfattribute* attributes = nullptr;
        if (fC->Type(Indentifier_list) == VObjectType::slAttribute_instance) {
          attributes = m_helper.compileAttributes(
              m_module, fC, Indentifier_list, m_compileDesign);
          while (fC->Type(Indentifier_list) ==
                 VObjectType::slAttribute_instance)
            Indentifier_list = fC->Sibling(Indentifier_list);
        }
        NodeId Identifier = fC->Child(Indentifier_list);
        while (Identifier) {
          const std::string_view inputname = fC->SymName(Identifier);
          std::vector<UHDM::io_decl*>* ios = defn->Io_decls();
          if (ios) {
            UHDM::logic_net* net = s.MakeLogic_net();
            fC->populateCoreMembers(id, id, net);
            net->Attributes(attributes);
            net->VpiParent(defn);
            for (auto io : *ios) {
              if (io->VpiName() == inputname) {
                io->Expr(net);
                net->VpiName(io->VpiName());
                io->VpiDirection(vpiInput);
                break;
              }
            }
          }
          Identifier = fC->Sibling(Identifier);
        }
        break;
      }
      case VObjectType::slCombinational_entry: {
        NodeId Level_input_list = fC->Child(id);
        NodeId Output_symbol = fC->Sibling(Level_input_list);
        NodeId Level_symbol = fC->Child(Level_input_list);
        std::string ventry = "STRING:";
        uint32_t nb = 0;
        while (Level_symbol) {
          NodeId Symbol = fC->Child(Level_symbol);
          uint32_t nbSymb = 0;
          if (fC->Type(Symbol) == VObjectType::slQmark) {
            ventry += "? ";
            nbSymb = 1;
          } else if (fC->Type(Symbol) == VObjectType::slBinOp_Mult) {
            ventry += "* ";
            nbSymb = 1;
          } else {
            const std::string_view symb = fC->SymName(Symbol);
            nbSymb = symb.size();
            std::string symbols;
            for (uint32_t i = 0; i < nbSymb; i++) {
              char s = symb[i];
              symbols += s + std::string(" ");
            }
            ventry += symbols;
          }
          Level_symbol = fC->Sibling(Level_symbol);
          nb = nb + nbSymb;
        }
        ventry += ": ";
        NodeId Symbol = fC->Child(Output_symbol);
        ventry += fC->SymName(Symbol);
        UHDM::VectorOftable_entry* entries = defn->Table_entrys();
        if (entries == nullptr) {
          defn->Table_entrys(s.MakeTable_entryVec());
          entries = defn->Table_entrys();
        }
        UHDM::table_entry* entry = s.MakeTable_entry();
        entry->VpiParent(defn);
        entry->VpiValue(ventry);
        entry->VpiSize(nb);
        fC->populateCoreMembers(Level_input_list, Level_input_list, entry);
        entries->push_back(entry);
        break;
      }
      case VObjectType::slSequential_entry: {
        NodeId Seq_input_list = fC->Child(id);
        NodeId Level_input_list = fC->Child(Seq_input_list);
        NodeId Current_state = fC->Sibling(Seq_input_list);
        NodeId Next_state = fC->Sibling(Current_state);
        std::string ventry = "STRING:";
        uint32_t nb = 0;
        NodeId Level_symbol = fC->Child(Level_input_list);
        while (Level_symbol) {
          if (fC->Type(Level_symbol) == VObjectType::slEdge_indicator) {
            NodeId Level_Symbol = fC->Child(Level_symbol);
            while (Level_Symbol) {
              NodeId Symbol = fC->Child(Level_Symbol);
              if (fC->Type(Symbol) == VObjectType::slQmark) {
                ventry += "?";
              } else if (fC->Type(Symbol) == VObjectType::slBinOp_Mult) {
                ventry += "* ";
              } else {
                const std::string_view symb = fC->SymName(Symbol);
                ventry += symb;
              }
              Level_Symbol = fC->Sibling(Level_Symbol);
            }
            ventry += " ";
            nb++;
          } else {
            NodeId Symbol = fC->Child(Level_symbol);

            uint32_t nbSymb = 0;
            if (fC->Type(Symbol) == VObjectType::slQmark) {
              ventry += "? ";
              nbSymb = 1;
            } else if (fC->Type(Symbol) == VObjectType::slBinOp_Mult) {
              ventry += "* ";
              nbSymb = 1;
            } else {
              const std::string_view symb = fC->SymName(Symbol);
              nbSymb = symb.size();
              std::string symbols;
              for (uint32_t i = 0; i < nbSymb; i++) {
                char s = symb[i];
                symbols += s + std::string(" ");
              }
              ventry += symbols;
            }
            nb = nb + nbSymb;
          }
          Level_symbol = fC->Sibling(Level_symbol);
        }
        ventry += ": ";
        NodeId Symbol = fC->Child(Current_state);

        if (fC->Type(Symbol) == VObjectType::slQmark) {
          ventry += "? ";
        } else if (fC->Type(Symbol) == VObjectType::slBinOp_Mult) {
          ventry += "* ";
        } else {
          const std::string_view symb = fC->SymName(Symbol);
          uint32_t nbSymb = symb.size();
          std::string symbols;
          for (uint32_t i = 0; i < nbSymb; i++) {
            char s = symb[i];
            symbols += s + std::string(" ");
          }
          ventry += symbols;
        }

        ventry += ": ";
        Symbol = fC->Child(Next_state);

        if (fC->Type(Symbol) == VObjectType::slOutput_symbol) {
          Symbol = fC->Child(Symbol);
          const std::string_view symb = fC->SymName(Symbol);
          uint32_t nbSymb = symb.size();
          std::string symbols;
          for (uint32_t i = 0; i < nbSymb; i++) {
            char s = symb[i];
            symbols += s + std::string(" ");
          }
          ventry += symbols;
        } else {
          ventry += "-";
        }

        UHDM::VectorOftable_entry* entries = defn->Table_entrys();
        if (entries == nullptr) {
          defn->Table_entrys(s.MakeTable_entryVec());
          entries = defn->Table_entrys();
        }
        UHDM::table_entry* entry = s.MakeTable_entry();
        entry->VpiParent(defn);
        entry->VpiValue(ventry);
        entry->VpiSize(nb);
        fC->populateCoreMembers(Level_input_list, Level_input_list, entry);
        entries->push_back(entry);
        break;
      }
      case VObjectType::slUdp_initial_statement: {
        NodeId Identifier = fC->Child(id);
        NodeId Value = fC->Sibling(Identifier);
        UHDM::initial* init = s.MakeInitial();
        fC->populateCoreMembers(id, id, init);
        init->VpiParent(defn);
        defn->Initial(init);
        UHDM::assign_stmt* assign_stmt = s.MakeAssign_stmt();
        init->Stmt(assign_stmt);
        UHDM::ref_obj* ref = s.MakeRef_obj();
        ref->VpiName(fC->SymName(Identifier));
        ref->VpiParent(assign_stmt);
        fC->populateCoreMembers(Identifier, Identifier, ref);
        assign_stmt->Lhs(ref);
        fC->populateCoreMembers(id, id, assign_stmt);
        assign_stmt->VpiParent(init);
        UHDM::constant* c = s.MakeConstant();
        assign_stmt->Rhs(c);
        std::string val = StrCat("UINT:", fC->SymName(Value));
        c->VpiValue(val);
        c->VpiDecompile(fC->SymName(Value));
        c->VpiSize(64);
        c->VpiConstType(vpiUIntConst);
        c->VpiParent(assign_stmt);
        fC->populateCoreMembers(Value, Value, c);
        break;
      }
      default:
        break;
    }
    if (current.m_sibling) stack.push(current.m_sibling);
    if (current.m_child) stack.push(current.m_child);
  }

  return true;
}

bool CompileModule::collectModuleObjects_(CollectType collectType) {
  std::vector<VObjectType> stopPoints = {
      VObjectType::slConditional_generate_construct,
      VObjectType::slGenerate_module_conditional_statement,
      VObjectType::slLoop_generate_construct,
      VObjectType::slGenerate_module_loop_statement,
      VObjectType::slPar_block,
      VObjectType::slSeq_block,
      VObjectType::slModule_declaration,
      VObjectType::slClass_declaration,
      VObjectType::slFunction_body_declaration,
      VObjectType::slTask_body_declaration,
      VObjectType::slGenerate_region};

  for (uint32_t i = 0; i < m_module->m_fileContents.size(); i++) {
    const FileContent* fC = m_module->m_fileContents[i];
    VObject current = fC->Object(m_module->m_nodeIds[i]);
    NodeId id = current.m_child;

    NodeId endOfBlockId;
    if (m_module->getGenBlockId()) {
      id = m_module->getGenBlockId();
      endOfBlockId = id;
      while (endOfBlockId) {
        VObjectType type = fC->Type(endOfBlockId);
        if (type == VObjectType::slEnd) break;
        if (type == VObjectType::slElse) break;
        endOfBlockId = fC->Sibling(endOfBlockId);
      }
      if (!endOfBlockId) endOfBlockId = fC->Sibling(m_module->getGenBlockId());
      if (fC->Type(id) == VObjectType::slGenerate_item) {
        id = fC->Parent(id);
      }
    }
    if (!id) id = current.m_sibling;
    if (!id) return false;

    if (collectType == CollectType::FUNCTION) {
      // Package imports
      std::vector<FileCNodeId> pack_imports;
      // - Local file imports
      for (auto import : fC->getObjects(VObjectType::slPackage_import_item)) {
        pack_imports.push_back(import);
      }

      for (auto pack_import : pack_imports) {
        const FileContent* pack_fC = pack_import.fC;
        NodeId pack_id = pack_import.nodeId;
        m_helper.importPackage(m_module, m_design, pack_fC, pack_id,
                               m_compileDesign);
      }
    }
    NodeId ParameterPortListId;
    std::stack<NodeId> stack;
    stack.push(id);
    VObjectType port_direction = VObjectType::slNoType;

    while (!stack.empty()) {
      id = stack.top();
      if (endOfBlockId && (id == endOfBlockId)) {
        break;
      }
      if (ParameterPortListId && (id == ParameterPortListId)) {
        ParameterPortListId = InvalidNodeId;
      }
      stack.pop();
      current = fC->Object(id);
      VObjectType type = fC->Type(id);
      bool skipChildren = false;
      switch (type) {
        case VObjectType::slPackage_import_item: {
          if (collectType != CollectType::FUNCTION) break;
          m_helper.importPackage(m_module, m_design, fC, id, m_compileDesign);
          m_helper.compileImportDeclaration(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slAnsi_port_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          m_helper.compileAnsiPortDeclaration(m_module, fC, id, port_direction);
          m_attributes = nullptr;
          break;
        }
        case VObjectType::slPort: {
          if (fC->Child(id)) {
            m_hasNonNullPort = true;
          }
          if (collectType == CollectType::FUNCTION) m_nbPorts++;
          if (collectType != CollectType::DEFINITION) break;
          m_helper.compilePortDeclaration(m_module, fC, id, m_compileDesign,
                                          port_direction,
                                          m_hasNonNullPort || (m_nbPorts > 1));
          m_attributes = nullptr;
          break;
        }
        case VObjectType::slElaboration_system_task: {
          if (collectType != CollectType::FUNCTION) break;
          m_helper.elaborationSystemTask(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slInput_declaration:
        case VObjectType::slOutput_declaration:
        case VObjectType::slInout_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          m_helper.compilePortDeclaration(m_module, fC, id, m_compileDesign,
                                          port_direction, m_hasNonNullPort);
          m_attributes = nullptr;
          break;
        }
        case VObjectType::slClocking_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          compileClockingBlock_(fC, id);
          break;
        }
        case VObjectType::slNet_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          m_helper.compileNetDeclaration(m_module, fC, id, false,
                                         m_compileDesign);
          m_attributes = nullptr;
          break;
        }
        case VObjectType::slData_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          m_helper.compileDataDeclaration(m_module, fC, id, false,
                                          m_compileDesign, Reduce::No,
                                          m_attributes);
          m_attributes = nullptr;
          break;
        }
        case VObjectType::slAttribute_instance: {
          if (collectType != CollectType::DEFINITION) break;
          m_attributes =
              m_helper.compileAttributes(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slPort_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          m_helper.compilePortDeclaration(m_module, fC, id, m_compileDesign,
                                          port_direction, m_hasNonNullPort);
          m_attributes = nullptr;
          break;
        }
        case VObjectType::slContinuous_assign: {
          if (collectType != CollectType::OTHER) break;
          m_helper.compileContinuousAssignment(m_module, fC, fC->Child(id),
                                               m_compileDesign, m_instance);
          break;
        }
        case VObjectType::slAlways_construct: {
          if (collectType != CollectType::OTHER) break;
          m_helper.compileAlwaysBlock(m_module, fC, id, m_compileDesign,
                                      m_instance);
          break;
        }
        case VObjectType::slParameter_port_list: {
          if (collectType != CollectType::DEFINITION) break;
          ParameterPortListId = id;
          NodeId list_of_param_assignments = fC->Child(id);
          while (list_of_param_assignments) {
            m_helper.compileParameterDeclaration(
                m_module, fC, list_of_param_assignments, m_compileDesign,
                m_instance != nullptr ? Reduce::Yes : Reduce::No, false,
                m_instance, false, false);
            list_of_param_assignments = fC->Sibling(list_of_param_assignments);
          }
          break;
        }
        case VObjectType::slParameter_declaration: {
          if (collectType != CollectType::DEFINITION) break;

          NodeId list_of_type_assignments = fC->Child(id);
          if (fC->Type(list_of_type_assignments) ==
                  VObjectType::slList_of_type_assignments ||
              fC->Type(list_of_type_assignments) == VObjectType::slType) {
            // Type param
            m_helper.compileParameterDeclaration(
                m_module, fC, list_of_type_assignments, m_compileDesign,
                m_instance != nullptr ? Reduce::Yes : Reduce::No, false,
                m_instance, ParameterPortListId, false);

          } else {
            m_helper.compileParameterDeclaration(
                m_module, fC, id, m_compileDesign,
                m_instance != nullptr ? Reduce::Yes : Reduce::No, false,
                m_instance, ParameterPortListId, false);
          }
          break;
        }
        case VObjectType::slLocal_parameter_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          NodeId list_of_type_assignments = fC->Child(id);
          if (fC->Type(list_of_type_assignments) ==
                  VObjectType::slList_of_type_assignments ||
              fC->Type(list_of_type_assignments) == VObjectType::slType) {
            // Type param
            m_helper.compileParameterDeclaration(
                m_module, fC, list_of_type_assignments, m_compileDesign,
                m_instance != nullptr ? Reduce::Yes : Reduce::No, true,
                m_instance, ParameterPortListId, false);

          } else {
            m_helper.compileParameterDeclaration(
                m_module, fC, id, m_compileDesign,
                m_instance != nullptr ? Reduce::Yes : Reduce::No, true,
                m_instance, ParameterPortListId, false);
          }
          break;
        }
        case VObjectType::slTask_declaration: {
          // Called twice, placeholder first, then definition
          if (collectType == CollectType::OTHER) break;
          m_helper.compileTask(m_module, fC, id, m_compileDesign, Reduce::No,
                               m_instance, false);
          break;
        }
        case VObjectType::slFunction_declaration: {
          // Called twice, placeholder first, then definition
          if (collectType == CollectType::OTHER) break;
          m_helper.compileFunction(m_module, fC, id, m_compileDesign,
                                   Reduce::No, m_instance, false);
          break;
        }
        case VObjectType::slDpi_import_export: {
          if (collectType != CollectType::FUNCTION) break;
          NodeId Import = fC->Child(id);
          NodeId StringLiteral = fC->Sibling(Import);
          NodeId Context_keyword = fC->Sibling(StringLiteral);
          NodeId Task_prototype;
          if (fC->Type(Context_keyword) == VObjectType::slContext_keyword)
            Task_prototype = fC->Sibling(Context_keyword);
          else
            Task_prototype = Context_keyword;
          if (fC->Type(Task_prototype) == VObjectType::slTask_prototype) {
            Task* task = m_helper.compileTaskPrototype(m_module, fC, id,
                                                       m_compileDesign);
            m_module->insertTask(task);
          } else {
            Function* func = m_helper.compileFunctionPrototype(m_module, fC, id,
                                                               m_compileDesign);
            m_module->insertFunction(func);
          }
          break;
        }
        case VObjectType::slAssertion_item: {
          if (collectType != CollectType::OTHER) break;
          m_helper.compileAssertionItem(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slClass_declaration: {
          if (collectType != CollectType::OTHER) break;
          NodeId nameId = fC->Child(id);
          if (fC->Type(nameId) == VObjectType::slVirtual) {
            nameId = fC->Sibling(nameId);
          }
          const std::string_view name = fC->SymName(nameId);
          FileCNodeId fnid(fC, nameId);
          m_module->addObject(type, fnid);

          std::string completeName = StrCat(m_module->getName(), "::", name);

          DesignComponent* comp = fC->getComponentDefinition(completeName);

          m_module->addNamedObject(name, fnid, comp);
          break;
        }
        case VObjectType::slClass_constructor_declaration: {
          if (collectType != CollectType::OTHER) break;
          m_helper.compileClassConstructorDeclaration(m_module, fC, id,
                                                      m_compileDesign);
          break;
        }
        case VObjectType::slBind_directive: {
          skipChildren = true;
          if (collectType != CollectType::OTHER) break;
          m_helper.compileBindStmt(m_module, fC, id, m_compileDesign,
                                   m_instance);
          break;
        }
        case VObjectType::slLet_declaration: {
          if (collectType != CollectType::FUNCTION) break;
          m_helper.compileLetDeclaration(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slParam_assignment:
        case VObjectType::slHierarchical_instance:
        case VObjectType::slUdp_instance:
        case VObjectType::slGate_instantiation:
        case VObjectType::slConditional_generate_construct:
        case VObjectType::slGenerate_module_conditional_statement:
        case VObjectType::slLoop_generate_construct:
        case VObjectType::slGenerate_module_loop_statement:
        case VObjectType::slPar_block:
        case VObjectType::slSeq_block:
        case VObjectType::slDefparam_assignment: {
          if (collectType != CollectType::OTHER) break;
          FileCNodeId fnid(fC, id);
          m_module->addObject(type, fnid);
          break;
        }
        case VObjectType::slUdp_instantiation: {
          if (collectType != CollectType::OTHER) break;
          FileCNodeId fnid(fC, id);
          m_module->addObject(type, fnid);
          m_helper.compileUdpInstantiation(m_module, fC, m_compileDesign, id,
                                           m_instance);
          break;
        }
        case VObjectType::slN_input_gate_instance:
        case VObjectType::slN_output_gate_instance: {
          if (collectType != CollectType::OTHER) break;
          FileCNodeId fnid(fC, id);
          m_module->addObject(type, fnid);
          m_helper.compileGateInstantiation(m_module, fC, m_compileDesign, id,
                                            m_instance);
          break;
        }
        case VObjectType::slInterface_instantiation:
        case VObjectType::slModule_instantiation:
        case VObjectType::slProgram_instantiation: {
          if (collectType != CollectType::OTHER) break;
          m_helper.compileInstantiation(m_module, fC, m_compileDesign, id,
                                        m_instance);
          FileCNodeId fnid(fC, id);
          m_module->addObject(type, fnid);
          break;
        }
        case VObjectType::slInitial_construct:
          if (collectType != CollectType::OTHER) break;
          m_helper.compileInitialBlock(m_module, fC, id, m_compileDesign);
          break;
        case VObjectType::slFinal_construct:
          if (collectType != CollectType::OTHER) break;
          m_helper.compileFinalBlock(m_module, fC, id, m_compileDesign);
          break;
        case VObjectType::slStringConst: {
          if (collectType != CollectType::DEFINITION) break;
          NodeId sibling = fC->Sibling(id);
          if (!sibling) {
            if (fC->Type(fC->Parent(id)) != VObjectType::slModule_declaration)
              break;
            const std::string_view endLabel = fC->SymName(id);
            std::string_view moduleName = m_module->getName();
            moduleName = StringUtils::ltrim_until(moduleName, '@');
            moduleName = StringUtils::ltrim_until(moduleName, ':');
            moduleName = StringUtils::ltrim_until(moduleName, ':');
            if (endLabel != moduleName) {
              Location loc(fC->getFileId(m_module->getNodeIds()[0]),
                           fC->Line(m_module->getNodeIds()[0]),
                           fC->Column(m_module->getNodeIds()[0]),
                           m_compileDesign->getCompiler()
                               ->getSymbolTable()
                               ->registerSymbol(moduleName));
              Location loc2(fC->getFileId(id), fC->Line(id), fC->Column(id),
                            m_compileDesign->getCompiler()
                                ->getSymbolTable()
                                ->registerSymbol(endLabel));
              Error err(ErrorDefinition::COMP_UNMATCHED_LABEL, loc, loc2);
              m_compileDesign->getCompiler()->getErrorContainer()->addError(
                  err);
            }
          }
          break;
        }
        default:
          break;
      }

      if (current.m_sibling) stack.push(current.m_sibling);
      if (current.m_child && (!skipChildren)) {
        if (!stopPoints.empty()) {
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
  if (collectType == CollectType::DEFINITION) {
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
  }

  return true;
}

bool CompileModule::collectInterfaceObjects_(CollectType collectType) {
  std::vector<VObjectType> stopPoints = {
      VObjectType::slConditional_generate_construct,
      VObjectType::slGenerate_module_conditional_statement,
      VObjectType::slGenerate_interface_conditional_statement,
      VObjectType::slLoop_generate_construct,
      VObjectType::slGenerate_module_loop_statement,
      VObjectType::slGenerate_interface_loop_statement,
      VObjectType::slPar_block,
      VObjectType::slSeq_block,
      VObjectType::slModule_declaration,
      VObjectType::slInterface_declaration,
      VObjectType::slClass_declaration,
      VObjectType::slFunction_body_declaration,
      VObjectType::slTask_body_declaration};
  for (uint32_t i = 0; i < m_module->m_fileContents.size(); i++) {
    const FileContent* fC = m_module->m_fileContents[i];
    VObject current = fC->Object(m_module->m_nodeIds[i]);
    NodeId id = current.m_child;
    if (!id) id = current.m_sibling;
    if (!id) return false;

    if (collectType == CollectType::FUNCTION) {
      // Package imports
      std::vector<FileCNodeId> pack_imports;
      // - Local file imports
      for (auto import : fC->getObjects(VObjectType::slPackage_import_item)) {
        pack_imports.push_back(import);
      }

      for (auto pack_import : pack_imports) {
        const FileContent* pack_fC = pack_import.fC;
        NodeId pack_id = pack_import.nodeId;
        m_helper.importPackage(m_module, m_design, pack_fC, pack_id,
                               m_compileDesign);
      }
    }
    NodeId ParameterPortListId;
    std::stack<NodeId> stack;
    stack.push(id);
    VObjectType port_direction = VObjectType::slNoType;
    while (!stack.empty()) {
      id = stack.top();
      if (ParameterPortListId && (id == ParameterPortListId)) {
        ParameterPortListId = InvalidNodeId;
      }
      stack.pop();
      current = fC->Object(id);
      VObjectType type = fC->Type(id);
      switch (type) {
        case VObjectType::slPackage_import_item: {
          if (collectType != CollectType::FUNCTION) break;
          m_helper.importPackage(m_module, m_design, fC, id, m_compileDesign);
          m_helper.compileImportDeclaration(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slParameter_port_list: {
          if (collectType != CollectType::DEFINITION) break;
          ParameterPortListId = id;
          NodeId list_of_param_assignments = fC->Child(id);
          while (list_of_param_assignments) {
            m_helper.compileParameterDeclaration(
                m_module, fC, list_of_param_assignments, m_compileDesign,
                m_instance != nullptr ? Reduce::Yes : Reduce::No, false,
                m_instance, false, false);
            list_of_param_assignments = fC->Sibling(list_of_param_assignments);
          }
          break;
        }
        case VObjectType::slPort_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          m_helper.compilePortDeclaration(m_module, fC, id, m_compileDesign,
                                          port_direction, m_hasNonNullPort);
          m_attributes = nullptr;
          break;
        }
        case VObjectType::slAnsi_port_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          m_helper.compileAnsiPortDeclaration(m_module, fC, id, port_direction);
          m_attributes = nullptr;
          break;
        }
        case VObjectType::slNet_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          m_helper.compileNetDeclaration(m_module, fC, id, true,
                                         m_compileDesign);
          m_attributes = nullptr;
          break;
        }
        case VObjectType::slData_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          m_helper.compileDataDeclaration(m_module, fC, id, true,
                                          m_compileDesign, Reduce::No,
                                          m_attributes);
          m_attributes = nullptr;
          break;
        }
        case VObjectType::slAttribute_instance: {
          if (collectType != CollectType::DEFINITION) break;
          m_attributes =
              m_helper.compileAttributes(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slContinuous_assign: {
          if (collectType != CollectType::OTHER) break;
          m_helper.compileContinuousAssignment(m_module, fC, fC->Child(id),
                                               m_compileDesign, m_instance);
          break;
        }
        case VObjectType::slAlways_construct: {
          if (collectType != CollectType::OTHER) break;
          m_helper.compileAlwaysBlock(m_module, fC, id, m_compileDesign,
                                      m_instance);
          break;
        }
        case VObjectType::slTask_declaration: {
          if (collectType != CollectType::FUNCTION) break;
          m_helper.compileTask(m_module, fC, id, m_compileDesign, Reduce::No,
                               m_instance, false);
          break;
        }
        case VObjectType::slFunction_declaration: {
          if (collectType != CollectType::FUNCTION) break;
          m_helper.compileFunction(m_module, fC, id, m_compileDesign,
                                   Reduce::No, m_instance, false);
          break;
        }
        case VObjectType::slDpi_import_export: {
          if (collectType != CollectType::FUNCTION) break;
          Function* func = m_helper.compileFunctionPrototype(m_module, fC, id,
                                                             m_compileDesign);
          m_module->insertFunction(func);
          break;
        }
        case VObjectType::slAssertion_item: {
          if (collectType != CollectType::OTHER) break;
          m_helper.compileAssertionItem(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slElaboration_system_task: {
          if (collectType != CollectType::FUNCTION) break;
          m_helper.elaborationSystemTask(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slInterface_instantiation:
        case VObjectType::slModule_instantiation:
        case VObjectType::slProgram_instantiation: {
          if (collectType != CollectType::OTHER) break;
          m_helper.compileInstantiation(m_module, fC, m_compileDesign, id,
                                        m_instance);
          FileCNodeId fnid(fC, id);
          m_module->addObject(type, fnid);
          break;
        }
        case VObjectType::slClocking_declaration:
          if (collectType != CollectType::OTHER) break;
          compileClockingBlock_(fC, id);
          break;
        case VObjectType::slGenerate_interface_item: {
          if (collectType != CollectType::OTHER) break;
          // TODO: rewrite this rough implementation
          VObjectTypeUnorderedSet types = {VObjectType::slModport_item};
          std::vector<NodeId> items = fC->sl_collect_all(id, types);
          for (auto nodeId : items) {
            Location loc(fC->getFileId(nodeId), fC->Line(nodeId),
                         fC->Column(nodeId));
            Error err(ErrorDefinition::COMP_NO_MODPORT_IN_GENERATE, loc);
            m_errors->addError(err);
          }
          break;
        }
        case VObjectType::slModport_item:
          if (collectType != CollectType::OTHER) break;
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
            const std::string_view modportsymb = fC->SymName(modportname);
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
                    if (port->getFileContent()->Name(port->getNodeId()) ==
                        port_symbol) {
                      port_exists = true;
                      break;
                    }
                  }
                  NodeId Expression = fC->Sibling(simple_port_name);
                  if (!Expression) {
                    // If expression is not null, we cannot conclude here
                    if (!port_exists) {
                      Location loc(fC->getFileId(simple_port_name),
                                   fC->Line(simple_port_name),
                                   fC->Column(simple_port_name),
                                   m_symbols->registerSymbol(
                                       fC->SymName(simple_port_name)));
                      Error err(ErrorDefinition::COMP_MODPORT_UNDEFINED_PORT,
                                loc);
                      m_errors->addError(err);
                    }
                  }
                  Signal signal(fC, simple_port_name,
                                VObjectType::slData_type_or_implicit,
                                port_direction_type, InvalidNodeId, false);
                  m_module->insertModPort(modportsymb, signal, modportname);
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
                if (cb == nullptr) {
                  Location loc(fC->getFileId(clocking_block_name),
                               fC->Line(clocking_block_name),
                               fC->Column(clocking_block_name),
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
          break;
        case VObjectType::slInitial_construct:
          if (collectType != CollectType::OTHER) break;
          m_helper.compileInitialBlock(m_module, fC, id, m_compileDesign);
          break;
        case VObjectType::slFinal_construct:
          if (collectType != CollectType::OTHER) break;
          m_helper.compileFinalBlock(m_module, fC, id, m_compileDesign);
          break;
        case VObjectType::slParameter_declaration: {
          if (collectType != CollectType::DEFINITION) break;

          NodeId list_of_type_assignments = fC->Child(id);
          if (fC->Type(list_of_type_assignments) ==
                  VObjectType::slList_of_type_assignments ||
              fC->Type(list_of_type_assignments) == VObjectType::slType) {
            // Type param
            m_helper.compileParameterDeclaration(
                m_module, fC, list_of_type_assignments, m_compileDesign,
                m_instance != nullptr ? Reduce::Yes : Reduce::No, false,
                m_instance, ParameterPortListId, false);

          } else {
            m_helper.compileParameterDeclaration(
                m_module, fC, id, m_compileDesign,
                m_instance != nullptr ? Reduce::Yes : Reduce::No, false,
                m_instance, ParameterPortListId, false);
          }
          break;
        }
        case VObjectType::slLocal_parameter_declaration: {
          if (collectType != CollectType::DEFINITION) break;
          NodeId list_of_type_assignments = fC->Child(id);
          if (fC->Type(list_of_type_assignments) ==
                  VObjectType::slList_of_type_assignments ||
              fC->Type(list_of_type_assignments) == VObjectType::slType) {
            // Type param
            m_helper.compileParameterDeclaration(
                m_module, fC, list_of_type_assignments, m_compileDesign,
                m_instance != nullptr ? Reduce::Yes : Reduce::No, true,
                m_instance, ParameterPortListId, false);

          } else {
            m_helper.compileParameterDeclaration(
                m_module, fC, id, m_compileDesign,
                m_instance != nullptr ? Reduce::Yes : Reduce::No, true,
                m_instance, ParameterPortListId, false);
          }
          break;
        }
        case VObjectType::slBind_directive: {
          if (collectType != CollectType::OTHER) break;
          m_helper.compileBindStmt(m_module, fC, id, m_compileDesign,
                                   m_instance);
          break;
        }
        case VObjectType::slConditional_generate_construct:
        case VObjectType::slGenerate_interface_conditional_statement:
        case VObjectType::slLoop_generate_construct:
        case VObjectType::slGenerate_interface_loop_statement:
        case VObjectType::slParam_assignment:
        case VObjectType::slDefparam_assignment: {
          if (collectType != CollectType::OTHER) break;
          FileCNodeId fnid(fC, id);
          m_module->addObject(type, fnid);
          break;
        }
        case VObjectType::slLet_declaration: {
          if (collectType != CollectType::FUNCTION) break;
          m_helper.compileLetDeclaration(m_module, fC, id, m_compileDesign);
          break;
        }
        case VObjectType::slEndinterface: {
          if (collectType != CollectType::DEFINITION) break;
          NodeId InterfaceIdentifier = fC->Sibling(id);
          if (InterfaceIdentifier) {
            NodeId label = fC->Child(InterfaceIdentifier);
            const std::string_view endLabel = fC->SymName(label);
            std::string_view moduleName = m_module->getName();
            moduleName = StringUtils::ltrim_until(moduleName, '@');
            moduleName = StringUtils::ltrim_until(moduleName, ':');
            moduleName = StringUtils::ltrim_until(moduleName, ':');
            if (endLabel != moduleName) {
              Location loc(fC->getFileId(m_module->getNodeIds()[0]),
                           fC->Line(m_module->getNodeIds()[0]),
                           fC->Column(m_module->getNodeIds()[0]),
                           m_compileDesign->getCompiler()
                               ->getSymbolTable()
                               ->registerSymbol(moduleName));
              Location loc2(fC->getFileId(id), fC->Line(id), fC->Column(id),
                            m_compileDesign->getCompiler()
                                ->getSymbolTable()
                                ->registerSymbol(endLabel));
              Error err(ErrorDefinition::COMP_UNMATCHED_LABEL, loc, loc2);
              m_compileDesign->getCompiler()->getErrorContainer()->addError(
                  err);
            }
          }
          break;
        }
        default:
          break;
      }

      if (current.m_sibling) stack.push(current.m_sibling);
      if (current.m_child) {
        if (!stopPoints.empty()) {
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

  if (collectType == CollectType::DEFINITION) {
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
  }
  return true;
}

bool CompileModule::checkModule_() {
  FileSystem* const fileSystem = FileSystem::getInstance();
  int32_t countMissingType = 0;
  int32_t countMissingDirection = 0;
  Location* missingTypeLoc = nullptr;
  Location* missingDirectionLoc = nullptr;
  for (Signal* port : m_module->m_ports) {
    if (port->isInterface()) continue;
    const FileContent* fC = port->getFileContent();
    NodeId portId = port->getNodeId();
    if (fC->Type(portId) == VObjectType::slPort) {
      NodeId expName = fC->Child(portId);
      if (fC->Type(expName) == VObjectType::slStringConst) {
        // Port expression
        continue;
      }
    }
    if (port->getType() == VObjectType::slData_type_or_implicit) {
      if (port->getDirection() == VObjectType::slPortDir_Out ||
          port->getDirection() == VObjectType::slPortDir_Inout) {
        if (countMissingType == 0)
          missingTypeLoc = new Location(
              fileSystem->copy(
                  port->getFileContent()->getFileId(port->getNodeId()),
                  m_symbols),
              port->getFileContent()->Line(port->getNodeId()),
              port->getFileContent()->Column(port->getNodeId()),
              m_symbols->registerSymbol(port->getName()));
        countMissingType++;
      }
    }
    if (port->getDirection() == VObjectType::slNoType) {
      if (countMissingDirection == 0)
        missingDirectionLoc = new Location(
            fileSystem->copy(
                port->getFileContent()->getFileId(port->getNodeId()),
                m_symbols),
            port->getFileContent()->Line(port->getNodeId()),
            port->getFileContent()->Column(port->getNodeId()),
            m_symbols->registerSymbol(port->getName()));
      countMissingDirection++;
    }
  }
  if (countMissingType) {
    Location countLoc(
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
    if (countMissingType) {
      Error err(ErrorDefinition::COMP_UNSPECIFIED_PORT, *missingDirectionLoc);
      m_errors->addError(err);
    }
    delete missingDirectionLoc;
  }

  return true;
}

bool CompileModule::checkInterface_() {
  FileSystem* const fileSystem = FileSystem::getInstance();
  int32_t countMissingType = 0;
  Location* missingTypeLoc = nullptr;
  for (auto& port : m_module->m_ports) {
    if (port->getType() == VObjectType::slData_type_or_implicit) {
      if (port->getDirection() == VObjectType::slPortDir_Out ||
          port->getDirection() == VObjectType::slPortDir_Inout) {
        if (countMissingType == 0)
          missingTypeLoc = new Location(
              fileSystem->copy(
                  port->getFileContent()->getFileId(port->getNodeId()),
                  m_symbols),
              port->getFileContent()->Line(port->getNodeId()), 0,
              m_symbols->registerSymbol(port->getName()));
        countMissingType++;
      }
    }
  }
  if (countMissingType) {
    Location countLoc(
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

void CompileModule::compileClockingBlock_(const FileContent* fC, NodeId id) {
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

  NodeId clocking_block_type = fC->Child(id);
  NodeId clocking_block_name;
  SymbolId clocking_block_symbol;
  ClockingBlock::Type type = ClockingBlock::Regular;
  if (fC->Type(clocking_block_type) == VObjectType::slDefault)
    type = ClockingBlock::Default;
  else if (fC->Type(clocking_block_type) == VObjectType::slGlobal)
    type = ClockingBlock::Global;
  else if (fC->Type(clocking_block_type) == VObjectType::slStringConst)
    clocking_block_name = clocking_block_type;
  NodeId clocking_event = fC->Sibling(clocking_block_type);
  if (fC->Type(clocking_event) == VObjectType::slStringConst) {
    clocking_block_name = clocking_event;
    clocking_event = fC->Sibling(clocking_block_name);
  }
  if (clocking_block_name)
    clocking_block_symbol =
        m_symbols->registerSymbol(fC->SymName(clocking_block_name));
  else
    clocking_block_symbol = m_symbols->registerSymbol("unnamed_clocking_block");
  UHDM::clocking_block* cblock = m_helper.compileClockingBlock(
      m_module, fC, id, m_compileDesign, nullptr, m_instance);
  ClockingBlock cb(fC, clocking_block_type, clocking_event, type, cblock);
  m_module->addClockingBlock(clocking_block_symbol, cb);
}

}  // namespace SURELOG
