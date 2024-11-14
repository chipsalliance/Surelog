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
 * File:   ElaborationStep.cpp
 * Author: alain
 *
 * Created on July 12, 2017, 8:55 PM
 */

#include "Surelog/DesignCompile/ElaborationStep.h"

#include <uhdm/expr.h>
#include <uhdm/uhdm_types.h>

#include <cstdint>
#include <cstring>
#include <functional>
#include <map>
#include <queue>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/Containers.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Design/DataType.h"
#include "Surelog/Design/DummyType.h"
#include "Surelog/Design/Enum.h"
#include "Surelog/Design/FileCNodeId.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/Function.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Netlist.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/Design/SimpleType.h"
#include "Surelog/Design/Struct.h"
#include "Surelog/Design/TfPortItem.h"
#include "Surelog/Design/Union.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Testbench/Program.h"
#include "Surelog/Testbench/Property.h"
#include "Surelog/Testbench/TypeDef.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/sv_vpi_user.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_visitor.h>

namespace SURELOG {

using namespace UHDM;  // NOLINT (using a bunch of these)

ElaborationStep::ElaborationStep(CompileDesign* compileDesign)
    : m_compileDesign(compileDesign) {
  m_exprBuilder.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
  m_exprBuilder.setDesign(m_compileDesign->getCompiler()->getDesign());
  m_helper.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
  m_symbols = m_compileDesign->getCompiler()->getSymbolTable();
  m_errors = m_compileDesign->getCompiler()->getErrorContainer();
}

ElaborationStep::~ElaborationStep() = default;

bool ElaborationStep::bindTypedefs_() {
  FileSystem* const fileSystem = FileSystem::getInstance();
  Compiler* compiler = m_compileDesign->getCompiler();
  ErrorContainer* errors = compiler->getErrorContainer();
  SymbolTable* symbols = compiler->getSymbolTable();
  Design* design = compiler->getDesign();
  Serializer& s = m_compileDesign->getSerializer();
  std::vector<std::pair<TypeDef*, DesignComponent*>> defs;
  std::map<std::string, typespec*, std::less<>> specs;
  for (const auto& file : design->getAllFileContents()) {
    FileContent* fC = file.second;
    for (const auto& typed : fC->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      defs.emplace_back(typd, fC);
    }
  }

  for (const auto& package : design->getPackageDefinitions()) {
    Package* pack = package.second;
    for (const auto& typed : pack->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      defs.emplace_back(typd, pack);
    }
  }

  for (const auto& module : design->getModuleDefinitions()) {
    ModuleDefinition* mod = module.second;
    for (const auto& typed : mod->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      defs.emplace_back(typd, mod);
    }
  }

  for (const auto& program_def : design->getProgramDefinitions()) {
    Program* program = program_def.second;
    for (const auto& typed : program->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      defs.emplace_back(typd, program);
    }
  }

  for (const auto& class_def : design->getClassDefinitions()) {
    ClassDefinition* classp = class_def.second;
    for (const auto& typed : classp->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      defs.emplace_back(typd, classp);
    }
  }

  for (auto& defTuple : defs) {
    TypeDef* typd = defTuple.first;
    DesignComponent* comp = defTuple.second;
    const DataType* prevDef = typd->getDefinition();
    bool noTypespec = false;
    if (prevDef) {
      prevDef = prevDef->getActual();
      if (prevDef->getTypespec() == nullptr)
        noTypespec = true;
      else {
        specs.emplace(prevDef->getTypespec()->VpiName(),
                      prevDef->getTypespec());
        if (Package* pack = valuedcomponenti_cast<Package*>(comp)) {
          std::string name =
              StrCat(pack->getName(), "::", prevDef->getTypespec()->VpiName());
          specs.emplace(name, prevDef->getTypespec());
        }
        if (ClassDefinition* pack =
                valuedcomponenti_cast<ClassDefinition*>(comp)) {
          std::string name =
              StrCat(pack->getName(), "::", prevDef->getTypespec()->VpiName());
          specs.emplace(name, prevDef->getTypespec());
        }
      }
    }

    if (noTypespec == true) {
      if (prevDef && prevDef->getCategory() == DataType::Category::DUMMY) {
        const DataType* def =
            bindTypeDef_(typd, comp, ErrorDefinition::NO_ERROR_MESSAGE);
        if (def && (typd != def)) {
          typd->setDefinition(def);
          typd->setDataType((DataType*)def);
          NodeId id = typd->getDefinitionNode();
          const FileContent* fC = typd->getFileContent();
          NodeId Packed_dimension = fC->Sibling(id);
          typespec* tpclone = nullptr;
          if (Packed_dimension &&
              fC->Type(Packed_dimension) == VObjectType::paPacked_dimension) {
            tpclone = m_helper.compileTypespec(
                defTuple.second, typd->getFileContent(),
                typd->getDefinitionNode(), m_compileDesign, Reduce::Yes,
                nullptr, nullptr, false);
          } else if (typespec* tps = def->getTypespec()) {
            ElaboratorContext elaboratorContext(&s, false, true);
            tpclone =
                (typespec*)UHDM::clone_tree((any*)tps, &elaboratorContext);
            ref_typespec* rt = s.MakeRef_typespec();
            rt->VpiParent(tpclone);
            rt->Actual_typespec(tps);
            tpclone->Typedef_alias(rt);
          }
          if (typespec* unpacked = prevDef->getUnpackedTypespec()) {
            ElaboratorContext elaboratorContext(&s, false, true);
            array_typespec* unpacked_clone = (array_typespec*)UHDM::clone_tree(
                (any*)unpacked, &elaboratorContext);
            if (tpclone != nullptr) {
              ref_typespec* rt = s.MakeRef_typespec();
              rt->VpiParent(unpacked_clone);
              rt->Actual_typespec(tpclone);
              unpacked_clone->Elem_typespec(rt);
            }
            tpclone = unpacked_clone;
          }

          if (tpclone) {
            typd->setTypespec(tpclone);
            tpclone->VpiName(typd->getName());
            specs.emplace(typd->getName(), tpclone);
            if (Package* pack = valuedcomponenti_cast<Package*>(comp)) {
              std::string name = StrCat(pack->getName(), "::", typd->getName());
              specs.emplace(name, tpclone);
            }
          }
        }
      }
      if (typd->getTypespec() == nullptr) {
        const FileContent* typeF = typd->getFileContent();
        NodeId typeId = typd->getDefinitionNode();
        UHDM::typespec* ts = m_helper.compileTypespec(
            defTuple.second, typeF, typeId, m_compileDesign, Reduce::Yes,
            nullptr, nullptr, false);
        if (ts) {
          ts->VpiName(typd->getName());
          std::string name;
          if (typeF->Type(typeId) == VObjectType::slStringConst) {
            name = typeF->SymName(typeId);
          } else {
            name = typd->getName();
          }
          specs.emplace(typd->getName(), ts);
          if (Package* pack = valuedcomponenti_cast<Package*>(comp)) {
            std::string name = StrCat(pack->getName(), "::", typd->getName());
            specs.emplace(name, ts);
          }
          if (ClassDefinition* pack =
                  valuedcomponenti_cast<ClassDefinition*>(comp)) {
            std::string name = StrCat(pack->getName(), "::", typd->getName());
            specs.emplace(name, ts);
          }
          if (ts->UhdmType() == uhdmunsupported_typespec) {
            Location loc1(fileSystem->toPathId(ts->VpiFile(), symbols),
                          ts->VpiLineNo(), ts->VpiColumnNo(),
                          symbols->registerSymbol(name));
            Error err1(ErrorDefinition::COMP_UNDEFINED_TYPE, loc1);
            errors->addError(err1);
          }
        }
        typd->setTypespec(ts);
        if (DataType* dt = (DataType*)typd->getDataType()) {
          if (dt->getTypespec() == nullptr) {
            dt->setTypespec(ts);
          }
        }
      }
    } else if (prevDef == nullptr) {
      const DataType* def =
          bindTypeDef_(typd, comp, ErrorDefinition::NO_ERROR_MESSAGE);
      if (def && (typd != def)) {
        typd->setDefinition(def);
        typd->setDataType((DataType*)def);
        typd->setTypespec(nullptr);
        UHDM::typespec* ts = m_helper.compileTypespec(
            defTuple.second, typd->getFileContent(), typd->getDefinitionNode(),
            m_compileDesign, Reduce::Yes, nullptr, nullptr, false);
        if (ts) {
          specs.emplace(typd->getName(), ts);
          ts->VpiName(typd->getName());
          if (Package* pack = valuedcomponenti_cast<Package*>(comp)) {
            std::string name = StrCat(pack->getName(), "::", typd->getName());
            specs.emplace(name, ts);
          }
        }
        typd->setTypespec(ts);
      } else {
        if (prevDef == nullptr) {
          const FileContent* fC = typd->getFileContent();
          NodeId id = typd->getNodeId();
          std::string definition_string;
          NodeId defNode = typd->getDefinitionNode();
          VObjectType defType = fC->Type(defNode);
          if (defType == VObjectType::slStringConst) {
            definition_string = fC->SymName(defNode);
          }
          Location loc1(fC->getFileId(id), fC->Line(id), fC->Column(id),
                        symbols->registerSymbol(definition_string));
          Error err1(ErrorDefinition::COMP_UNDEFINED_TYPE, loc1);
          errors->addError(err1);
        }
      }
    }
    if (typespec* tps = typd->getTypespec()) {
      for (any* var : comp->getLateTypedefBinding()) {
        const ref_typespec* orig_rt = nullptr;
        if (expr* ex = any_cast<expr*>(var)) {
          orig_rt = ex->Typespec();
        } else if (typespec_member* ex = any_cast<typespec_member*>(var)) {
          orig_rt = ex->Typespec();
        } else if (parameter* ex = any_cast<parameter*>(var)) {
          orig_rt = ex->Typespec();
        } else if (type_parameter* ex = any_cast<type_parameter*>(var)) {
          orig_rt = ex->Typespec();
        } else if (io_decl* ex = any_cast<io_decl*>(var)) {
          orig_rt = ex->Typespec();
        }
        if (orig_rt) {
          if (const unsupported_typespec* orig_ut =
                  orig_rt->Actual_typespec<unsupported_typespec>()) {
            const std::string_view need = orig_ut->VpiName();
            if (need == tps->VpiName()) {
              m_compileDesign->getSwapedObjects().emplace(orig_ut, tps);
            }
          }
        }
      }
    }
  }
  for (const auto& module : design->getPackageDefinitions()) {
    Package* pack = module.second;
    std::vector<Package*> packages;
    packages.emplace_back(pack);
    packages.emplace_back(pack->getUnElabPackage());
    for (auto comp : packages) {
      for (any* var : comp->getLateTypedefBinding()) {
        const ref_typespec* orig_rt = nullptr;
        if (expr* ex = any_cast<expr*>(var)) {
          orig_rt = ex->Typespec();
        } else if (typespec_member* ex = any_cast<typespec_member*>(var)) {
          orig_rt = ex->Typespec();
        } else if (parameter* ex = any_cast<parameter*>(var)) {
          orig_rt = ex->Typespec();
        } else if (type_parameter* ex = any_cast<type_parameter*>(var)) {
          orig_rt = ex->Typespec();
        } else if (io_decl* ex = any_cast<io_decl*>(var)) {
          orig_rt = ex->Typespec();
        }
        if (orig_rt) {
          if (const unsupported_typespec* orig_ut =
                  orig_rt->Actual_typespec<unsupported_typespec>()) {
            const std::string_view need = orig_ut->VpiName();
            std::map<std::string, typespec*>::iterator itr = specs.find(need);
            if (itr != specs.end()) {
              m_compileDesign->getSwapedObjects().emplace(orig_ut, itr->second);
            }
          }
        }
      }
    }
  }
  for (const auto& module : design->getModuleDefinitions()) {
    DesignComponent* comp = module.second;
    for (any* var : comp->getLateTypedefBinding()) {
      const ref_typespec* orig_rt = nullptr;
      if (expr* ex = any_cast<expr*>(var)) {
        orig_rt = ex->Typespec();
      } else if (typespec_member* ex = any_cast<typespec_member*>(var)) {
        orig_rt = ex->Typespec();
      } else if (parameter* ex = any_cast<parameter*>(var)) {
        orig_rt = ex->Typespec();
      } else if (type_parameter* ex = any_cast<type_parameter*>(var)) {
        orig_rt = ex->Typespec();
      } else if (io_decl* ex = any_cast<io_decl*>(var)) {
        orig_rt = ex->Typespec();
      }
      if (orig_rt) {
        if (const unsupported_typespec* orig_ut =
                orig_rt->Actual_typespec<unsupported_typespec>()) {
          const std::string_view need = orig_ut->VpiName();
          std::map<std::string, typespec*>::iterator itr = specs.find(need);
          if (itr != specs.end()) {
            m_compileDesign->getSwapedObjects().emplace(orig_ut, itr->second);
          }
        }
      }
    }
  }
  for (const auto& module : design->getClassDefinitions()) {
    DesignComponent* comp = module.second;
    for (any* var : comp->getLateTypedefBinding()) {
      const ref_typespec* orig_rt = nullptr;
      if (expr* ex = any_cast<expr*>(var)) {
        orig_rt = ex->Typespec();
      } else if (typespec_member* ex = any_cast<typespec_member*>(var)) {
        orig_rt = ex->Typespec();
      } else if (parameter* ex = any_cast<parameter*>(var)) {
        orig_rt = ex->Typespec();
      } else if (type_parameter* ex = any_cast<type_parameter*>(var)) {
        orig_rt = ex->Typespec();
      } else if (io_decl* ex = any_cast<io_decl*>(var)) {
        orig_rt = ex->Typespec();
      }
      if (orig_rt) {
        if (const unsupported_typespec* orig_ut =
                orig_rt->Actual_typespec<unsupported_typespec>()) {
          const std::string_view need = orig_ut->VpiName();
          std::map<std::string, typespec*>::iterator itr = specs.find(need);
          if (itr != specs.end()) {
            m_compileDesign->getSwapedObjects().emplace(orig_ut, itr->second);
          }
        }
      }
    }
  }

  swapTypespecPointersInUhdm(s, m_compileDesign->getSwapedObjects());
  swapTypespecPointersInTypedef(design, m_compileDesign->getSwapedObjects());

  return true;
}

static typespec* replace(
    const typespec* orig,
    std::map<const UHDM::typespec*, const UHDM::typespec*>& typespecSwapMap) {
  if (orig && (orig->UhdmType() == uhdmunsupported_typespec)) {
    auto itr = typespecSwapMap.find(orig);
    if (itr != typespecSwapMap.end()) {
      return const_cast<typespec*>(itr->second);
    }
  }
  return const_cast<typespec*>(orig);
}

static void replace(
    const ref_typespec* orig_rt,
    std::map<const UHDM::typespec*, const UHDM::typespec*>& typespecSwapMap) {
  if (orig_rt) {
    if (const unsupported_typespec* orig_ut =
            orig_rt->Actual_typespec<unsupported_typespec>()) {
      auto itr = typespecSwapMap.find(orig_ut);
      if (itr != typespecSwapMap.end()) {
        const_cast<ref_typespec*>(orig_rt)->Actual_typespec(
            const_cast<typespec*>(itr->second));
      }
    }
  }
}

void ElaborationStep::swapTypespecPointersInTypedef(
    Design* design,
    std::map<const UHDM::typespec*, const UHDM::typespec*>& typespecSwapMap) {
  for (const auto& file : design->getAllFileContents()) {
    FileContent* fC = file.second;
    for (const auto& typed : fC->getDataTypeMap()) {
      const DataType* dt = typed.second;
      while (dt) {
        ((DataType*)dt)
            ->setTypespec(replace(dt->getTypespec(), typespecSwapMap));
        dt = dt->getDefinition();
      }
    }
    for (const auto& typed : fC->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      const DataType* dt = typd;
      while (dt) {
        ((DataType*)dt)
            ->setTypespec(replace(dt->getTypespec(), typespecSwapMap));
        dt = dt->getDefinition();
      }
    }
  }
  for (const auto& package : design->getPackageDefinitions()) {
    Package* pack = package.second;
    for (const auto& typed : pack->getDataTypeMap()) {
      const DataType* dt = typed.second;
      while (dt) {
        ((DataType*)dt)
            ->setTypespec(replace(dt->getTypespec(), typespecSwapMap));
        dt = dt->getDefinition();
      }
    }
    for (const auto& typed : pack->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      const DataType* dt = typd;
      while (dt) {
        ((DataType*)dt)
            ->setTypespec(replace(dt->getTypespec(), typespecSwapMap));
        dt = dt->getDefinition();
      }
    }
  }
  for (const auto& module : design->getModuleDefinitions()) {
    ModuleDefinition* mod = module.second;
    for (const auto& typed : mod->getDataTypeMap()) {
      const DataType* dt = typed.second;
      while (dt) {
        ((DataType*)dt)
            ->setTypespec(replace(dt->getTypespec(), typespecSwapMap));
        dt = dt->getDefinition();
      }
    }
    for (const auto& typed : mod->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      const DataType* dt = typd;
      while (dt) {
        ((DataType*)dt)
            ->setTypespec(replace(dt->getTypespec(), typespecSwapMap));
        dt = dt->getDefinition();
      }
    }
  }
  for (const auto& program_def : design->getProgramDefinitions()) {
    Program* program = program_def.second;
    for (const auto& typed : program->getDataTypeMap()) {
      const DataType* dt = typed.second;
      while (dt) {
        ((DataType*)dt)
            ->setTypespec(replace(dt->getTypespec(), typespecSwapMap));
        dt = dt->getDefinition();
      }
    }
    for (const auto& typed : program->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      const DataType* dt = typd;
      while (dt) {
        ((DataType*)dt)
            ->setTypespec(replace(dt->getTypespec(), typespecSwapMap));
        dt = dt->getDefinition();
      }
    }
  }

  for (const auto& class_def : design->getClassDefinitions()) {
    ClassDefinition* classp = class_def.second;
    for (const auto& typed : classp->getDataTypeMap()) {
      const DataType* dt = typed.second;
      while (dt) {
        ((DataType*)dt)
            ->setTypespec(replace(dt->getTypespec(), typespecSwapMap));
        dt = dt->getDefinition();
      }
    }
    for (const auto& typed : classp->getTypeDefMap()) {
      TypeDef* typd = typed.second;
      const DataType* dt = typd;
      while (dt) {
        ((DataType*)dt)
            ->setTypespec(replace(dt->getTypespec(), typespecSwapMap));
        dt = dt->getDefinition();
      }
    }
  }
}

void ElaborationStep::swapTypespecPointersInUhdm(
    UHDM::Serializer& s,
    std::map<const UHDM::typespec*, const UHDM::typespec*>& typespecSwapMap) {
  // Replace all references of obsolete typespecs
  for (auto o : s.AllObjects()) {
    any* var = (any*)o.first;
    if (typespec_member* ex = any_cast<typespec_member*>(var)) {
      replace(ex->Typespec(), typespecSwapMap);
    } else if (parameter* ex = any_cast<parameter*>(var)) {
      replace(ex->Typespec(), typespecSwapMap);
    } else if (type_parameter* ex = any_cast<type_parameter*>(var)) {
      replace(ex->Typespec(), typespecSwapMap);
      replace(ex->Expr(), typespecSwapMap);
    } else if (io_decl* ex = any_cast<io_decl*>(var)) {
      replace(ex->Typespec(), typespecSwapMap);
    } else if (class_typespec* ex = any_cast<class_typespec*>(var)) {
      replace(ex->Extends(), typespecSwapMap);
    } else if (class_defn* ex = any_cast<class_defn*>(var)) {
      if (ex->Typespecs()) {
        for (auto& tps : *ex->Typespecs()) {
          tps = replace(tps, typespecSwapMap);
        }
      }
    } else if (ports* ex = any_cast<ports*>(var)) {
      replace(ex->Typespec(), typespecSwapMap);
    } else if (prop_formal_decl* ex = any_cast<prop_formal_decl*>(var)) {
      replace(ex->Typespec(), typespecSwapMap);
    } else if (class_obj* ex = any_cast<class_obj*>(var)) {
      if (ex->Typespecs()) {
        for (auto& tps : *ex->Typespecs()) {
          tps = replace(tps, typespecSwapMap);
        }
      }
      replace(ex->Class_typespec(), typespecSwapMap);
    } else if (design* ex = any_cast<design*>(var)) {
      if (ex->Typespecs()) {
        for (auto& tps : *ex->Typespecs()) {
          tps = replace(tps, typespecSwapMap);
        }
      }
    } else if (extends* ex = any_cast<extends*>(var)) {
      replace(ex->Class_typespec(), typespecSwapMap);
    } else if (logic_typespec* ex = any_cast<logic_typespec*>(var)) {
      replace(ex->Elem_typespec(), typespecSwapMap);
      replace(ex->Index_typespec(), typespecSwapMap);
    } else if (tagged_pattern* ex = any_cast<tagged_pattern*>(var)) {
      replace(ex->Typespec(), typespecSwapMap);
    } else if (array_typespec* ex = any_cast<array_typespec*>(var)) {
      replace(ex->Elem_typespec(), typespecSwapMap);
      replace(ex->Index_typespec(), typespecSwapMap);
    } else if (packed_array_typespec* ex =
                   any_cast<packed_array_typespec*>(var)) {
      replace(ex->Elem_typespec(), typespecSwapMap);
      replace(ex->Typespec(), typespecSwapMap);
    } else if (bit_typespec* ex = any_cast<bit_typespec*>(var)) {
      replace(ex->Bit_typespec(), typespecSwapMap);
      replace(ex->Typespec(), typespecSwapMap);
    } else if (enum_typespec* ex = any_cast<enum_typespec*>(var)) {
      replace(ex->Base_typespec(), typespecSwapMap);
    } else if (seq_formal_decl* ex = any_cast<seq_formal_decl*>(var)) {
      replace(ex->Typespec(), typespecSwapMap);
    } else if (instance_array* ex = any_cast<instance_array*>(var)) {
      replace(ex->Elem_typespec(), typespecSwapMap);
    } else if (named_event* ex = any_cast<named_event*>(var)) {
      replace(ex->Event_typespec(), typespecSwapMap);
    } else if (param_assign* ex = any_cast<param_assign*>(var)) {
      if (typespec* rhs = ex->Rhs<typespec>()) {
        ex->Rhs(replace(rhs, typespecSwapMap));
      }
    }
    // common pointers
    if (scope* ex = any_cast<scope*>(var)) {
      if (ex->Typespecs()) {
        for (auto& tps : *ex->Typespecs()) {
          tps = replace(tps, typespecSwapMap);
        }
      }
    }
    if (expr* ex = any_cast<expr*>(var)) {
      replace(ex->Typespec(), typespecSwapMap);
    }
    if (typespec* ex = any_cast<typespec*>(var)) {
      replace(ex->Typedef_alias(), typespecSwapMap);
    }
  }
}

bool ElaborationStep::bindTypedefsPostElab_() {
  Compiler* compiler = m_compileDesign->getCompiler();
  Design* design = compiler->getDesign();
  Serializer& s = m_compileDesign->getSerializer();
  std::queue<ModuleInstance*> queue;
  for (auto instance : design->getTopLevelModuleInstances()) {
    queue.push(instance);
  }

  while (!queue.empty()) {
    ModuleInstance* current = queue.front();
    queue.pop();
    if (current == nullptr) continue;
    for (uint32_t i = 0; i < current->getNbChildren(); i++) {
      queue.push(current->getChildren(i));
    }
    if (auto comp = current->getDefinition()) {
      for (any* var : comp->getLateTypedefBinding()) {
        const ref_typespec* orig_rt = nullptr;
        if (expr* ex = any_cast<expr*>(var)) {
          orig_rt = ex->Typespec();
        } else if (typespec_member* ex = any_cast<typespec_member*>(var)) {
          orig_rt = ex->Typespec();
        } else if (parameter* ex = any_cast<parameter*>(var)) {
          orig_rt = ex->Typespec();
        } else if (type_parameter* ex = any_cast<type_parameter*>(var)) {
          orig_rt = ex->Typespec();
        } else if (io_decl* ex = any_cast<io_decl*>(var)) {
          orig_rt = ex->Typespec();
        }
        const unsupported_typespec* orig_ut = nullptr;
        if (orig_rt) {
          orig_ut = orig_rt->Actual_typespec<unsupported_typespec>();
        }
        if (orig_ut) {
          const std::string_view need = orig_ut->VpiName();
          if (Netlist* netlist = current->getNetlist()) {
            UHDM::typespec* tps = nullptr;
            bool found = false;
            if (netlist->nets()) {
              for (auto net : *netlist->nets()) {
                if (net->VpiName() == need) {
                  if (UHDM::ref_typespec* rt = net->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                  found = true;
                  break;
                }
              }
            }
            if (tps == nullptr) {
              if (netlist->variables()) {
                for (auto var : *netlist->variables()) {
                  if (var->VpiName() == need) {
                    if (UHDM::ref_typespec* rt = var->Typespec()) {
                      tps = rt->Actual_typespec();
                    }
                    found = true;
                    break;
                  }
                }
              }
            }
            if (tps == nullptr) {
              if (const DataType* dtype = comp->getDataType(need)) {
                while (dtype) {
                  if ((tps = dtype->getTypespec())) {
                    found = true;
                    break;
                  }
                  dtype = dtype->getDefinition();
                }
              }
            }
            if (tps == nullptr) {
              if (const TypeDef* dtype = comp->getTypeDef(need)) {
                if ((tps = dtype->getTypespec())) {
                  found = true;
                } else {
                  std::string_view name = dtype->getFileContent()->SymName(
                      dtype->getDefinitionNode());
                  const DataType* def = bindDataType_(
                      name, dtype->getFileContent(), dtype->getDefinitionNode(),
                      comp, ErrorDefinition::NO_ERROR_MESSAGE);

                  if (def && (dtype != def)) {
                    dtype->setDefinition(def);
                    ((TypeDef*)dtype)->setDataType((DataType*)def);
                  }
                  const DataType* dtype2 = dtype->getDataType();
                  while (dtype2) {
                    if ((tps = dtype2->getTypespec())) {
                      found = true;
                      break;
                    }
                    dtype2 = dtype2->getDefinition();
                  }
                }
              }
            }
            if (found == true) {
              m_compileDesign->getSwapedObjects().emplace(orig_ut, tps);
            }
          }
        }
      }
      for (const auto& typed : comp->getDataTypeMap()) {
        const DataType* dt = typed.second;
        while (dt) {
          ((DataType*)dt)
              ->setTypespec(replace(dt->getTypespec(),
                                    m_compileDesign->getSwapedObjects()));
          dt = dt->getDefinition();
        }
      }
      for (const auto& typed : comp->getTypeDefMap()) {
        TypeDef* typd = typed.second;
        const DataType* dt = typd;
        while (dt) {
          ((DataType*)dt)
              ->setTypespec(replace(dt->getTypespec(),
                                    m_compileDesign->getSwapedObjects()));
          dt = dt->getDefinition();
        }
      }
    }
  }

  swapTypespecPointersInUhdm(s, m_compileDesign->getSwapedObjects());
  swapTypespecPointersInTypedef(design, m_compileDesign->getSwapedObjects());
  return true;
}

const DataType* ElaborationStep::bindTypeDef_(
    TypeDef* typd, const DesignComponent* parent,
    ErrorDefinition::ErrorType errtype) {
  Compiler* compiler = m_compileDesign->getCompiler();
  SymbolTable* symbols = compiler->getSymbolTable();
  NodeId defNode = typd->getDefinitionNode();
  const FileContent* fC = typd->getFileContent();
  VObjectType defType = fC->Type(defNode);
  std::string objName;
  if (defType == VObjectType::slStringConst) {
    objName = fC->SymName(defNode);
  } else if (defType == VObjectType::paClass_scope) {
    NodeId class_type = fC->Child(defNode);
    NodeId nameId = fC->Child(class_type);
    objName.assign(fC->SymName(nameId))
        .append("::")
        .append(fC->SymName(fC->Sibling(defNode)));
  } else {
    objName = "NOT_A_VALID_TYPE_NAME";
    symbols->registerSymbol(objName);
  }

  const DataType* result = bindDataType_(objName, fC, defNode, parent, errtype);
  if (result != typd)
    return result;
  else
    return nullptr;
}

const DataType* ElaborationStep::bindDataType_(
    std::string_view type_name, const FileContent* fC, NodeId id,
    const DesignComponent* parent, ErrorDefinition::ErrorType errtype) {
  Compiler* compiler = m_compileDesign->getCompiler();
  ErrorContainer* errors = compiler->getErrorContainer();
  SymbolTable* symbols = compiler->getSymbolTable();
  Design* design = compiler->getDesign();
  std::string libName = "work";
  if (!parent->getFileContents().empty()) {
    libName = parent->getFileContents()[0]->getLibrary()->getName();
  }
  ClassNameClassDefinitionMultiMap classes = design->getClassDefinitions();
  bool found = false;
  bool classFound = false;
  std::string class_in_lib = StrCat(libName, "@", type_name);
  ClassNameClassDefinitionMultiMap::iterator itr1 = classes.end();

  if (type_name == "signed") {
    return new DataType(fC, id, type_name, VObjectType::paSigning_Signed);
  } else if (type_name == "unsigned") {
    return new DataType(fC, id, type_name, VObjectType::paSigning_Unsigned);
  } else if (type_name == "logic") {
    return new DataType(fC, id, type_name, VObjectType::paIntVec_TypeLogic);
  } else if (type_name == "bit") {
    return new DataType(fC, id, type_name, VObjectType::paIntVec_TypeBit);
  } else if (type_name == "byte") {
    return new DataType(fC, id, type_name, VObjectType::paIntegerAtomType_Byte);
  }

  const DataType* result = nullptr;
  if ((result = parent->getDataType(type_name))) {
    found = true;
  }
  if (found == false) {
    itr1 = classes.find(class_in_lib);

    if (itr1 != classes.end()) {
      found = true;
      classFound = true;
    }
  }
  if (found == false) {
    itr1 = classes.find(type_name);

    if (itr1 != classes.end()) {
      found = true;
      classFound = true;
    }
  }
  if (found == false) {
    std::string class_in_class = StrCat(parent->getName(), "::", type_name);
    itr1 = classes.find(class_in_class);

    if (itr1 != classes.end()) {
      found = true;
      classFound = true;
    }
  }
  if (found == false) {
    if (parent->getParentScope()) {
      std::string class_in_own_package =
          StrCat(((DesignComponent*)parent->getParentScope())->getName(),
                 "::", type_name);
      itr1 = classes.find(class_in_own_package);
      if (itr1 != classes.end()) {
        found = true;
        classFound = true;
      }
    }
  }
  if (found == false) {
    for (const auto& package : parent->getAccessPackages()) {
      std::string class_in_package =
          StrCat(package->getName(), "::", type_name);
      itr1 = classes.find(class_in_package);
      if (itr1 != classes.end()) {
        found = true;
        classFound = true;
        break;
      }
      const DataType* dtype = package->getDataType(type_name);
      if (dtype) {
        found = true;
        result = dtype;
        break;
      }
    }
  }
  if (found == false) {
    const ClassDefinition* classDefinition =
        valuedcomponenti_cast<const ClassDefinition*>(parent);
    if (classDefinition) {
      if (classDefinition->getName() == type_name) {
        result = classDefinition;
        found = true;
      }
      if (found == false) {
        Parameter* param = classDefinition->getParameter(type_name);
        if (param) {
          found = true;
          result = param;
        }
      }
      if (found == false) {
        if ((result = classDefinition->getBaseDataType(type_name))) {
          found = true;
        }
      }
      if (found == false) {
        if (classDefinition->getContainer()) {
          const DataType* dtype =
              classDefinition->getContainer()->getDataType(type_name);
          if (dtype) {
            found = true;
            result = dtype;
          }
        }
      }
    }
  }
  if (found == false) {
    const TypeDef* def = parent->getTypeDef(type_name);
    if (def) {
      found = true;
      result = def;
    }
  }

  if (found == false) {
    auto res = parent->getNamedObject(type_name);
    if (res) {
      DesignComponent* comp = res->second;
      result = valuedcomponenti_cast<ClassDefinition*>(comp);
      if (result) found = true;
    }
  }
  if (found == false) {
    auto res = parent->getNamedObject(StrCat(libName, "@", type_name));
    if (res) {
      DesignComponent* comp = res->second;
      result = valuedcomponenti_cast<ClassDefinition*>(comp);
      if (result) found = true;
    }
  }
  if (found == false) {
    if (type_name.find("::") != std::string::npos) {
      std::vector<std::string_view> args;
      StringUtils::tokenizeMulti(type_name, "::", args);
      std::string_view classOrPackageName = args[0];
      std::string_view the_type_name = args[1];
      itr1 = classes.find(StrCat(libName, "@", classOrPackageName));
      if (itr1 == classes.end()) {
        if (parent->getParentScope()) {
          std::string class_in_own_package =
              StrCat(((DesignComponent*)parent->getParentScope())->getName(),
                     "::", classOrPackageName);
          itr1 = classes.find(class_in_own_package);
        }
      }
      if (itr1 != classes.end()) {
        const DataType* dtype = (*itr1).second->getDataType(the_type_name);
        if (dtype) {
          result = dtype;
          found = true;
        }
      }
      if (found == false) {
        Package* pack = design->getPackage(classOrPackageName);
        if (pack) {
          const DataType* dtype = pack->getDataType(the_type_name);
          if (dtype) {
            result = dtype;
            found = true;
          }
          if (found == false) {
            dtype = pack->getDataType(type_name);
            if (dtype) {
              result = dtype;
              found = true;
            }
          }
          if (found == false) {
            dtype = pack->getClassDefinition(type_name);
            if (dtype) {
              result = dtype;
              found = true;
            }
          }
        }
      }
    }
  }

  if ((found == false) && (errtype != ErrorDefinition::NO_ERROR_MESSAGE)) {
    Location loc1(fC->getFileId(id), fC->Line(id), fC->Column(id),
                  symbols->registerSymbol(type_name));
    Location loc2(symbols->registerSymbol(parent->getName()));
    Error err1(errtype, loc1, loc2);
    errors->addError(err1);
  } else {
    if (classFound == true) {
      // Binding
      ClassDefinition* def = (*itr1).second;
      result = def;
    }
  }
  while (result && result->getDefinition()) {
    result = result->getDefinition();
  }

  return result;
}

Variable* ElaborationStep::bindVariable_(std::string_view var_name,
                                         Scope* scope, const FileContent* fC,
                                         NodeId id,
                                         const DesignComponent* parent,
                                         ErrorDefinition::ErrorType errtype,
                                         bool returnClassParam) {
  Compiler* compiler = m_compileDesign->getCompiler();
  ErrorContainer* errors = compiler->getErrorContainer();
  SymbolTable* symbols = compiler->getSymbolTable();
  Variable* result = nullptr;

  const ClassDefinition* classDefinition =
      valuedcomponenti_cast<const ClassDefinition*>(parent);
  if (classDefinition) result = classDefinition->getProperty(var_name);

  if (result == nullptr) {
    if (scope) {
      result = scope->getVariable(var_name);
    }
  }
  if ((result == nullptr) && scope) {
    Scope* itr_scope = scope;
    while (itr_scope) {
      Procedure* proc = scope_cast<Procedure*>(itr_scope);
      if (proc) {
        for (auto param : proc->getParams()) {
          if (param->getName() == var_name) {
            result = param;
            break;
          }
        }
      }
      if (result) break;
      itr_scope = itr_scope->getParentScope();
    }
  }

  if (result == nullptr && parent) {
    for (auto package : parent->getAccessPackages()) {
      Value* val = package->getValue(var_name);
      if (val) {
        break;
      }
    }
  }

  if ((result == nullptr) && (errtype != ErrorDefinition::NO_ERROR_MESSAGE)) {
    Location loc1(fC->getFileId(id), fC->Line(id), fC->Column(id),
                  symbols->registerSymbol(var_name));
    Location loc2(symbols->registerSymbol(parent->getName()));
    Error err1(errtype, loc1, loc2);
    errors->addError(err1);
  }

  if (!returnClassParam) {
    // Class parameters datatype have no definition and are strings
    if (result) {
      const DataType* dtype = result->getDataType();
      if (dtype && !dtype->getDefinition()) {
        if (dtype->getType() == VObjectType::slStringConst) {
          result = nullptr;
        }
      }
    }
  }

  return result;
}

Variable* ElaborationStep::locateVariable_(
    const std::vector<std::string_view>& var_chain, const FileContent* fC,
    NodeId id, Scope* scope, DesignComponent* parentComponent,
    ErrorDefinition::ErrorType errtype) {
  Variable* the_obj = nullptr;
  const DesignComponent* currentComponent = parentComponent;
  for (auto var : var_chain) {
    if (var == "this") {
    } else if (var == "super") {
      const ClassDefinition* classDefinition =
          valuedcomponenti_cast<const ClassDefinition*>(currentComponent);
      if (classDefinition) {
        currentComponent = nullptr;
        const auto& baseClassMap = classDefinition->getBaseClassMap();
        if (!baseClassMap.empty()) {
          currentComponent = datatype_cast<const ClassDefinition*>(
              baseClassMap.begin()->second);
          var = "this";
        }
        if (currentComponent == nullptr) {
          var = "super";
          currentComponent = parentComponent;
        }
      }
    }

    the_obj =
        bindVariable_(var, scope, fC, id, currentComponent, errtype, false);
    if (the_obj) {
      const DataType* dtype = the_obj->getDataType();
      while (dtype && dtype->getDefinition()) {
        dtype = dtype->getDefinition();
      }
      const ClassDefinition* tmpClass =
          datatype_cast<const ClassDefinition*>(dtype);
      if (tmpClass) {
        currentComponent = tmpClass;
      }
    }
  }
  return the_obj;
}

Variable* ElaborationStep::locateStaticVariable_(
    const std::vector<std::string_view>& var_chain, const FileContent* fC,
    NodeId id, Scope* scope, DesignComponent* parentComponent,
    ErrorDefinition::ErrorType errtype) {
  std::string name;
  for (uint32_t i = 0; i < var_chain.size(); i++) {
    name += var_chain[i];
    if (i < var_chain.size() - 1) name += "::";
  }
  std::map<std::string, Variable*>::iterator itr = m_staticVariables.find(name);
  if (itr != m_staticVariables.end()) return (*itr).second;
  Variable* result = nullptr;
  Design* design = m_compileDesign->getCompiler()->getDesign();
  if (!var_chain.empty()) {
    Package* package = design->getPackage(var_chain[0]);
    if (package) {
      if (var_chain.size() > 1) {
        ClassDefinition* classDefinition =
            package->getClassDefinition(var_chain[1]);
        if (classDefinition) {
          if (var_chain.size() == 2) {
            result =
                new Variable(classDefinition, classDefinition->getFileContent(),
                             classDefinition->getNodeId(), InvalidNodeId,
                             classDefinition->getName());
          }
          if (var_chain.size() == 3) {
            std::vector<std::string_view> tmp;
            tmp.emplace_back(var_chain[2]);
            result =
                locateVariable_(tmp, fC, id, scope, classDefinition, errtype);
          }
        }
      }
    }

    if (result == nullptr) {
      ClassDefinition* classDefinition =
          design->getClassDefinition(var_chain[0]);
      if (classDefinition == nullptr) {
        if (parentComponent && parentComponent->getParentScope()) {
          const std::string name = StrCat(
              ((DesignComponent*)parentComponent->getParentScope())->getName(),
              "::", var_chain[0]);
          classDefinition = design->getClassDefinition(name);
        }
      }
      if (classDefinition) {
        if (var_chain.size() == 1)
          result =
              new Variable(classDefinition, classDefinition->getFileContent(),
                           classDefinition->getNodeId(), InvalidNodeId,
                           classDefinition->getName());
        if (var_chain.size() == 2) {
          std::vector<std::string_view> tmp;
          tmp.emplace_back(var_chain[1]);

          const DataType* dtype =
              bindDataType_(var_chain[1], fC, id, classDefinition,
                            ErrorDefinition::NO_ERROR_MESSAGE);
          if (dtype) {
            result =
                new Variable(dtype, dtype->getFileContent(), dtype->getNodeId(),
                             InvalidNodeId, dtype->getName());
          } else
            result =
                locateVariable_(tmp, fC, id, scope, classDefinition, errtype);
        }
      }
    }
  }
  if (result == nullptr) {
    if (!var_chain.empty()) {
      const DataType* dtype =
          bindDataType_(var_chain[0], fC, id, parentComponent, errtype);
      if (dtype) {
        result =
            new Variable(dtype, dtype->getFileContent(), dtype->getNodeId(),
                         InvalidNodeId, dtype->getName());
      }
    }
  }
  m_staticVariables.emplace(name, result);
  return result;
}

void checkIfBuiltInTypeOrErrorOut(DesignComponent* def, const FileContent* fC,
                                  NodeId id, const DataType* type,
                                  std::string_view interfName,
                                  ErrorContainer* errors,
                                  SymbolTable* symbols) {
  if (def == nullptr && type == nullptr && (interfName != "logic") &&
      (interfName != "byte") && (interfName != "bit") &&
      (interfName != "new") && (interfName != "expect") &&
      (interfName != "var") && (interfName != "signed") &&
      (interfName != "unsigned") && (interfName != "do") &&
      (interfName != "final") && (interfName != "global") &&
      (interfName != "soft")) {
    Location loc(fC->getFileId(id), fC->Line(id), fC->Column(id),
                 symbols->registerSymbol(interfName));
    Error err(ErrorDefinition::COMP_UNDEFINED_TYPE, loc);
    errors->addError(err);
  }
}

bool bindStructInPackage(Design* design, Signal* signal,
                         std::string_view packageName,
                         std::string_view structName) {
  Package* p = design->getPackage(packageName);
  if (p) {
    const DataType* dtype = p->getDataType(structName);
    if (dtype) {
      signal->setDataType(dtype);
      const DataType* actual = dtype->getActual();
      if (actual->getCategory() == DataType::Category::STRUCT) {
        Struct* st = (Struct*)actual;
        if (st->isNet()) {
          signal->setType(VObjectType::paNetType_Wire);
        }
      }
      return true;
    } else {
      const DataType* dtype = p->getClassDefinition(structName);
      if (dtype) {
        signal->setDataType(dtype);
        return true;
      }
    }
  }
  return false;
}

bool ElaborationStep::bindPortType_(Signal* signal, const FileContent* fC,
                                    NodeId id, Scope* scope,
                                    ModuleInstance* instance,
                                    DesignComponent* parentComponent,
                                    ErrorDefinition::ErrorType errtype) {
  if (signal->getDataType() || signal->getInterfaceDef() ||
      signal->getModPort())
    return true;
  Compiler* compiler = m_compileDesign->getCompiler();
  ErrorContainer* errors = compiler->getErrorContainer();
  SymbolTable* symbols = compiler->getSymbolTable();
  Design* design = compiler->getDesign();
  const std::string_view libName = fC->getLibrary()->getName();
  VObjectType type = fC->Type(id);
  switch (type) {
    case VObjectType::paPort:
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
            (fC->Type(Port_expression) == VObjectType::paPort_expression)) {
          NodeId if_type = fC->Child(Port_expression);
          if (fC->Type(if_type) == VObjectType::paPort_reference) {
            NodeId if_type_name_s = fC->Child(if_type);
            NodeId if_name = fC->Sibling(if_type);
            if (if_name) {
              std::string interfaceName =
                  StrCat(libName, "@", fC->SymName(if_type_name_s));
              ModuleDefinition* interface =
                  design->getModuleDefinition(interfaceName);
              if (interface) {
                signal->setInterfaceDef(interface);
              } else {
                Location loc(fC->getFileId(if_type_name_s),
                             fC->Line(if_type_name_s),
                             fC->Column(if_type_name_s),
                             symbols->registerSymbol(interfaceName));
                Error err(ErrorDefinition::COMP_UNDEFINED_INTERFACE, loc);
                errors->addError(err);
              }
            }
          }
        }
        break;
      }
    case VObjectType::paInput_declaration:
    case VObjectType::paOutput_declaration:
    case VObjectType::paInout_declaration: {
      break;
    }
    case VObjectType::paPort_declaration: {
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
        case VObjectType::paInterface_port_declaration: {
          NodeId interface_identifier = fC->Child(subNode);
          NodeId interfIdName = fC->Child(interface_identifier);
          const std::string_view interfName = fC->SymName(interfIdName);

          DesignComponent* def = nullptr;
          const DataType* type = nullptr;

          const std::pair<FileCNodeId, DesignComponent*>* datatype =
              parentComponent->getNamedObject(interfName);
          if (!datatype) {
            def = design->getClassDefinition(
                StrCat(parentComponent->getName(), "::", interfName));
          }
          if (datatype) {
            def = datatype->second;
          }
          if (def == nullptr) {
            def = design->getComponentDefinition(
                StrCat(libName, "@", interfName));
          }
          if (def == nullptr) {
            type = parentComponent->getDataType(interfName);
          }
          checkIfBuiltInTypeOrErrorOut(def, fC, id, type, interfName, errors,
                                       symbols);
          break;
        }
        case VObjectType::paInput_declaration:
        case VObjectType::paOutput_declaration:
        case VObjectType::paInout_declaration: {
          break;
        }
        default:
          break;
      }
      break;
    }
    case VObjectType::slStringConst: {
      std::string interfName;
      if (signal->getInterfaceTypeNameId()) {
        interfName = signal->getInterfaceTypeName();
      } else {
        if (NodeId typespecId = signal->getTypeSpecId()) {
          if (fC->Type(typespecId) == VObjectType::paClass_scope) {
            NodeId Class_type = fC->Child(typespecId);
            NodeId Class_type_name = fC->Child(Class_type);
            NodeId Class_scope_name = fC->Sibling(typespecId);
            if (bindStructInPackage(design, signal,
                                    fC->SymName(Class_type_name),
                                    fC->SymName(Class_scope_name)))
              return true;
          } else if (fC->Type(typespecId) == VObjectType::slStringConst) {
            interfName = fC->SymName(typespecId);
          }
        }
      }
      std::string baseName = interfName;
      std::string modPort;
      if (interfName.find('.') != std::string::npos) {
        modPort = interfName;
        modPort = StringUtils::ltrim_until(modPort, '.');
        baseName = StringUtils::rtrim_until(baseName, '.');
      } else if (interfName.find("::") != std::string::npos) {
        std::vector<std::string_view> result;
        StringUtils::tokenizeMulti(interfName, "::", result);
        if (result.size() > 1) {
          const std::string_view packName = result[0];
          const std::string_view structName = result[1];
          if (bindStructInPackage(design, signal, packName, structName))
            return true;
        }
      }

      DesignComponent* def = nullptr;
      const DataType* type = nullptr;

      const std::pair<FileCNodeId, DesignComponent*>* datatype =
          parentComponent->getNamedObject(interfName);
      if (datatype) {
        def = datatype->second;
        DataType* dt = valuedcomponenti_cast<ClassDefinition*>(def);
        if (dt) {
          signal->setDataType(dt);
        }
      } else {
        std::string name = StrCat(parentComponent->getName(), "::", interfName);
        def = design->getClassDefinition(name);
        DataType* dt = valuedcomponenti_cast<ClassDefinition*>(def);
        if (dt) {
          signal->setDataType(dt);
        }
      }
      if (def == nullptr) {
        def = design->getComponentDefinition(StrCat(libName, "@", baseName));
        if (def) {
          ModuleDefinition* module =
              valuedcomponenti_cast<ModuleDefinition*>(def);
          ClassDefinition* cl = valuedcomponenti_cast<ClassDefinition*>(def);
          if (module) {
            signal->setInterfaceDef(module);
          } else if (cl) {
            signal->setDataType(cl);
            return true;
          } else {
            def = nullptr;
          }
          if (!modPort.empty()) {
            if (module) {
              if (ModPort* modport = module->getModPort(modPort)) {
                signal->setModPort(modport);
              } else {
                def = nullptr;
              }
            }
          }
        }
      }
      if (def == nullptr) {
        def = design->getComponentDefinition(StrCat(libName, "@", baseName));
        ClassDefinition* c = valuedcomponenti_cast<ClassDefinition*>(def);
        if (c) {
          Variable* var = new Variable(c, fC, signal->getNodeId(),
                                       InvalidNodeId, signal->getName());
          parentComponent->addVariable(var);
          return false;
        } else {
          def = nullptr;
        }
      }
      if (def == nullptr) {
        type = parentComponent->getDataType(interfName);
        if (type == nullptr) {
          if (!m_compileDesign->getCompiler()
                   ->getCommandLineParser()
                   ->fileunit()) {
            for (const auto& fC : m_compileDesign->getCompiler()
                                      ->getDesign()
                                      ->getAllFileContents()) {
              if (const DataType* dt1 = fC.second->getDataType(interfName)) {
                type = dt1;
                break;
              }
            }
          }
        }

        if (type) {
          const DataType* def = type->getActual();
          DataType::Category cat = def->getCategory();
          if (cat == DataType::Category::SIMPLE_TYPEDEF) {
            VObjectType t = def->getType();
            if (t == VObjectType::paIntVec_TypeLogic) {
              // Make "net types" explicit (vs variable types) for elab.
              signal->setType(VObjectType::paIntVec_TypeLogic);
            } else if (t == VObjectType::paIntVec_TypeReg) {
              signal->setType(VObjectType::paIntVec_TypeReg);
            } else if (t == VObjectType::paNetType_Wire) {
              signal->setType(VObjectType::paNetType_Wire);
            }
          } else if (cat == DataType::Category::REF) {
            // Should not arrive here, there should always be an actual
            // definition
          }
          signal->setDataType(type);
        }
      }
      if (def == nullptr) {
        if (parentComponent->getParameters()) {
          for (auto param : *parentComponent->getParameters()) {
            if (param->UhdmType() == uhdmtype_parameter) {
              if (param->VpiName() == interfName) {
                Parameter* p = parentComponent->getParameter(interfName);
                type = p;
                signal->setDataType(type);
                return true;
              }
            }
          }
        }
      }
      if (signal->getType() != VObjectType::slNoType) {
        return true;
      }
      if (def == nullptr) {
        while (instance) {
          for (Parameter* p : instance->getTypeParams()) {
            if (p->getName() == interfName) {
              type = p;
              signal->setDataType(type);
              return true;
            }
          }

          DesignComponent* component = instance->getDefinition();
          if (component) {
            if (component->getParameters()) {
              for (auto param : *component->getParameters()) {
                if (param->UhdmType() == uhdmtype_parameter) {
                  if (param->VpiName() == interfName) {
                    Parameter* p = component->getParameter(interfName);
                    type = p;
                    signal->setDataType(type);
                    return true;
                  }
                }
              }
            }
          }
          instance = instance->getParent();
        }
      }
      checkIfBuiltInTypeOrErrorOut(def, fC, id, type, interfName, errors,
                                   symbols);
      break;
    }
    default:
      break;
  }
  return true;
}

UHDM::expr* ElaborationStep::exprFromAssign_(DesignComponent* component,
                                             const FileContent* fC, NodeId id,
                                             NodeId unpackedDimension,
                                             ModuleInstance* instance) {
  // Assignment section
  NodeId assignment;
  NodeId Assign = fC->Sibling(id);
  if (Assign && (fC->Type(Assign) == VObjectType::paExpression)) {
    assignment = Assign;
  }
  if (unpackedDimension) {
    NodeId tmp = unpackedDimension;
    while ((fC->Type(tmp) == VObjectType::paUnpacked_dimension) ||
           (fC->Type(tmp) == VObjectType::paVariable_dimension)) {
      tmp = fC->Sibling(tmp);
    }
    if (tmp && (fC->Type(tmp) != VObjectType::paUnpacked_dimension) &&
        (fC->Type(tmp) != VObjectType::paVariable_dimension)) {
      assignment = tmp;
    }
  }

  NodeId expression;
  if (assignment) {
    if (fC->Type(assignment) == VObjectType::paClass_new) {
      expression = assignment;
    } else {
      NodeId Primary = fC->Child(assignment);
      if (fC->Type(assignment) == VObjectType::paExpression) {
        Primary = assignment;
      }
      expression = Primary;
    }
  } else {
    expression = fC->Sibling(id);
    if ((fC->Type(expression) != VObjectType::paExpression) &&
        (fC->Type(expression) != VObjectType::paConstant_expression))
      expression = InvalidNodeId;
  }

  expr* exp = nullptr;
  if (expression) {
    exp = (expr*)m_helper.compileExpression(component, fC, expression,
                                            m_compileDesign, Reduce::No,
                                            nullptr, instance);
  }
  return exp;
}

UHDM::typespec* ElaborationStep::elabTypeParameter_(DesignComponent* component,
                                                    Parameter* sit,
                                                    ModuleInstance* instance) {
  Serializer& s = m_compileDesign->getSerializer();
  UHDM::any* uparam = sit->getUhdmParam();
  UHDM::typespec* spec = nullptr;
  bool type_param = false;
  if (uparam->UhdmType() == uhdmtype_parameter) {
    if (ref_typespec* rt = ((type_parameter*)uparam)->Typespec())
      spec = rt->Actual_typespec();
    type_param = true;
  } else {
    if (ref_typespec* rt = ((parameter*)uparam)->Typespec())
      spec = rt->Actual_typespec();
  }

  const std::string_view pname = sit->getName();
  for (Parameter* param : instance->getTypeParams()) {
    // Param override
    if (param->getName() == pname) {
      UHDM::any* uparam = param->getUhdmParam();
      UHDM::typespec* override_spec = nullptr;
      if (uparam == nullptr) {
        if (type_param) {
          type_parameter* tp = s.MakeType_parameter();
          tp->VpiName(pname);
          param->setUhdmParam(tp);
        } else {
          parameter* tp = s.MakeParameter();
          tp->VpiName(pname);
          param->setUhdmParam(tp);
        }
        uparam = param->getUhdmParam();
      }

      if (type_param) {
        if (ref_typespec* rt = ((type_parameter*)uparam)->Typespec()) {
          override_spec = rt->Actual_typespec();
        }
      } else {
        if (ref_typespec* rt = ((parameter*)uparam)->Typespec()) {
          override_spec = rt->Actual_typespec();
        }
      }

      if (override_spec == nullptr) {
        ModuleInstance* parent = instance;
        if (ModuleInstance* pinst = instance->getParent()) parent = pinst;
        override_spec = m_helper.compileTypespec(
            component, param->getFileContent(), param->getNodeType(),
            m_compileDesign, Reduce::Yes, nullptr, parent, false);
      }

      if (override_spec) {
        if (type_param) {
          type_parameter* tparam = (type_parameter*)uparam;
          if (tparam->Typespec() == nullptr) {
            ref_typespec* override_specRef = s.MakeRef_typespec();
            override_specRef->VpiParent(tparam);
            tparam->Typespec(override_specRef);
          }
          tparam->Typespec()->Actual_typespec(override_spec);
        } else {
          parameter* tparam = (parameter*)uparam;
          if (tparam->Typespec() == nullptr) {
            ref_typespec* override_specRef = s.MakeRef_typespec();
            override_specRef->VpiParent(tparam);
            tparam->Typespec(override_specRef);
          }
          tparam->Typespec()->Actual_typespec(override_spec);
        }
        spec = override_spec;
        spec->VpiParent(uparam);
      }
      break;
    }
  }
  return spec;
}

any* ElaborationStep::makeVar_(DesignComponent* component, Signal* sig,
                               std::vector<UHDM::range*>* packedDimensions,
                               int32_t packedSize,
                               std::vector<UHDM::range*>* unpackedDimensions,
                               int32_t unpackedSize, ModuleInstance* instance,
                               UHDM::VectorOfvariables* vars,
                               UHDM::expr* assignExp, UHDM::typespec* tps) {
  Serializer& s = m_compileDesign->getSerializer();
  const DataType* dtype = sig->getDataType();
  VObjectType subnettype = sig->getType();

  const std::string_view signame = sig->getName();
  const FileContent* const fC = sig->getFileContent();

  variables* obj = nullptr;
  bool found = false;
  while (dtype) {
    if (const TypeDef* tdef = datatype_cast<const TypeDef*>(dtype)) {
      if (tdef->getTypespec()) {
        tps = tdef->getTypespec();
        found = false;
        break;
      }
    } else if (const Enum* en = datatype_cast<const Enum*>(dtype)) {
      if (en->getTypespec()) {
        enum_var* stv = s.MakeEnum_var();
        if (typespec* ts = en->getTypespec()) {
          ref_typespec* tsRef = s.MakeRef_typespec();
          tsRef->VpiParent(stv);
          tsRef->Actual_typespec(ts);
          stv->Typespec(tsRef);
        }
        if (assignExp != nullptr) {
          stv->Expr(assignExp);
          assignExp->VpiParent(stv);
        }
        obj = stv;
        found = true;
        break;
      }
    } else if (const Struct* st = datatype_cast<const Struct*>(dtype)) {
      if (st->getTypespec()) {
        struct_var* stv = s.MakeStruct_var();
        if (typespec* ts = st->getTypespec()) {
          ref_typespec* tsRef = s.MakeRef_typespec();
          tsRef->VpiParent(stv);
          tsRef->Actual_typespec(ts);
          stv->Typespec(tsRef);
        }
        if (assignExp != nullptr) {
          stv->Expr(assignExp);
          assignExp->VpiParent(stv);
        }
        obj = stv;
        found = true;
        break;
      }
    } else if (const Union* un = datatype_cast<const Union*>(dtype)) {
      if (un->getTypespec()) {
        union_var* stv = s.MakeUnion_var();
        if (typespec* ts = un->getTypespec()) {
          ref_typespec* tsRef = s.MakeRef_typespec();
          tsRef->VpiParent(stv);
          tsRef->Actual_typespec(ts);
          stv->Typespec(tsRef);
        }
        if (assignExp != nullptr) {
          stv->Expr(assignExp);
          assignExp->VpiParent(stv);
        }
        obj = stv;
        found = true;
        break;
      }
    } else if (const DummyType* un = datatype_cast<const DummyType*>(dtype)) {
      typespec* tps = un->getTypespec();
      if (tps == nullptr) {
        tps = m_helper.compileTypespec(component, un->getFileContent(),
                                       un->getNodeId(), m_compileDesign,
                                       Reduce::Yes, nullptr, instance, true);
        ((DummyType*)un)->setTypespec(tps);
      }
      variables* var = nullptr;
      UHDM_OBJECT_TYPE ttps = tps->UhdmType();
      if (ttps == uhdmenum_typespec) {
        var = s.MakeEnum_var();
      } else if (ttps == uhdmstruct_typespec) {
        var = s.MakeStruct_var();
      } else if (ttps == uhdmunion_typespec) {
        var = s.MakeUnion_var();
      } else if (ttps == uhdmpacked_array_typespec) {
        packed_array_var* avar = s.MakePacked_array_var();
        auto elems = s.MakeAnyVec();
        avar->Elements(elems);
        var = avar;
      } else if (ttps == uhdmarray_typespec) {
        UHDM::array_var* array_var = s.MakeArray_var();
        ref_typespec* tmpRef = s.MakeRef_typespec();
        tmpRef->VpiParent(array_var);
        tmpRef->Actual_typespec(s.MakeArray_typespec());
        array_var->Typespec(tmpRef);
        array_var->VpiArrayType(vpiStaticArray);
        array_var->VpiRandType(vpiNotRand);
        var = array_var;
      } else if (ttps == uhdmint_typespec) {
        var = s.MakeInt_var();
      } else if (ttps == uhdminteger_typespec) {
        var = s.MakeInteger_var();
      } else if (ttps == uhdmbyte_typespec) {
        var = s.MakeByte_var();
      } else if (ttps == uhdmbit_typespec) {
        var = s.MakeBit_var();
      } else if (ttps == uhdmshort_int_typespec) {
        var = s.MakeShort_int_var();
      } else if (ttps == uhdmlong_int_typespec) {
        var = s.MakeLong_int_var();
      } else if (ttps == uhdmstring_typespec) {
        var = s.MakeString_var();
      } else if (ttps == uhdmlogic_typespec) {
        logic_typespec* ltps = (logic_typespec*)tps;
        logic_var* avar = s.MakeLogic_var();
        avar->Ranges(ltps->Ranges());
        var = avar;
      } else {
        var = s.MakeLogic_var();
      }
      var->VpiName(signame);
      if (var->Typespec() == nullptr) {
        ref_typespec* tpsRef = s.MakeRef_typespec();
        tpsRef->VpiParent(var);
        var->Typespec(tpsRef);
      }
      var->Typespec()->Actual_typespec(tps);
      if (assignExp != nullptr) {
        var->Expr(assignExp);
        assignExp->VpiParent(var);
      }
      obj = var;
      found = true;
      break;
    } else if (const SimpleType* sit =
                   datatype_cast<const SimpleType*>(dtype)) {
      UHDM::typespec* spec = sit->getTypespec();
      spec = m_helper.elabTypespec(component, spec, m_compileDesign, nullptr,
                                   instance);
      variables* var = m_helper.getSimpleVarFromTypespec(spec, packedDimensions,
                                                         m_compileDesign);
      var->VpiConstantVariable(sig->isConst());
      var->VpiSigned(sig->isSigned());
      var->VpiName(signame);
      if (var->Typespec() == nullptr) {
        ref_typespec* specRef = s.MakeRef_typespec();
        specRef->VpiParent(var);
        var->Typespec(specRef);
      }
      var->Typespec()->Actual_typespec(spec);
      if (assignExp != nullptr) {
        var->Expr(assignExp);
        assignExp->VpiParent(var);
      }
      obj = var;
      found = true;
      break;
    } else if (/*const ClassDefinition* cl = */ datatype_cast<
               const ClassDefinition*>(dtype)) {
      class_var* stv = s.MakeClass_var();
      ref_typespec* tpsRef = s.MakeRef_typespec();
      tpsRef->VpiParent(stv);
      tpsRef->Actual_typespec(tps);
      stv->Typespec(tpsRef);
      if (assignExp != nullptr) {
        stv->Expr(assignExp);
        assignExp->VpiParent(stv);
      }
      obj = stv;
      found = true;
      break;
    } else if (Parameter* sit = const_cast<Parameter*>(
                   datatype_cast<const Parameter*>(dtype))) {
      if (UHDM::typespec* spec = elabTypeParameter_(component, sit, instance)) {
        if (variables* var = m_helper.getSimpleVarFromTypespec(
                spec, packedDimensions, m_compileDesign)) {
          var->VpiConstantVariable(sig->isConst());
          var->VpiSigned(sig->isSigned());
          var->VpiName(signame);
          if (assignExp != nullptr) {
            var->Expr(assignExp);
            assignExp->VpiParent(var);
          }
          obj = var;
          found = true;
          break;
        }
      }
    }
    dtype = dtype->getDefinition();
  }

  if ((found == false) && tps) {
    UHDM::UHDM_OBJECT_TYPE tpstype = tps->UhdmType();
    if (tpstype == uhdmstruct_typespec) {
      struct_var* stv = s.MakeStruct_var();
      obj = stv;
    } else if (tpstype == uhdmlogic_typespec) {
      logic_var* stv = s.MakeLogic_var();
      // Do not set packedDimensions, it is a repeat of the typespec packed
      // dimension.
      // stv->Ranges(packedDimensions);
      obj = stv;
    } else if (tpstype == uhdmenum_typespec) {
      enum_var* stv = s.MakeEnum_var();
      obj = stv;
    } else if (tpstype == uhdmbit_typespec) {
      bit_var* stv = s.MakeBit_var();
      stv->Ranges(unpackedDimensions);
      obj = stv;
    } else if (tpstype == uhdmbyte_typespec) {
      byte_var* stv = s.MakeByte_var();
      obj = stv;
    } else if (tpstype == uhdmreal_typespec) {
      real_var* stv = s.MakeReal_var();
      obj = stv;
    } else if (tpstype == uhdmint_typespec) {
      int_var* stv = s.MakeInt_var();
      obj = stv;
    } else if (tpstype == uhdminteger_typespec) {
      integer_var* stv = s.MakeInteger_var();
      obj = stv;
    } else if (tpstype == uhdmlong_int_typespec) {
      long_int_var* stv = s.MakeLong_int_var();
      obj = stv;
    } else if (tpstype == uhdmshort_int_typespec) {
      short_int_var* stv = s.MakeShort_int_var();
      obj = stv;
    } else if (tpstype == uhdmstring_typespec) {
      string_var* stv = s.MakeString_var();
      obj = stv;
    } else if (tpstype == uhdmbit_typespec) {
      bit_var* stv = s.MakeBit_var();
      obj = stv;
    } else if (tpstype == uhdmbyte_typespec) {
      byte_var* stv = s.MakeByte_var();
      obj = stv;
    } else if (tpstype == uhdmtime_typespec) {
      time_var* stv = s.MakeTime_var();
      obj = stv;
    } else if (tpstype == uhdmunion_typespec) {
      union_var* stv = s.MakeUnion_var();
      obj = stv;
    } else if (tpstype == uhdmclass_typespec) {
      class_var* stv = s.MakeClass_var();
      obj = stv;
    } else if (tpstype == uhdmpacked_array_typespec) {
      packed_array_var* stv = s.MakePacked_array_var();
      obj = stv;
    } else if (tpstype == uhdmarray_typespec) {
      UHDM::array_var* stv = s.MakeArray_var();
      obj = stv;
    }

    if (obj != nullptr) {
      if (assignExp != nullptr) {
        assignExp->VpiParent(obj);
        obj->Expr(assignExp);
      }
      if (tps != nullptr) {
        if (obj->Typespec() == nullptr) {
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(obj);
          obj->Typespec(rt);
        }
        obj->Typespec()->Actual_typespec(tps);
        tps->VpiParent(obj);
      }
      obj->VpiName(signame);
    }
  }

  if (obj == nullptr) {
    variables* var = nullptr;
    if (subnettype == VObjectType::paIntegerAtomType_Shortint) {
      UHDM::short_int_var* int_var = s.MakeShort_int_var();
      var = int_var;
      tps = s.MakeShort_int_typespec();
      ref_typespec* tpsRef = s.MakeRef_typespec();
      tpsRef->VpiParent(int_var);
      tpsRef->Actual_typespec(tps);
      int_var->Typespec(tpsRef);
    } else if (subnettype == VObjectType::paIntegerAtomType_Int) {
      UHDM::int_var* int_var = s.MakeInt_var();
      var = int_var;
      tps = s.MakeInt_typespec();
      ref_typespec* tpsRef = s.MakeRef_typespec();
      tpsRef->VpiParent(int_var);
      tpsRef->Actual_typespec(tps);
      int_var->Typespec(tpsRef);
    } else if (subnettype == VObjectType::paIntegerAtomType_Integer) {
      UHDM::integer_var* int_var = s.MakeInteger_var();
      var = int_var;
      tps = s.MakeInteger_typespec();
      ref_typespec* tpsRef = s.MakeRef_typespec();
      tpsRef->VpiParent(int_var);
      tpsRef->Actual_typespec(tps);
      int_var->Typespec(tpsRef);
    } else if (subnettype == VObjectType::paIntegerAtomType_LongInt) {
      UHDM::long_int_var* int_var = s.MakeLong_int_var();
      var = int_var;
      tps = s.MakeLong_int_typespec();
      ref_typespec* tpsRef = s.MakeRef_typespec();
      tpsRef->VpiParent(int_var);
      tpsRef->Actual_typespec(tps);
      int_var->Typespec(tpsRef);
    } else if (subnettype == VObjectType::paIntegerAtomType_Time) {
      UHDM::time_var* int_var = s.MakeTime_var();
      var = int_var;
    } else if (subnettype == VObjectType::paIntVec_TypeBit) {
      UHDM::bit_var* int_var = s.MakeBit_var();
      bit_typespec* btps = s.MakeBit_typespec();
      btps->Ranges(packedDimensions);
      tps = btps;
      ref_typespec* tpsRef = s.MakeRef_typespec();
      tpsRef->VpiParent(int_var);
      tpsRef->Actual_typespec(tps);
      int_var->Typespec(tpsRef);
      int_var->Ranges(packedDimensions);
      var = int_var;
    } else if (subnettype == VObjectType::paIntegerAtomType_Byte) {
      UHDM::byte_var* int_var = s.MakeByte_var();
      byte_typespec* btps = s.MakeByte_typespec();
      tps = btps;
      ref_typespec* tpsRef = s.MakeRef_typespec();
      tpsRef->VpiParent(int_var);
      tpsRef->Actual_typespec(tps);
      int_var->Typespec(tpsRef);
      var = int_var;
    } else if (subnettype == VObjectType::paNonIntType_ShortReal) {
      UHDM::short_real_var* int_var = s.MakeShort_real_var();
      var = int_var;
    } else if (subnettype == VObjectType::paNonIntType_Real) {
      UHDM::real_var* int_var = s.MakeReal_var();
      var = int_var;
    } else if (subnettype == VObjectType::paNonIntType_RealTime) {
      UHDM::time_var* int_var = s.MakeTime_var();
      var = int_var;
    } else if (subnettype == VObjectType::paString_type) {
      UHDM::string_var* int_var = s.MakeString_var();
      var = int_var;
    } else if (subnettype == VObjectType::paChandle_type) {
      UHDM::chandle_var* chandle_var = s.MakeChandle_var();
      var = chandle_var;
    } else if (subnettype == VObjectType::paIntVec_TypeLogic) {
      logic_var* logicv = s.MakeLogic_var();
      logicv->Ranges(packedDimensions);
      logic_typespec* ltps = s.MakeLogic_typespec();
      ltps->Ranges(packedDimensions);
      NodeId id;
      if (sig->getPackedDimension()) id = fC->Parent(sig->getPackedDimension());
      if (!id) id = sig->getNodeId();
      if (id) {
        fC->populateCoreMembers(id, id, ltps);
      }
      tps = ltps;
      ref_typespec* tpsRef = s.MakeRef_typespec();
      tpsRef->VpiParent(logicv);
      tpsRef->Actual_typespec(tps);
      logicv->Typespec(tpsRef);
      var = logicv;
    } else if (subnettype == VObjectType::paEvent_type) {
      named_event* event = s.MakeNamed_event();
      event->VpiName(signame);
      if (instance) {
        Netlist* netlist = instance->getNetlist();
        VectorOfnamed_event* events = netlist->named_events();
        if (events == nullptr) {
          netlist->named_events(s.MakeNamed_eventVec());
          events = netlist->named_events();
        }
        events->push_back(event);
      }
      return event;
    } else {
      // default type (fallback)
      logic_var* logicv = s.MakeLogic_var();
      logicv->Ranges(packedDimensions);
      var = logicv;
    }
    var->VpiSigned(sig->isSigned());
    var->VpiConstantVariable(sig->isConst());
    var->VpiName(signame);
    var->Expr(assignExp);
    obj = var;
  } else if (packedDimensions && (obj->UhdmType() != uhdmlogic_var) &&
             (obj->UhdmType() != uhdmbit_var) &&
             (obj->UhdmType() != uhdmpacked_array_var)) {
    // packed struct array ...
    UHDM::packed_array_var* parray = s.MakePacked_array_var();
    parray->Ranges(packedDimensions);
    VectorOfany* elements = s.MakeAnyVec();
    elements->push_back(obj);
    parray->Elements(elements);
    obj->VpiParent(parray);
    parray->VpiName(signame);
    obj = parray;
  }

  if (unpackedDimensions) {
    array_var* array_var = s.MakeArray_var();
    array_var->Variables(s.MakeVariablesVec());
    bool dynamic = false;
    bool associative = false;
    bool queue = false;
    int32_t index = 0;
    for (auto itr = unpackedDimensions->begin();
         itr != unpackedDimensions->end(); itr++) {
      range* r = *itr;
      const expr* rhs = r->Right_expr();
      if (rhs->UhdmType() == uhdmconstant) {
        const std::string_view value = rhs->VpiValue();
        if (value == "STRING:$") {
          queue = true;
          unpackedDimensions->erase(itr);
          break;
        } else if (value == "STRING:associative") {
          associative = true;
          const typespec* tp = nullptr;
          if (const ref_typespec* rt = rhs->Typespec()) {
            tp = rt->Actual_typespec();
          }
          array_typespec* taps = s.MakeArray_typespec();
          ref_typespec* tpRef = s.MakeRef_typespec();
          tpRef->VpiParent(taps);
          tpRef->Actual_typespec(const_cast<UHDM::typespec*>(tp));
          taps->Index_typespec(tpRef);

          ref_typespec* taps_ref = s.MakeRef_typespec();
          taps_ref->VpiParent(array_var);
          taps_ref->Actual_typespec(taps);
          array_var->Typespec(taps_ref);
          unpackedDimensions->erase(itr);
          break;
        } else if (value == "STRING:unsized") {
          dynamic = true;
          unpackedDimensions->erase(itr);
          break;
        }
      }
      index++;
    }

    if (associative || queue || dynamic) {
      if (!unpackedDimensions->empty()) {
        if (index == 0) {
          array_var->Ranges(unpackedDimensions);
        } else {
          array_typespec* tps = s.MakeArray_typespec();
          ref_typespec* tpsRef = s.MakeRef_typespec();
          tpsRef->VpiParent(array_var);
          tpsRef->Actual_typespec(tps);
          array_var->Typespec(tpsRef);

          if (associative)
            tps->VpiArrayType(vpiAssocArray);
          else if (queue)
            tps->VpiArrayType(vpiQueueArray);
          else if (dynamic)
            tps->VpiArrayType(vpiDynamicArray);
          else
            tps->VpiArrayType(vpiStaticArray);
          array_typespec* subtps = s.MakeArray_typespec();
          tpsRef = s.MakeRef_typespec();
          tpsRef->VpiParent(tps);
          tpsRef->Actual_typespec(subtps);
          tps->Elem_typespec(tpsRef);

          subtps->Ranges(unpackedDimensions);
          switch (obj->UhdmType()) {
            case uhdmint_var: {
              int_typespec* ts = s.MakeInt_typespec();
              tpsRef = s.MakeRef_typespec();
              tpsRef->VpiParent(subtps);
              tpsRef->Actual_typespec(ts);
              subtps->Elem_typespec(tpsRef);
              break;
            }
            case uhdminteger_var: {
              integer_typespec* ts = s.MakeInteger_typespec();
              tpsRef = s.MakeRef_typespec();
              tpsRef->VpiParent(subtps);
              tpsRef->Actual_typespec(ts);
              subtps->Elem_typespec(tpsRef);
              break;
            }
            case uhdmlogic_var: {
              logic_typespec* ts = s.MakeLogic_typespec();
              tpsRef = s.MakeRef_typespec();
              tpsRef->VpiParent(subtps);
              tpsRef->Actual_typespec(ts);
              subtps->Elem_typespec(tpsRef);
              break;
            }
            case uhdmlong_int_var: {
              long_int_typespec* ts = s.MakeLong_int_typespec();
              tpsRef = s.MakeRef_typespec();
              tpsRef->VpiParent(subtps);
              tpsRef->Actual_typespec(ts);
              subtps->Elem_typespec(tpsRef);
              break;
            }
            case uhdmshort_int_var: {
              short_int_typespec* ts = s.MakeShort_int_typespec();
              tpsRef = s.MakeRef_typespec();
              tpsRef->VpiParent(subtps);
              tpsRef->Actual_typespec(ts);
              subtps->Elem_typespec(tpsRef);
              break;
            }
            case uhdmbyte_var: {
              byte_typespec* ts = s.MakeByte_typespec();
              tpsRef = s.MakeRef_typespec();
              tpsRef->VpiParent(subtps);
              tpsRef->Actual_typespec(ts);
              subtps->Elem_typespec(tpsRef);
              break;
            }
            case uhdmbit_var: {
              bit_typespec* ts = s.MakeBit_typespec();
              tpsRef = s.MakeRef_typespec();
              tpsRef->VpiParent(subtps);
              tpsRef->Actual_typespec(ts);
              subtps->Elem_typespec(tpsRef);
              break;
            }
            case uhdmstring_var: {
              string_typespec* ts = s.MakeString_typespec();
              tpsRef = s.MakeRef_typespec();
              tpsRef->VpiParent(subtps);
              tpsRef->Actual_typespec(ts);
              subtps->Elem_typespec(tpsRef);
              break;
            }
            default: {
              unsupported_typespec* ts = s.MakeUnsupported_typespec();
              tpsRef = s.MakeRef_typespec();
              tpsRef->VpiParent(subtps);
              tpsRef->Actual_typespec(ts);
              subtps->Elem_typespec(tpsRef);
              break;
            }
          }
        }
      }
    }

    if (associative) {
      array_var->VpiArrayType(vpiAssocArray);
    } else if (queue) {
      array_var->VpiArrayType(vpiQueueArray);
    } else if (dynamic) {
      array_var->VpiArrayType(vpiDynamicArray);
    } else {
      array_var->Ranges(unpackedDimensions);
      array_var->VpiArrayType(vpiStaticArray);
    }
    array_var->VpiSize(unpackedSize);
    array_var->VpiName(signame);
    array_var->VpiRandType(vpiNotRand);
    array_var->VpiVisibility(vpiPublicVis);
    fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), array_var);
    vars->push_back(array_var);
    obj->VpiParent(array_var);
    if ((array_var->Typespec() == nullptr) || associative) {
      VectorOfvariables* array_vars = array_var->Variables();
      array_vars->push_back(obj);
      (obj)->VpiName("");
    }
    if (array_var->Typespec() == nullptr) {
      ref_typespec* tsRef = s.MakeRef_typespec();
      tsRef->VpiParent(array_var);
      tsRef->Actual_typespec(s.MakeArray_typespec());
      array_var->Typespec(tsRef);
    }
    array_var->Expr(assignExp);
    fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), obj);
    obj = array_var;
  } else {
    if (obj->UhdmType() == uhdmenum_var) {
      ((enum_var*)obj)->VpiName(signame);
    } else if (obj->UhdmType() == uhdmstruct_var) {
      ((struct_var*)obj)->VpiName(signame);
    } else if (obj->UhdmType() == uhdmunion_var) {
      ((union_var*)obj)->VpiName(signame);
    } else if (obj->UhdmType() == uhdmclass_var) {
      ((class_var*)obj)->VpiName(signame);
    } else if (obj->UhdmType() == uhdmlogic_var) {
      ((logic_var*)obj)->VpiName(signame);
    }
    vars->push_back(obj);
  }

  if (assignExp) {
    if (assignExp->UhdmType() == uhdmconstant) {
      m_helper.adjustSize(tps, component, m_compileDesign, instance,
                          (constant*)assignExp);
    } else if (assignExp->UhdmType() == uhdmoperation) {
      operation* op = (operation*)assignExp;
      int32_t opType = op->VpiOpType();
      const typespec* tp = tps;
      if (opType == vpiAssignmentPatternOp) {
        if (tp->UhdmType() == uhdmpacked_array_typespec) {
          packed_array_typespec* ptp = (packed_array_typespec*)tp;
          if (const ref_typespec* ert = ptp->Elem_typespec()) {
            tp = ert->Actual_typespec();
          }
          if (tp == nullptr) tp = tps;
        }
      }
      for (auto oper : *op->Operands()) {
        if (oper->UhdmType() == uhdmconstant)
          m_helper.adjustSize(tp, component, m_compileDesign, instance,
                              (constant*)oper, false, true);
      }
    }
  }

  if (obj) {
    if (packedDimensions != nullptr) {
      for (auto r : *packedDimensions) r->VpiParent(obj);
    }
    if (unpackedDimensions != nullptr) {
      for (auto r : *unpackedDimensions) r->VpiParent(obj);
    }

    UHDM::ExprEval eval;
    obj->Expr(eval.flattenPatternAssignments(s, tps, assignExp));
    obj->VpiSigned(sig->isSigned());
    obj->VpiConstantVariable(sig->isConst());
    obj->VpiIsRandomized(sig->isRand() || sig->isRandc());
    if (sig->isRand())
      obj->VpiRandType(vpiRand);
    else if (sig->isRandc())
      obj->VpiRandType(vpiRandC);
    if (sig->isStatic()) {
      obj->VpiAutomatic(false);
    } else {
      obj->VpiAutomatic(true);
    }
    if (sig->isProtected()) {
      obj->VpiVisibility(vpiProtectedVis);
    } else if (sig->isLocal()) {
      obj->VpiVisibility(vpiLocalVis);
    } else {
      obj->VpiVisibility(vpiPublicVis);
    }
  }
  return obj;
}
}  // namespace SURELOG
