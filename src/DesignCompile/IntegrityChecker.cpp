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
 * File:   IntegrityChecker.cpp
 * Author: hs
 *
 * Created on August 10, 2024, 00:00 AM
 */

#include <Surelog/Common/FileSystem.h>
#include <Surelog/Common/Session.h>
#include <Surelog/DesignCompile/IntegrityChecker.h>
#include <Surelog/ErrorReporting/ErrorContainer.h>
#include <Surelog/SourceCompile/SymbolTable.h>
#include <Surelog/Utils/StringUtils.h>

// uhdm
#include <uhdm/uhdm.h>

namespace SURELOG {
IntegrityChecker::IntegrityChecker(Session* session)
    : m_session(session),
      m_acceptedUhdmTypesWithInvalidLocation({
          uhdm::UhdmType::Design,
          uhdm::UhdmType::SourceFile,
          uhdm::UhdmType::PreprocMacroDefinition,
          uhdm::UhdmType::PreprocMacroInstance,
      }) {}

static std::string asSymbol(const uhdm::Any* object) {
  return StrCat(object->getUhdmId(), ", ",
                uhdm::UhdmName(object->getUhdmType()), ", ", object->getName());
}

std::string_view IntegrityChecker::toString(LineColumnRelation relation) const {
  switch (relation) {
    case LineColumnRelation::Before:
      return "Before";
    case LineColumnRelation::Inside:
      return "Inside";
    case LineColumnRelation::After:
      return "After";
    case LineColumnRelation::Inconclusive:
      return "Inconclusive";
  }
  return "VeryBad";
}

bool IntegrityChecker::isBuiltInPackageOnStack(const uhdm::Any* object) const {
  static constexpr std::string_view kBuiltIn{"builtin"};
  return ((object->getUhdmType() == uhdm::UhdmType::Package) &&
          (object->getName() == kBuiltIn)) ||
         std::find_if(
             m_callstack.crbegin(), m_callstack.crend(),
             [](const uhdm::Any* const object) {
               return (object->getUhdmType() == uhdm::UhdmType::Package) &&
                      (object->getName() == kBuiltIn);
             }) != m_callstack.rend();
}

bool IntegrityChecker::isUVMMember(const uhdm::Any* object) const {
  std::string_view filepath = object->getFile();
  return (filepath.find("\\uvm_") != std::string_view::npos) ||
         (filepath.find("/uvm_") != std::string_view::npos) ||
         (filepath.find("\\ovm_") != std::string_view::npos) ||
         (filepath.find("/ovm_") != std::string_view::npos);
}

template <typename T>
void IntegrityChecker::reportDuplicates(const uhdm::Any* object,
                                        const std::vector<T*>& collection,
                                        uint32_t vpiRelation) const {
  if (isUVMMember(object)) return;

  const std::set<T*> unique(collection.cbegin(), collection.cend());
  if (unique.size() != collection.size()) {
    SymbolTable* const symbolTable = m_session->getSymbolTable();
    FileSystem* const fileSystem = m_session->getFileSystem();
    ErrorContainer* const errorContainer = m_session->getErrorContainer();

    Location loc(fileSystem->toPathId(object->getFile(), symbolTable),
                 object->getStartLine(), object->getStartColumn(),
                 symbolTable->registerSymbol(asSymbol(object)));
    errorContainer->addError(
        ErrorDefinition::INTEGRITY_CHECK_COLLECTION_HAS_DUPLICATES, loc);
  }
}

inline IntegrityChecker::LineColumnRelation
IntegrityChecker::getLineColumnRelation(uint32_t sl, uint16_t sc, uint32_t el,
                                        uint16_t ec) const {
  if (sl == el) {
    if (sc < ec) return LineColumnRelation::Before;
    if (sc == ec) return LineColumnRelation::Inside;
    if (sc > ec) return LineColumnRelation::After;
  }

  return (sl < el) ? LineColumnRelation::Before : LineColumnRelation::After;
}

inline IntegrityChecker::LineColumnRelation
IntegrityChecker::getLineColumnRelation(uint32_t l, uint16_t c, uint32_t sl,
                                        uint16_t sc, uint32_t el,
                                        uint16_t ec) const {
  if (l < sl) return LineColumnRelation::Before;
  if (l > el) return LineColumnRelation::After;

  if ((l == sl) && (c < sc)) return LineColumnRelation::Before;
  if ((l == el) && (c > ec)) return LineColumnRelation::After;

  return LineColumnRelation::Inside;
}

inline IntegrityChecker::LineColumnRelation
IntegrityChecker::getLineColumnRelation(uint32_t csl, uint16_t csc,
                                        uint32_t cel, uint16_t cec,
                                        uint32_t psl, uint16_t psc,
                                        uint32_t pel, uint16_t pec) const {
  if (cel < psl) return LineColumnRelation::Before;
  if (csl > pel) return LineColumnRelation::After;

  if ((csl == pel) && (csc >= pec)) return LineColumnRelation::After;
  if ((cel == psl) && (cec <= psc)) return LineColumnRelation::Before;

  const bool startIsInside = (csl > psl) || ((csl == psl) && (csc >= psc));
  const bool endIsInside = (cel < pel) || ((cel == pel) && (cec <= pec));
  if (startIsInside && endIsInside) return LineColumnRelation::Inside;

  return LineColumnRelation::Inconclusive;
}

std::set<const uhdm::PreprocMacroInstance*> IntegrityChecker::getMacroInstances(
    const uhdm::Any* object) const {
  std::pair<any_macro_instance_map_t::const_iterator,
            any_macro_instance_map_t::const_iterator>
      bounds = m_anyMacroInstance.equal_range(object);
  std::set<const uhdm::PreprocMacroInstance*> pmis;
  std::transform(bounds.first, bounds.second, std::inserter(pmis, pmis.end()),
                 [](any_macro_instance_map_t::const_reference& entry) {
                   return entry.second;
                 });
  return pmis;
}

void IntegrityChecker::reportInvalidLocation(const uhdm::Any* object) const {
  if ((object->getStartLine() == 0) && (object->getEndLine() == 0) &&
      (object->getStartColumn() == 0) && (object->getEndColumn() == 0))
    return;

  const uhdm::Any* const parent = object->getParent();
  if (parent == nullptr) return;
  if (parent->getUhdmType() == uhdm::UhdmType::Design) return;

  if ((parent->getStartLine() == 0) && (parent->getEndLine() == 0) &&
      (parent->getStartColumn() == 0) && (parent->getEndColumn() == 0))
    return;

  if (m_acceptedUhdmTypesWithInvalidLocation.find(object->getUhdmType()) !=
      m_acceptedUhdmTypesWithInvalidLocation.cend())
    return;

  // There are cases where things can be different files. e.g. PreprocTest
  if (object->getFile() != parent->getFile()) return;

  // Task body can be outside of the class definition itself!
  if ((object->getUhdmType() == uhdm::UhdmType::Task) &&
      (parent->getUhdmType() == uhdm::UhdmType::ClassDefn))
    return;

  // Function body can be outside of the class definition itself!
  if ((object->getUhdmType() == uhdm::UhdmType::Function) &&
      (parent->getUhdmType() == uhdm::UhdmType::ClassDefn))
    return;

  // Function begin is implicit!
  if ((object->getUhdmType() == uhdm::UhdmType::Begin) &&
      (parent->getUhdmType() == uhdm::UhdmType::Function))
    return;

  // REVISIT(HS): Temporarily ignore some issues
  const uhdm::Any* p = object;
  while (p != nullptr) {
    if ((p->getUhdmType() == uhdm::UhdmType::BitSelect) ||
        (p->getUhdmType() == uhdm::UhdmType::HierPath)) {
      return;
    }
    p = p->getParent();
  }

  SymbolTable* const symbolTable = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errorContainer = m_session->getErrorContainer();

  const uint32_t csl = object->getStartLine();
  const uint32_t csc = object->getStartColumn();
  const uint32_t cel = object->getEndLine();
  const uint32_t cec = object->getEndColumn();

  LineColumnRelation actualRelation = getLineColumnRelation(csl, csc, cel, cec);
  if ((actualRelation != LineColumnRelation::Before) &&
      (actualRelation != LineColumnRelation::Inside)) {
    Location loc(fileSystem->toPathId(object->getFile(), symbolTable),
                 object->getStartLine(), object->getStartColumn(),
                 symbolTable->registerSymbol(asSymbol(object)));
    errorContainer->addError(ErrorDefinition::INTEGRITY_CHECK_INVALID_LOCATION,
                             loc);
    return;
  }

  const uint32_t psl = parent->getStartLine();
  const uint32_t psc = parent->getStartColumn();
  const uint32_t pel = parent->getEndLine();
  const uint32_t pec = parent->getEndColumn();

  actualRelation = getLineColumnRelation(psl, psc, pel, pec);
  if ((actualRelation != LineColumnRelation::Before) &&
      (actualRelation != LineColumnRelation::Inside))
    // If parent location is known to be bad, don't bother reporting issues
    // with the child. Parent is already reported and so when the parent
    // gets fixed, the child becomes important.
    return;

  actualRelation =
      getLineColumnRelation(csl, csc, cel, cec, psl, psc, pel, pec);

  LineColumnRelation expectedRelation = LineColumnRelation::Inside;
  if (const uhdm::RefTypespec* const objectAsRefTypespec =
          object->Cast<uhdm::RefTypespec>()) {
    if (objectAsRefTypespec->getActual<uhdm::UnsupportedTypespec>() !=
        nullptr) {
      // Ignore issues with UnsupportedTypespec.
      // There are known issues with genvar not followed with a type.
      return;
    }

    if ((parent->Cast<uhdm::Extends>() != nullptr) ||
        (parent->Cast<uhdm::TFCall>() != nullptr)) {
      expectedRelation = LineColumnRelation::Inside;
    } else if (parent->Cast<uhdm::TypeParameter>() != nullptr) {
      expectedRelation = LineColumnRelation::After;
    } else {
      expectedRelation = LineColumnRelation::Before;
    }

    if (const uhdm::EnumTypespec* const parentAsEnumTypespec =
            parent->Cast<uhdm::EnumTypespec>()) {
      if (parentAsEnumTypespec->getBaseTypespec() == object) {
        // typedef enum <base_type> { ... }
        expectedRelation = LineColumnRelation::Inside;
      }
    } else if (const uhdm::TaggedPattern* const parentAsTaggedPattern =
                   parent->Cast<uhdm::TaggedPattern>()) {
      if (parentAsTaggedPattern->getTypespec() == object) {
        // BlahBlab: constant|operation
        expectedRelation = LineColumnRelation::Inside;
      }
    } else if (const uhdm::PackedArrayTypespec* const
                   parentAsPackedArrayTypespec =
                       parent->Cast<uhdm::PackedArrayTypespec>()) {
      if (parentAsPackedArrayTypespec->getElemTypespec() == object) {
        // elem_type [0:n] var_name
        expectedRelation = LineColumnRelation::Before;
      }
    } else if (const uhdm::ArrayVar* const parentAsArrayVar =
                   parent->Cast<uhdm::ArrayVar>()) {
      if (parentAsArrayVar->getTypespec() == object) {
        // elem_type var_name[range]
        // For arrayVar/Typespec, the range is the location
        if (parentAsArrayVar->getArrayType() == vpiQueueArray) {
          // In the case of declaration, i.e. <type> <var_name[$] it is 'After'
          // In the case of assignment to empty queue, it is overlapping i.e
          //    <var_name> = {}
          expectedRelation =
              ((csl == psl) && (csc == psc) && (cel == pel) && (cec == pec))
                  ? LineColumnRelation::Inside
                  : LineColumnRelation::After;
        } else {
          // <var_name> <ranges> = ....
          // ArrayVar::typespec refers to the ranges
          expectedRelation = LineColumnRelation::After;
        }
      }
    } else if (const uhdm::ArrayTypespec* const parentAsArrayTypespec =
                   parent->Cast<uhdm::ArrayTypespec>()) {
      if (parentAsArrayTypespec->getIndexTypespec() == object) {
        // Since array_typspec refers to the range, index is basically the
        // range in case of associative arrays, queues, and dynamic arrays.
        expectedRelation = LineColumnRelation::After;
      } else if (parentAsArrayTypespec->getElemTypespec() == object) {
        expectedRelation = LineColumnRelation::Before;
      }
    } else if (const uhdm::IODecl* const parentAsIODecl =
                   parent->Cast<uhdm::IODecl>()) {
      if (parentAsIODecl->getTypespec() == object) {
        // In old verilog style, the parameter declaration is different!
        // task MYHDL3_adv;
        //   input width;
        //   integer width;
        // begin: MYHDL82_RETURN
        // end
        if (actualRelation == LineColumnRelation::After)
          expectedRelation = LineColumnRelation::After;
      }
    } else if (const uhdm::Variables* const parentAsVariables =
                   parent->Cast<uhdm::Variables>()) {
      expectedRelation = LineColumnRelation::Before;
    }
  } else if (const uhdm::RefObj* const objAsRefObj =
                 any_cast<uhdm::RefObj>(object)) {
    if (const uhdm::BitSelect* const parentAsBitSelect =
            any_cast<uhdm::BitSelect>(parent)) {
      if (parentAsBitSelect->getIndex() == object) {
        expectedRelation = LineColumnRelation::After;
      }
    }
  } else if (object->getUhdmType() == uhdm::UhdmType::Range) {
    if (const uhdm::ArrayTypespec* const parentAsArrayTypespec =
            parent->Cast<uhdm::ArrayTypespec>()) {
      if (!parentAsArrayTypespec->getName().empty() &&
          (parentAsArrayTypespec->getName() != SymbolTable::getBadSymbol())) {
        // typedef int var_name[range];
        expectedRelation = LineColumnRelation::After;
      }
    } else if (parent->Cast<uhdm::IODecl>() != nullptr) {
      // (int var_name[range])
      expectedRelation = LineColumnRelation::After;
    } else if (parent->Cast<uhdm::ModuleArray>() != nullptr) {
      // (module_type var_name[range])
      expectedRelation = LineColumnRelation::After;
    } else if (parent->Cast<uhdm::ArrayVar>() != nullptr) {
      // int var_name[range]
      expectedRelation = LineColumnRelation::After;
    } else if (parent->Cast<uhdm::ArrayNet>() != nullptr) {
      // some_type var_name[range]
      expectedRelation = LineColumnRelation::After;
    } else if (parent->Cast<uhdm::PackedArrayVar>() != nullptr) {
      // elem_type [range] var_name
      expectedRelation = LineColumnRelation::Before;
    } else if (parent->Cast<uhdm::LogicVar>() != nullptr) {
      // logic [range] var_name
      expectedRelation = LineColumnRelation::Before;
    }
  } else if (object->getUhdmType() == uhdm::UhdmType::Attribute) {
    expectedRelation = LineColumnRelation::Before;
    if (parent->Cast<uhdm::Instance>() != nullptr) {
      // (* uhdm::Attribute*) class <class_name>;
      // (* uhdm::Attribute*) module <module_name>;
      // (* uhdm::Attribute*) interface <interface_name>;
      // (* uhdm::Attribute*) package <package_name>;
      // (* uhdm::Attribute*) program <program_name>;
      expectedRelation = LineColumnRelation::Before;
    } else if (parent->Cast<uhdm::LogicNet>() != nullptr) {
      // (* uhdm::Attribute*) input <logic_name>;
      // (* uhdm::Attribute*) output <logic_name>;
      expectedRelation = LineColumnRelation::Before;
    } else if (parent->Cast<uhdm::Port>() != nullptr) {
      // (* uhdm::Attribute*) input <port_name>
      // (* uhdm::Attribute*) output <port_name>
      expectedRelation = LineColumnRelation::Before;
    } else if (parent->Cast<uhdm::Primitive>() != nullptr) {
      // (* uhdm::Attribute*) primitive primitive_name;
      expectedRelation = LineColumnRelation::Before;
    }
  } else if (object->getUhdmType() == uhdm::UhdmType::SeqFormalDecl) {
    if (const uhdm::LetDecl* const parentAsLetDecl =
            parent->Cast<uhdm::LetDecl>()) {
      if (const uhdm::SeqFormalDeclCollection* const decls =
              parentAsLetDecl->getSeqFormalDecls()) {
        for (const uhdm::SeqFormalDecl* const decl : *decls) {
          if (decl == object) {
            // let <name>(<..., decl, ...>) = <object>
            expectedRelation = LineColumnRelation::After;
            break;
          }
        }
      }
    }
  } else if (object->getUhdmType() == uhdm::UhdmType::Port) {
    if ((parent->Cast<uhdm::RefModule>() != nullptr) ||
        (parent->Cast<uhdm::ModuleArray>() != nullptr)) {
      // module_type module_name(..., port, ...)
      expectedRelation = LineColumnRelation::After;
    }
  }

  if (const uhdm::EventControl* parentAsEventControl =
          parent->Cast<uhdm::EventControl>()) {
    if (parentAsEventControl->getStmt() == object) {
      // always @(....) begin ... end
      expectedRelation = LineColumnRelation::After;
    }
  } else if (const uhdm::IODecl* const parentAsIODecl =
                 parent->Cast<uhdm::IODecl>()) {
    if (parentAsIODecl->getExpr() == object) {
      // io_decl::expr represent the default value which is
      // on the right of the variable!
      expectedRelation = LineColumnRelation::After;
    }
  } else if (const uhdm::Variables* parentAsVariable =
                 parent->Cast<uhdm::Variables>()) {
    if (parentAsVariable->getExpr() == object) {
      expectedRelation = LineColumnRelation::After;
    }
  } else if (const uhdm::Ports* const parentAsPorts =
                 parent->Cast<uhdm::Port>()) {
    if (parentAsPorts->getHighConn() == object) {
      // module modname(..., .port(high_conn), ... )  <= After
      // module modname(..., port, ... )  <= Inside
      if (actualRelation == LineColumnRelation::After) {
        expectedRelation = LineColumnRelation::After;
      }
    }
  } else if (const uhdm::LetDecl* const parentAsLetDecl =
                 parent->Cast<uhdm::LetDecl>()) {
    if (const uhdm::ExprCollection* const exprs = parentAsLetDecl->getExprs()) {
      for (const uhdm::Expr* const expr : *exprs) {
        if (expr == object) {
          // let <name>(<args>) = <object>
          expectedRelation = LineColumnRelation::After;
          break;
        }
      }
    }
  }

  if (actualRelation != expectedRelation) {
    if ((actualRelation == LineColumnRelation::After) &&
        (expectedRelation == LineColumnRelation::Before) &&
        (object->getUhdmType() == uhdm::UhdmType::RefTypespec) &&
        ((parent->getUhdmType() == uhdm::UhdmType::Port) ||
         (parent->getUhdmType() == uhdm::UhdmType::PackedArrayVar))) {
      // typespec for uhdm::Ports*can* be inside the parent module!
      // module (port_name):
      //   input int port_name;
      // endmodule
      const uhdm::Any* const grandParent = parent->getParent();

      const uint32_t psl = grandParent->getStartLine();
      const uint32_t psc = grandParent->getStartColumn();
      const uint32_t pel = grandParent->getEndLine();
      const uint32_t pec = grandParent->getEndColumn();

      actualRelation =
          getLineColumnRelation(csl, csc, cel, cec, psl, psc, pel, pec);
      expectedRelation = LineColumnRelation::Inside;
    } else if ((actualRelation == LineColumnRelation::Inside) &&
               (expectedRelation == LineColumnRelation::After) &&
               (parent->getUhdmType() == uhdm::UhdmType::Port)) {
      // unnamed port arguments for ref_module
      // module_type module_name(..., port, ...)

      if ((csl == psl) && (csc == psc) && (cel == pel) && (cec == pec)) {
        if (const uhdm::Port* const parentAsPort = parent->Cast<uhdm::Port>()) {
          if (parentAsPort->getHighConn() == object) {
            expectedRelation = LineColumnRelation::Inside;
          }
        }
      }
    }
  }

  if (actualRelation != expectedRelation) {
    const std::set<const uhdm::PreprocMacroInstance*> objectPMIs =
        getMacroInstances(object);
    const std::set<const uhdm::PreprocMacroInstance*> parentPMIs =
        getMacroInstances(parent);
    if (objectPMIs == parentPMIs) {
      Location loc(
          fileSystem->toPathId(object->getFile(), symbolTable),
          object->getStartLine(), object->getStartColumn(),
          symbolTable->registerSymbol(StrCat("Child: ", asSymbol(object),
                                             " Parent: ", asSymbol(parent))));
      errorContainer->addError(
          ErrorDefinition::INTEGRITY_CHECK_BAD_RELATIVE_LOCATION, loc);
    }
  }
}

void IntegrityChecker::reportMissingLocation(const uhdm::Any* object) const {
  if ((object->getStartLine() != 0) && (object->getStartColumn() != 0) &&
      (object->getEndLine() != 0) && (object->getEndColumn() != 0))
    return;

  if (m_acceptedUhdmTypesWithInvalidLocation.find(object->getUhdmType()) !=
      m_acceptedUhdmTypesWithInvalidLocation.cend())
    return;

  const uhdm::Any* const parent = object->getParent();
  if (parent == nullptr) return;

  const uhdm::Any* const grandParent = parent->getParent();
  if (grandParent == nullptr) return;

  // begin in function body are implicit!
  if ((object->getUhdmType() == uhdm::UhdmType::Begin) &&
      (parent->getUhdmType() == uhdm::UhdmType::Function))
    return;

  if ((object->getUhdmType() == uhdm::UhdmType::RefTypespec) &&
      (grandParent->getName() == "new") &&
      (parent->Cast<uhdm::Variables>() != nullptr) &&
      (grandParent->getUhdmType() == uhdm::UhdmType::Function)) {
    // For refTypespec associated with a class's constructor return value
    // there is no legal position because the "new" operator's return value
    // is implicit.
    const uhdm::Variables* const parentAsVariables =
        parent->Cast<uhdm::Variables>();
    const uhdm::TaskFunc* const grandParentAsTaskFunc =
        grandParent->Cast<uhdm::Function>();
    if ((grandParentAsTaskFunc->getReturn() == parent) &&
        (parentAsVariables->getTypespec() == object)) {
      return;
    }
  } else if ((object->getUhdmType() == uhdm::UhdmType::ClassTypespec) &&
             (parent->getName() == "new") &&
             (parent->getUhdmType() == uhdm::UhdmType::Function)) {
    // For typespec associated with a class's constructor return value
    // there is no legal position because the "new" operator's return value
    // is implicit.
    const uhdm::Function* const parentAsFunction =
        parent->Cast<uhdm::Function>();
    if (const uhdm::Variables* const var = parentAsFunction->getReturn()) {
      if (const uhdm::RefTypespec* const rt = var->getTypespec()) {
        if ((rt == object) || (rt->getActual() == object)) {
          return;
        }
      }
    }
  } else if (object->Cast<uhdm::Variables>() != nullptr) {
    // When no explicit return is specific, the function's name
    // is consdiered the return type's name.
    if (const uhdm::TaskFunc* const parentAsTaskFunc =
            parent->Cast<uhdm::TaskFunc>()) {
      if (parentAsTaskFunc->getReturn() == object) return;
    }
  } else if (const uhdm::Constant* const objectAsConstant =
                 object->Cast<uhdm::Constant>()) {
    if (const uhdm::Range* const parentAsRange = parent->Cast<uhdm::Range>()) {
      // The left expression of range is allowed to be zero.
      if (parentAsRange->getLeftExpr() == object) return;

      // The right is allowed to be zero if it's associative
      if ((parentAsRange->getRightExpr() == object) &&
          (objectAsConstant->getValue() == "STRING:associative")) {
        return;
      }
    }
  }

  SymbolTable* const symbolTable = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errorContainer = m_session->getErrorContainer();

  Location loc(fileSystem->toPathId(object->getFile(), symbolTable),
               object->getStartLine(), object->getStartColumn(),
               symbolTable->registerSymbol(asSymbol(object)));
  errorContainer->addError(ErrorDefinition::INTEGRITY_CHECK_MISSING_LOCATION,
                           loc);
}

bool IntegrityChecker::isImplicitFunctionReturnType(const uhdm::Any* object) {
  if (any_cast<uhdm::RefTypespec>(object) != nullptr) {
    object = object->getParent();
  }
  if (const uhdm::Variables* v = any_cast<uhdm::Variables>(object)) {
    if (const uhdm::Function* f = object->getParent<uhdm::Function>()) {
      if ((f->getReturn() == v) && v->getName().empty()) return true;
    }
  }
  return false;
}

std::string_view IntegrityChecker::stripDecorations(std::string_view name) {
  while (!name.empty() && name.back() == ':') name.remove_suffix(1);

  size_t pos1 = name.rfind("::");
  if (pos1 != std::string::npos) name = name.substr(pos1 + 2);

  size_t pos2 = name.rfind('.');
  if (pos2 != std::string::npos) name = name.substr(pos2 + 1);

  size_t pos3 = name.rfind('@');
  if (pos3 != std::string::npos) name = name.substr(pos3 + 1);

  return name;
}

bool IntegrityChecker::areNamedSame(const uhdm::Any* object,
                                    const uhdm::Any* actual) {
  std::string_view objectName = stripDecorations(object->getName());
  std::string_view actualName = stripDecorations(actual->getName());
  return (objectName == actualName);
}

void IntegrityChecker::reportInvalidNames(const uhdm::Any* object) const {
  // Implicit function return type are unnammed.
  if (isImplicitFunctionReturnType(object)) return;

  bool shouldReport = false;

  if (const uhdm::RefObj* const objectAsRefObj = object->Cast<uhdm::RefObj>()) {
    shouldReport = object->getName().empty();
    shouldReport =
        shouldReport || (object->getName().find(SymbolTable::getBadSymbol()) !=
                         std::string_view::npos);

    if (const uhdm::Any* const actual = objectAsRefObj->getActual()) {
      shouldReport = shouldReport || !areNamedSame(object, actual);
      shouldReport = shouldReport && !isImplicitFunctionReturnType(actual);
    }

    shouldReport = shouldReport && (object->getName() != "super");
    shouldReport = shouldReport && (object->getName() != "this");
  } else if (const uhdm::RefTypespec* const objectAsRefTypespec =
                 object->Cast<const uhdm::RefTypespec*>()) {
    shouldReport = (object->getName().find(SymbolTable::getBadSymbol()) !=
                    std::string_view::npos);
    if (const uhdm::TypedefTypespec* const parent =
            object->getParent<uhdm::TypedefTypespec>()) {
      if (parent->getTypedefAlias() != nullptr) {
        shouldReport = false;
      }
    } else if (const uhdm::Any* actual = objectAsRefTypespec->getActual()) {
      if ((actual->getUhdmType() == uhdm::UhdmType::ArrayTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::BitTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::ByteTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::ChandleTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::IntTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::IntegerTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::LogicTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::LongIntTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::PackedArrayTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::RealTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::ShortIntTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::ShortRealTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::StringTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::TimeTypespec) ||
          (actual->getUhdmType() == uhdm::UhdmType::VoidTypespec)) {
        shouldReport = false;
      } else if ((actual->getUhdmType() == uhdm::UhdmType::EnumTypespec) ||
                 (actual->getUhdmType() == uhdm::UhdmType::StructTypespec) ||
                 (actual->getUhdmType() == uhdm::UhdmType::UnionTypespec)) {
        shouldReport = false;
      } else if ((actual->getUhdmType() == uhdm::UhdmType::ClassTypespec) ||
                 (actual->getUhdmType() == uhdm::UhdmType::InterfaceTypespec) ||
                 (actual->getUhdmType() == uhdm::UhdmType::ModuleTypespec) ||
                 (actual->getUhdmType() ==
                  uhdm::UhdmType::UnsupportedTypespec)) {
        shouldReport = shouldReport || object->getName().empty();
        if (object->getName() != "item") {
          shouldReport = shouldReport || !areNamedSame(object, actual);
        }
      }
    } else {
      shouldReport = shouldReport || object->getName().empty();
    }
  }

  if (shouldReport) {
    SymbolTable* const symbolTable = m_session->getSymbolTable();
    FileSystem* const fileSystem = m_session->getFileSystem();
    ErrorContainer* const errorContainer = m_session->getErrorContainer();

    Location loc(fileSystem->toPathId(object->getFile(), symbolTable),
                 object->getStartLine(), object->getStartColumn(),
                 symbolTable->registerSymbol(asSymbol(object)));
    errorContainer->addError(ErrorDefinition::INTEGRITY_CHECK_MISSING_NAME,
                             loc);
  }
}

void IntegrityChecker::reportInvalidFile(const uhdm::Any* object) const {
  if (object->getUhdmType() == uhdm::UhdmType::Design) return;

  std::string_view filename = object->getFile();
  if (filename.empty() || (filename == SymbolTable::getBadSymbol())) {
    SymbolTable* const symbolTable = m_session->getSymbolTable();
    FileSystem* const fileSystem = m_session->getFileSystem();
    ErrorContainer* const errorContainer = m_session->getErrorContainer();

    Location loc(fileSystem->toPathId(object->getFile(), symbolTable),
                 object->getStartLine(), object->getStartColumn(),
                 symbolTable->registerSymbol(asSymbol(object)));
    errorContainer->addError(ErrorDefinition::INTEGRITY_CHECK_MISSING_FILE,
                             loc);
  }
}

void IntegrityChecker::reportNullActual(const uhdm::Any* object) const {
  if (isBuiltInPackageOnStack(object)) return;

  bool shouldReport = false;

  if (const uhdm::RefObj* const objectAsRefObj = object->Cast<uhdm::RefObj>()) {
    shouldReport = objectAsRefObj->getActual() == nullptr;
    // Special case for $root and few others
    if (const uhdm::Any* const parent = object->getParent()) {
      shouldReport =
          shouldReport &&
          !(((object->getName() == "$root") || (object->getName() == "size") ||
             (object->getName() == "delete")) &&
            (parent->getUhdmType() == uhdm::UhdmType::HierPath));
      shouldReport = shouldReport &&
                     !((parent->getUhdmType() == uhdm::UhdmType::SysFuncCall) &&
                       (parent->getName() == "$bits"));
      shouldReport = shouldReport && (object->getName() != "default");
    }
  } else if (const uhdm::RefTypespec* const objectAsRefTypespec =
                 object->Cast<const uhdm::RefTypespec*>()) {
    if (const uhdm::TypedefTypespec* const parent =
            object->getParent<uhdm::TypedefTypespec>()) {
      if (parent->getTypedefAlias() != nullptr) {
        shouldReport = false;
      }
    } else {
      shouldReport = objectAsRefTypespec->getActual() == nullptr;
    }
  } else if (const uhdm::RefModule* const objectAsRefModule =
                 object->Cast<const uhdm::RefModule*>()) {
    shouldReport = objectAsRefModule->getActual() == nullptr;
  } else if (const uhdm::ChandleVar* const objectAsChandleVar =
                 object->Cast<const uhdm::ChandleVar*>()) {
    shouldReport = objectAsChandleVar->getActual() == nullptr;
  } else if (const uhdm::TaskFunc* const parentAsTaskFunc =
                 object->getParent<uhdm::TaskFunc>()) {
    if ((parentAsTaskFunc->getReturn() == object) &&
        (parentAsTaskFunc->getAccessType() == vpiDPIImportAcc)) {
      // Imported functions cannot be bound!
      shouldReport = false;
    }
  }

  if (shouldReport) {
    SymbolTable* const symbolTable = m_session->getSymbolTable();
    FileSystem* const fileSystem = m_session->getFileSystem();
    ErrorContainer* const errorContainer = m_session->getErrorContainer();

    Location loc(fileSystem->toPathId(object->getFile(), symbolTable),
                 object->getStartLine(), object->getStartColumn(),
                 symbolTable->registerSymbol(asSymbol(object)));
    errorContainer->addError(ErrorDefinition::INTEGRITY_CHECK_BINDING, loc);
  }
}

void IntegrityChecker::enterAny(const uhdm::Any* object, uint32_t vpiRelation) {
  if (isBuiltInPackageOnStack(object)) return;
  if (isUVMMember(object)) return;

  reportNullActual(object);

  // Known Issues!
  if (const uhdm::IntTypespec* const t = any_cast<uhdm::IntTypespec>(object)) {
    if (const uhdm::Expr* const e = t->getExpr()) {
      m_visited.emplace(e);
    }
  } else if (const uhdm::Operation* const op =
                 any_cast<uhdm::Operation>(object)) {
    if (op->getOpType() == vpiCastOp) {
      if (const uhdm::RefTypespec* const rt = op->getTypespec()) {
        if (const uhdm::IntTypespec* const t =
                rt->getActual<uhdm::IntTypespec>()) {
          if (const uhdm::Expr* const e = t->getExpr()) {
            m_visited.emplace(e);
          }
        }
      }
    }
  }

  reportMissingLocation(object);
  reportInvalidNames(object);
  reportInvalidFile(object);

  SymbolTable* const symbolTable = m_session->getSymbolTable();
  FileSystem* const fileSystem = m_session->getFileSystem();
  ErrorContainer* const errorContainer = m_session->getErrorContainer();

  const uhdm::Any* const parent = object->getParent();
  if ((object->getUhdmType() != uhdm::UhdmType::Design) &&
      (parent == nullptr)) {
    Location loc(fileSystem->toPathId(object->getFile(), symbolTable),
                 object->getStartLine(), object->getStartColumn(),
                 symbolTable->registerSymbol(asSymbol(object)));
    errorContainer->addError(ErrorDefinition::INTEGRITY_CHECK_MISSING_PARENT,
                             loc);
    return;
  }

  reportInvalidLocation(object);

  const uhdm::Scope* const parentAsScope = any_cast<uhdm::Scope>(parent);
  const uhdm::Design* const parentAsDesign = any_cast<uhdm::Design>(parent);
  const uhdm::UdpDefn* const parentAsUdpDefn = any_cast<uhdm::UdpDefn>(parent);

  const std::set<uhdm::UhdmType> allowedScopeChildren{
      uhdm::UhdmType::ArrayNet,
      uhdm::UhdmType::ArrayTypespec,
      uhdm::UhdmType::ArrayVar,
      uhdm::UhdmType::Assert,
      uhdm::UhdmType::Assume,
      uhdm::UhdmType::BitTypespec,
      uhdm::UhdmType::BitVar,
      uhdm::UhdmType::ByteTypespec,
      uhdm::UhdmType::ByteVar,
      uhdm::UhdmType::ChandleTypespec,
      uhdm::UhdmType::ChandleVar,
      uhdm::UhdmType::ClassTypespec,
      uhdm::UhdmType::ClassVar,
      uhdm::UhdmType::ConcurrentAssertions,
      uhdm::UhdmType::Cover,
      uhdm::UhdmType::EnumNet,
      uhdm::UhdmType::EnumTypespec,
      uhdm::UhdmType::EnumVar,
      uhdm::UhdmType::EventTypespec,
      uhdm::UhdmType::ImportTypespec,
      uhdm::UhdmType::IntTypespec,
      uhdm::UhdmType::IntVar,
      uhdm::UhdmType::IntegerNet,
      uhdm::UhdmType::IntegerTypespec,
      uhdm::UhdmType::IntegerVar,
      uhdm::UhdmType::InterfaceTypespec,
      uhdm::UhdmType::LetDecl,
      uhdm::UhdmType::LogicNet,
      uhdm::UhdmType::LogicTypespec,
      uhdm::UhdmType::LogicVar,
      uhdm::UhdmType::LongIntTypespec,
      uhdm::UhdmType::LongIntVar,
      uhdm::UhdmType::ModuleTypespec,
      uhdm::UhdmType::NamedEvent,
      uhdm::UhdmType::NamedEventArray,
      uhdm::UhdmType::NetBit,
      uhdm::UhdmType::PackedArrayNet,
      uhdm::UhdmType::PackedArrayTypespec,
      uhdm::UhdmType::PackedArrayVar,
      uhdm::UhdmType::ParamAssign,
      uhdm::UhdmType::Parameter,
      uhdm::UhdmType::PropertyDecl,
      uhdm::UhdmType::PropertyTypespec,
      uhdm::UhdmType::RealTypespec,
      uhdm::UhdmType::RealVar,
      uhdm::UhdmType::RefVar,
      uhdm::UhdmType::Restrict,
      uhdm::UhdmType::SequenceDecl,
      uhdm::UhdmType::SequenceTypespec,
      uhdm::UhdmType::ShortIntTypespec,
      uhdm::UhdmType::ShortIntVar,
      uhdm::UhdmType::ShortRealTypespec,
      uhdm::UhdmType::ShortRealVar,
      uhdm::UhdmType::StringTypespec,
      uhdm::UhdmType::StringVar,
      uhdm::UhdmType::StructNet,
      uhdm::UhdmType::StructTypespec,
      uhdm::UhdmType::StructVar,
      uhdm::UhdmType::TimeNet,
      uhdm::UhdmType::TimeTypespec,
      uhdm::UhdmType::TimeVar,
      uhdm::UhdmType::TypeParameter,
      uhdm::UhdmType::UnionTypespec,
      uhdm::UhdmType::UnionVar,
      uhdm::UhdmType::UnsupportedTypespec,
      uhdm::UhdmType::VarBit,
      uhdm::UhdmType::VirtualInterfaceVar,
      uhdm::UhdmType::VoidTypespec,
  };

  bool expectScope = (allowedScopeChildren.find(object->getUhdmType()) !=
                      allowedScopeChildren.cend());
  if (any_cast<uhdm::Begin>(object) != nullptr) {
    expectScope = false;
  }

  const std::set<uhdm::UhdmType> allowedDesignChildren{
      uhdm::UhdmType::Package,    uhdm::UhdmType::Module,
      uhdm::UhdmType::ClassDefn,  uhdm::UhdmType::Typespec,
      uhdm::UhdmType::LetDecl,    uhdm::UhdmType::Function,
      uhdm::UhdmType::Task,       uhdm::UhdmType::Parameter,
      uhdm::UhdmType::ParamAssign};
  bool expectDesign = (allowedDesignChildren.find(object->getUhdmType()) !=
                       allowedDesignChildren.cend());

  const std::set<uhdm::UhdmType> allowedUdpChildren{uhdm::UhdmType::LogicNet,
                                                    uhdm::UhdmType::IODecl,
                                                    uhdm::UhdmType::TableEntry};
  bool expectUdpDefn = (allowedUdpChildren.find(object->getUhdmType()) !=
                        allowedUdpChildren.cend());

  if ((object->getUhdmType() != uhdm::UhdmType::Design) &&
      (m_callstack.back() != object->getParent()) &&
      (m_callstack.back()->getUhdmType() !=
       uhdm::UhdmType::PreprocMacroInstance) &&
      ((object->getUhdmType() == uhdm::UhdmType::RefObj) ||
       (object->getUhdmType() == uhdm::UhdmType::RefTypespec))) {
    Location loc(
        fileSystem->toPathId(object->getFile(), symbolTable),
        object->getStartLine(), object->getStartColumn(),
        symbolTable->registerSymbol(std::to_string(object->getUhdmId())));
    errorContainer->addError(ErrorDefinition::INTEGRITY_CHECK_INVALID_REFPARENT,
                             loc);
  }

  if ((parentAsScope == nullptr) && (parentAsDesign == nullptr) &&
      (parentAsUdpDefn == nullptr) &&
      (expectScope || expectDesign || expectUdpDefn)) {
    Location loc(fileSystem->toPathId(object->getFile(), symbolTable),
                 object->getStartLine(), object->getStartColumn(),
                 symbolTable->registerSymbol(asSymbol(object)));
    errorContainer->addError(
        ErrorDefinition::INTEGRITY_CHECK_PARENT_IS_NEITHER_SCOPE_NOR_DESIGN,
        loc);
  }
}

void IntegrityChecker::enterAliasCollection(
    const uhdm::Any* object, const uhdm::AliasCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterAlwaysCollection(
    const uhdm::Any* object, const uhdm::AlwaysCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterAnyCollection(const uhdm::Any* object,
                                          const uhdm::AnyCollection& objects,
                                          uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterAnyPatternCollection(
    const uhdm::Any* object, const uhdm::AnyPatternCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterArrayExprCollection(
    const uhdm::Any* object, const uhdm::ArrayExprCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterArrayNetCollection(
    const uhdm::Any* object, const uhdm::ArrayNetCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterArrayTypespecCollection(
    const uhdm::Any* object, const uhdm::ArrayTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterArrayVarCollection(
    const uhdm::Any* object, const uhdm::ArrayVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterAssertCollection(
    const uhdm::Any* object, const uhdm::AssertCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterAssignStmtCollection(
    const uhdm::Any* object, const uhdm::AssignStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterAssignmentCollection(
    const uhdm::Any* object, const uhdm::AssignmentCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterAssumeCollection(
    const uhdm::Any* object, const uhdm::AssumeCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterAtomicStmtCollection(
    const uhdm::Any* object, const uhdm::AtomicStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterAttributeCollection(
    const uhdm::Any* object, const uhdm::AttributeCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterBeginCollection(
    const uhdm::Any* object, const uhdm::BeginCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterBitSelectCollection(
    const uhdm::Any* object, const uhdm::BitSelectCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterBitTypespecCollection(
    const uhdm::Any* object, const uhdm::BitTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterBitVarCollection(
    const uhdm::Any* object, const uhdm::BitVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterBreakStmtCollection(
    const uhdm::Any* object, const uhdm::BreakStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterByteTypespecCollection(
    const uhdm::Any* object, const uhdm::ByteTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterByteVarCollection(
    const uhdm::Any* object, const uhdm::ByteVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterCaseItemCollection(
    const uhdm::Any* object, const uhdm::CaseItemCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterCasePropertyCollection(
    const uhdm::Any* object, const uhdm::CasePropertyCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterCasePropertyItemCollection(
    const uhdm::Any* object, const uhdm::CasePropertyItemCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterCaseStmtCollection(
    const uhdm::Any* object, const uhdm::CaseStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterChandleTypespecCollection(
    const uhdm::Any* object, const uhdm::ChandleTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterChandleVarCollection(
    const uhdm::Any* object, const uhdm::ChandleVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterCheckerDeclCollection(
    const uhdm::Any* object, const uhdm::CheckerDeclCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterCheckerInstCollection(
    const uhdm::Any* object, const uhdm::CheckerInstCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterCheckerInstPortCollection(
    const uhdm::Any* object, const uhdm::CheckerInstPortCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterCheckerPortCollection(
    const uhdm::Any* object, const uhdm::CheckerPortCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterClassDefnCollection(
    const uhdm::Any* object, const uhdm::ClassDefnCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterClassObjCollection(
    const uhdm::Any* object, const uhdm::ClassObjCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterClassTypespecCollection(
    const uhdm::Any* object, const uhdm::ClassTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterClassVarCollection(
    const uhdm::Any* object, const uhdm::ClassVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterClockedPropertyCollection(
    const uhdm::Any* object, const uhdm::ClockedPropertyCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterClockedSeqCollection(
    const uhdm::Any* object, const uhdm::ClockedSeqCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterClockingBlockCollection(
    const uhdm::Any* object, const uhdm::ClockingBlockCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterClockingIODeclCollection(
    const uhdm::Any* object, const uhdm::ClockingIODeclCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterConcurrentAssertionsCollection(
    const uhdm::Any* object,
    const uhdm::ConcurrentAssertionsCollection& objects, uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterConstantCollection(
    const uhdm::Any* object, const uhdm::ConstantCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterConstrForeachCollection(
    const uhdm::Any* object, const uhdm::ConstrForeachCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterConstrIfCollection(
    const uhdm::Any* object, const uhdm::ConstrIfCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterConstrIfElseCollection(
    const uhdm::Any* object, const uhdm::ConstrIfElseCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterConstraintCollection(
    const uhdm::Any* object, const uhdm::ConstraintCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterConstraintExprCollection(
    const uhdm::Any* object, const uhdm::ConstraintExprCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterConstraintOrderingCollection(
    const uhdm::Any* object, const uhdm::ConstraintOrderingCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterContAssignBitCollection(
    const uhdm::Any* object, const uhdm::ContAssignBitCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterContAssignCollection(
    const uhdm::Any* object, const uhdm::ContAssignCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterContinueStmtCollection(
    const uhdm::Any* object, const uhdm::ContinueStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterCoverCollection(
    const uhdm::Any* object, const uhdm::CoverCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterDeassignCollection(
    const uhdm::Any* object, const uhdm::DeassignCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterDefParamCollection(
    const uhdm::Any* object, const uhdm::DefParamCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterDelayControlCollection(
    const uhdm::Any* object, const uhdm::DelayControlCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterDelayTermCollection(
    const uhdm::Any* object, const uhdm::DelayTermCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterDesignCollection(
    const uhdm::Any* object, const uhdm::DesignCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterDisableCollection(
    const uhdm::Any* object, const uhdm::DisableCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterDisableForkCollection(
    const uhdm::Any* object, const uhdm::DisableForkCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterDisablesCollection(
    const uhdm::Any* object, const uhdm::DisablesCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterDistItemCollection(
    const uhdm::Any* object, const uhdm::DistItemCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterDistributionCollection(
    const uhdm::Any* object, const uhdm::DistributionCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterDoWhileCollection(
    const uhdm::Any* object, const uhdm::DoWhileCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterEnumConstCollection(
    const uhdm::Any* object, const uhdm::EnumConstCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterEnumNetCollection(
    const uhdm::Any* object, const uhdm::EnumNetCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterEnumTypespecCollection(
    const uhdm::Any* object, const uhdm::EnumTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterEnumVarCollection(
    const uhdm::Any* object, const uhdm::EnumVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterEventControlCollection(
    const uhdm::Any* object, const uhdm::EventControlCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterEventStmtCollection(
    const uhdm::Any* object, const uhdm::EventStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterEventTypespecCollection(
    const uhdm::Any* object, const uhdm::EventTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterExpectStmtCollection(
    const uhdm::Any* object, const uhdm::ExpectStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterExprCollection(const uhdm::Any* object,
                                           const uhdm::ExprCollection& objects,
                                           uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterExtendsCollection(
    const uhdm::Any* object, const uhdm::ExtendsCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterFinalStmtCollection(
    const uhdm::Any* object, const uhdm::FinalStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterForStmtCollection(
    const uhdm::Any* object, const uhdm::ForStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterForceCollection(
    const uhdm::Any* object, const uhdm::ForceCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterForeachStmtCollection(
    const uhdm::Any* object, const uhdm::ForeachStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterForeverStmtCollection(
    const uhdm::Any* object, const uhdm::ForeverStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterForkStmtCollection(
    const uhdm::Any* object, const uhdm::ForkStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterFuncCallCollection(
    const uhdm::Any* object, const uhdm::FuncCallCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterFunctionCollection(
    const uhdm::Any* object, const uhdm::FunctionCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterFunctionDeclCollection(
    const uhdm::Any* object, const uhdm::FunctionDeclCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterGateArrayCollection(
    const uhdm::Any* object, const uhdm::GateArrayCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterGateCollection(const uhdm::Any* object,
                                           const uhdm::GateCollection& objects,
                                           uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterGenCaseCollection(
    const uhdm::Any* object, const uhdm::GenCaseCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterGenForCollection(
    const uhdm::Any* object, const uhdm::GenForCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterGenIfCollection(
    const uhdm::Any* object, const uhdm::GenIfCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterGenIfElseCollection(
    const uhdm::Any* object, const uhdm::GenIfElseCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterGenRegionCollection(
    const uhdm::Any* object, const uhdm::GenRegionCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterGenScopeArrayCollection(
    const uhdm::Any* object, const uhdm::GenScopeArrayCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterGenScopeCollection(
    const uhdm::Any* object, const uhdm::GenScopeCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterGenStmtCollection(
    const uhdm::Any* object, const uhdm::GenStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterGenVarCollection(
    const uhdm::Any* object, const uhdm::GenVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterHierPathCollection(
    const uhdm::Any* object, const uhdm::HierPathCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterIODeclCollection(
    const uhdm::Any* object, const uhdm::IODeclCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterIfElseCollection(
    const uhdm::Any* object, const uhdm::IfElseCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterIfStmtCollection(
    const uhdm::Any* object, const uhdm::IfStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterImmediateAssertCollection(
    const uhdm::Any* object, const uhdm::ImmediateAssertCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterImmediateAssumeCollection(
    const uhdm::Any* object, const uhdm::ImmediateAssumeCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterImmediateCoverCollection(
    const uhdm::Any* object, const uhdm::ImmediateCoverCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterImplicationCollection(
    const uhdm::Any* object, const uhdm::ImplicationCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterImportTypespecCollection(
    const uhdm::Any* object, const uhdm::ImportTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterIndexedPartSelectCollection(
    const uhdm::Any* object, const uhdm::IndexedPartSelectCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterInitialCollection(
    const uhdm::Any* object, const uhdm::InitialCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterInstanceArrayCollection(
    const uhdm::Any* object, const uhdm::InstanceArrayCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterInstanceCollection(
    const uhdm::Any* object, const uhdm::InstanceCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterIntTypespecCollection(
    const uhdm::Any* object, const uhdm::IntTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterIntVarCollection(
    const uhdm::Any* object, const uhdm::IntVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterIntegerNetCollection(
    const uhdm::Any* object, const uhdm::IntegerNetCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterIntegerTypespecCollection(
    const uhdm::Any* object, const uhdm::IntegerTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterIntegerVarCollection(
    const uhdm::Any* object, const uhdm::IntegerVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterInterfaceArrayCollection(
    const uhdm::Any* object, const uhdm::InterfaceArrayCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterInterfaceCollection(
    const uhdm::Any* object, const uhdm::InterfaceCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterInterfaceTFDeclCollection(
    const uhdm::Any* object, const uhdm::InterfaceTFDeclCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterInterfaceTypespecCollection(
    const uhdm::Any* object, const uhdm::InterfaceTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterLetDeclCollection(
    const uhdm::Any* object, const uhdm::LetDeclCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterLetExprCollection(
    const uhdm::Any* object, const uhdm::LetExprCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterLogicNetCollection(
    const uhdm::Any* object, const uhdm::LogicNetCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterLogicTypespecCollection(
    const uhdm::Any* object, const uhdm::LogicTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterLogicVarCollection(
    const uhdm::Any* object, const uhdm::LogicVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterLongIntTypespecCollection(
    const uhdm::Any* object, const uhdm::LongIntTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterLongIntVarCollection(
    const uhdm::Any* object, const uhdm::LongIntVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterMethodFuncCallCollection(
    const uhdm::Any* object, const uhdm::MethodFuncCallCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterMethodTaskCallCollection(
    const uhdm::Any* object, const uhdm::MethodTaskCallCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterModPathCollection(
    const uhdm::Any* object, const uhdm::ModPathCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterModportCollection(
    const uhdm::Any* object, const uhdm::ModportCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterModuleArrayCollection(
    const uhdm::Any* object, const uhdm::ModuleArrayCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterModuleCollection(
    const uhdm::Any* object, const uhdm::ModuleCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterModuleTypespecCollection(
    const uhdm::Any* object, const uhdm::ModuleTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterMulticlockSequenceExprCollection(
    const uhdm::Any* object,
    const uhdm::MulticlockSequenceExprCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterNamedEventArrayCollection(
    const uhdm::Any* object, const uhdm::NamedEventArrayCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterNamedEventCollection(
    const uhdm::Any* object, const uhdm::NamedEventCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterNetBitCollection(
    const uhdm::Any* object, const uhdm::NetBitCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterNetCollection(const uhdm::Any* object,
                                          const uhdm::NetCollection& objects,
                                          uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterNetDriversCollection(
    const uhdm::Any* object, const uhdm::NetDriversCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterNetLoadsCollection(
    const uhdm::Any* object, const uhdm::NetLoadsCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterNetsCollection(const uhdm::Any* object,
                                           const uhdm::NetsCollection& objects,
                                           uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterNullStmtCollection(
    const uhdm::Any* object, const uhdm::NullStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterOperationCollection(
    const uhdm::Any* object, const uhdm::OperationCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterOrderedWaitCollection(
    const uhdm::Any* object, const uhdm::OrderedWaitCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPackageCollection(
    const uhdm::Any* object, const uhdm::PackageCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPackedArrayNetCollection(
    const uhdm::Any* object, const uhdm::PackedArrayNetCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPackedArrayTypespecCollection(
    const uhdm::Any* object, const uhdm::PackedArrayTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPackedArrayVarCollection(
    const uhdm::Any* object, const uhdm::PackedArrayVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterParamAssignCollection(
    const uhdm::Any* object, const uhdm::ParamAssignCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterParameterCollection(
    const uhdm::Any* object, const uhdm::ParameterCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPartSelectCollection(
    const uhdm::Any* object, const uhdm::PartSelectCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPathTermCollection(
    const uhdm::Any* object, const uhdm::PathTermCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPortBitCollection(
    const uhdm::Any* object, const uhdm::PortBitCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPortCollection(const uhdm::Any* object,
                                           const uhdm::PortCollection& objects,
                                           uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPortsCollection(
    const uhdm::Any* object, const uhdm::PortsCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPreprocMacroDefinitionCollection(
    const uhdm::Any* object,
    const uhdm::PreprocMacroDefinitionCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPreprocMacroInstanceCollection(
    const uhdm::Any* object,
    const uhdm::PreprocMacroInstanceCollection& objects, uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPrimTermCollection(
    const uhdm::Any* object, const uhdm::PrimTermCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPrimitiveArrayCollection(
    const uhdm::Any* object, const uhdm::PrimitiveArrayCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPrimitiveCollection(
    const uhdm::Any* object, const uhdm::PrimitiveCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterProcessCollection(
    const uhdm::Any* object, const uhdm::ProcessCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterProgramArrayCollection(
    const uhdm::Any* object, const uhdm::ProgramArrayCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterProgramCollection(
    const uhdm::Any* object, const uhdm::ProgramCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPropFormalDeclCollection(
    const uhdm::Any* object, const uhdm::PropFormalDeclCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPropertyDeclCollection(
    const uhdm::Any* object, const uhdm::PropertyDeclCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPropertyInstCollection(
    const uhdm::Any* object, const uhdm::PropertyInstCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPropertySpecCollection(
    const uhdm::Any* object, const uhdm::PropertySpecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterPropertyTypespecCollection(
    const uhdm::Any* object, const uhdm::PropertyTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterRangeCollection(
    const uhdm::Any* object, const uhdm::RangeCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterRealTypespecCollection(
    const uhdm::Any* object, const uhdm::RealTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterRealVarCollection(
    const uhdm::Any* object, const uhdm::RealVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterRefModuleCollection(
    const uhdm::Any* object, const uhdm::RefModuleCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterRefObjCollection(
    const uhdm::Any* object, const uhdm::RefObjCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterRefTypespecCollection(
    const uhdm::Any* object, const uhdm::RefTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterRefVarCollection(
    const uhdm::Any* object, const uhdm::RefVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterRegArrayCollection(
    const uhdm::Any* object, const uhdm::RegArrayCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterRegCollection(const uhdm::Any* object,
                                          const uhdm::RegCollection& objects,
                                          uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterReleaseCollection(
    const uhdm::Any* object, const uhdm::ReleaseCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterRepeatCollection(
    const uhdm::Any* object, const uhdm::RepeatCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterRepeatControlCollection(
    const uhdm::Any* object, const uhdm::RepeatControlCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterRestrictCollection(
    const uhdm::Any* object, const uhdm::RestrictCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterReturnStmtCollection(
    const uhdm::Any* object, const uhdm::ReturnStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterScopeCollection(
    const uhdm::Any* object, const uhdm::ScopeCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterSeqFormalDeclCollection(
    const uhdm::Any* object, const uhdm::SeqFormalDeclCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterSequenceDeclCollection(
    const uhdm::Any* object, const uhdm::SequenceDeclCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterSequenceInstCollection(
    const uhdm::Any* object, const uhdm::SequenceInstCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterSequenceTypespecCollection(
    const uhdm::Any* object, const uhdm::SequenceTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterShortIntTypespecCollection(
    const uhdm::Any* object, const uhdm::ShortIntTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterShortIntVarCollection(
    const uhdm::Any* object, const uhdm::ShortIntVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterShortRealTypespecCollection(
    const uhdm::Any* object, const uhdm::ShortRealTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterShortRealVarCollection(
    const uhdm::Any* object, const uhdm::ShortRealVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterSimpleExprCollection(
    const uhdm::Any* object, const uhdm::SimpleExprCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterSoftDisableCollection(
    const uhdm::Any* object, const uhdm::SoftDisableCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterSourceFileCollection(
    const uhdm::Any* object, const uhdm::SourceFileCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterSpecParamCollection(
    const uhdm::Any* object, const uhdm::SpecParamCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterStringTypespecCollection(
    const uhdm::Any* object, const uhdm::StringTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterStringVarCollection(
    const uhdm::Any* object, const uhdm::StringVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterStructNetCollection(
    const uhdm::Any* object, const uhdm::StructNetCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterStructPatternCollection(
    const uhdm::Any* object, const uhdm::StructPatternCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterStructTypespecCollection(
    const uhdm::Any* object, const uhdm::StructTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterStructVarCollection(
    const uhdm::Any* object, const uhdm::StructVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterSwitchArrayCollection(
    const uhdm::Any* object, const uhdm::SwitchArrayCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterSwitchTranCollection(
    const uhdm::Any* object, const uhdm::SwitchTranCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterSysFuncCallCollection(
    const uhdm::Any* object, const uhdm::SysFuncCallCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterSysTaskCallCollection(
    const uhdm::Any* object, const uhdm::SysTaskCallCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTFCallCollection(
    const uhdm::Any* object, const uhdm::TFCallCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTableEntryCollection(
    const uhdm::Any* object, const uhdm::TableEntryCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTaggedPatternCollection(
    const uhdm::Any* object, const uhdm::TaggedPatternCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTaskCallCollection(
    const uhdm::Any* object, const uhdm::TaskCallCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTaskCollection(const uhdm::Any* object,
                                           const uhdm::TaskCollection& objects,
                                           uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTaskDeclCollection(
    const uhdm::Any* object, const uhdm::TaskDeclCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTaskFuncCollection(
    const uhdm::Any* object, const uhdm::TaskFuncCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTaskFuncDeclCollection(
    const uhdm::Any* object, const uhdm::TaskFuncDeclCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTchkCollection(const uhdm::Any* object,
                                           const uhdm::TchkCollection& objects,
                                           uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTchkTermCollection(
    const uhdm::Any* object, const uhdm::TchkTermCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterThreadCollection(
    const uhdm::Any* object, const uhdm::ThreadCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTimeNetCollection(
    const uhdm::Any* object, const uhdm::TimeNetCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTimeTypespecCollection(
    const uhdm::Any* object, const uhdm::TimeTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTimeVarCollection(
    const uhdm::Any* object, const uhdm::TimeVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTypeParameterCollection(
    const uhdm::Any* object, const uhdm::TypeParameterCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTypedefTypespecCollection(
    const uhdm::Any* object, const uhdm::TypedefTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTypespecCollection(
    const uhdm::Any* object, const uhdm::TypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterTypespecMemberCollection(
    const uhdm::Any* object, const uhdm::TypespecMemberCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterUdpArrayCollection(
    const uhdm::Any* object, const uhdm::UdpArrayCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterUdpCollection(const uhdm::Any* object,
                                          const uhdm::UdpCollection& objects,
                                          uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterUdpDefnCollection(
    const uhdm::Any* object, const uhdm::UdpDefnCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterUnionTypespecCollection(
    const uhdm::Any* object, const uhdm::UnionTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterUnionVarCollection(
    const uhdm::Any* object, const uhdm::UnionVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterUnsupportedExprCollection(
    const uhdm::Any* object, const uhdm::UnsupportedExprCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterUnsupportedStmtCollection(
    const uhdm::Any* object, const uhdm::UnsupportedStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterUnsupportedTypespecCollection(
    const uhdm::Any* object, const uhdm::UnsupportedTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterUserSystfCollection(
    const uhdm::Any* object, const uhdm::UserSystfCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterVarBitCollection(
    const uhdm::Any* object, const uhdm::VarBitCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterVarSelectCollection(
    const uhdm::Any* object, const uhdm::VarSelectCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterVariablesCollection(
    const uhdm::Any* object, const uhdm::VariablesCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterVirtualInterfaceVarCollection(
    const uhdm::Any* object, const uhdm::VirtualInterfaceVarCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterVoidTypespecCollection(
    const uhdm::Any* object, const uhdm::VoidTypespecCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterWaitForkCollection(
    const uhdm::Any* object, const uhdm::WaitForkCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterWaitStmtCollection(
    const uhdm::Any* object, const uhdm::WaitStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterWaitsCollection(
    const uhdm::Any* object, const uhdm::WaitsCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}
void IntegrityChecker::enterWhileStmtCollection(
    const uhdm::Any* object, const uhdm::WhileStmtCollection& objects,
    uint32_t vpiRelation) {
  reportDuplicates(object, objects, vpiRelation);
}

void IntegrityChecker::populateAnyMacroInstanceCache(
    const uhdm::PreprocMacroInstance* pmi) {
  if (const uhdm::AnyCollection* const objects = pmi->getObjects()) {
    for (const uhdm::Any* any : *objects) {
      m_anyMacroInstance.emplace(any, pmi);
    }
  }

  if (const uhdm::PreprocMacroInstanceCollection* children =
          pmi->getPreprocMacroInstances()) {
    for (const uhdm::PreprocMacroInstance* child : *children) {
      populateAnyMacroInstanceCache(child);
    }
  }
}

void IntegrityChecker::populateAnyMacroInstanceCache() {
  if (const uhdm::SourceFileCollection* const sourceFiles =
          m_design->getSourceFiles()) {
    for (const uhdm::SourceFile* sourceFile : *sourceFiles) {
      if (const uhdm::PreprocMacroInstanceCollection* const macroInstances =
              sourceFile->getPreprocMacroInstances()) {
        for (const uhdm::PreprocMacroInstance* pmi : *macroInstances) {
          populateAnyMacroInstanceCache(pmi);
        }
      }
    }
  }
}

void IntegrityChecker::check(const uhdm::Design* object) {
  m_design = object;
  populateAnyMacroInstanceCache();
  listenAny(object);
  m_design = nullptr;
}

void IntegrityChecker::check(const std::vector<const uhdm::Design*>& objects) {
  for (const uhdm::Design* d : objects) {
    check(d);
  }
}
}  // namespace SURELOG
