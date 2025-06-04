// -*- c++ -*-

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
 * File:   roundtrip.cpp
 * Author: hs
 *
 * Created on February 10, 2022, 12:00 PM
 */

#include <uhdm/ElaboratorListener.h>
#include <uhdm/UhdmListener.h>
#include <uhdm/VpiListener.h>
#include <uhdm/expr.h>
#include <uhdm/sv_vpi_user.h>
#include <uhdm/uhdm.h>
#include <uhdm/uhdm_types.h>
#include <uhdm/vpi_user.h>

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <regex>
#include <sstream>
#include <stack>
#include <string>
#include <string_view>
#include <system_error>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "Surelog/API/Surelog.h"
#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/PlatformFileSystem.h"
#include "Surelog/Common/Session.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/SourceCompile/SymbolTable.h"

#if defined(_MSC_VER)
#include <Windows.h>
#undef interface
#endif

static constexpr char kOverwriteMarker = '\0';

using file_content_t = std::vector<std::string>;
using design_content_t = std::map<std::filesystem::path, file_content_t>;

using op_type_names_t = std::unordered_map<int32_t, std::string_view>;
using direction_names_t = std::unordered_map<int16_t, std::string_view>;
using net_type_names_t = std::unordered_map<int16_t, std::string_view>;
using typespec_names_t = std::unordered_map<uhdm::UhdmType, std::string_view>;
using variable_type_names_t =
    std::unordered_map<uhdm::UhdmType, std::string_view>;
using edge_names_t = std::unordered_map<int32_t, std::string_view>;
using always_type_names_t = std::unordered_map<int32_t, std::string_view>;
using case_type_names_t = std::unordered_map<int32_t, std::string_view>;
using case_qualifier_names_t = std::unordered_map<int32_t, std::string_view>;

using comparison_result_t = std::pair<size_t, size_t>;
using file_statistics_t =
    std::tuple<std::filesystem::path, std::filesystem::path, size_t, size_t>;
using design_statistics_t = std::vector<file_statistics_t>;

static std::regex re_strip_single_line_comments("//.+$");
static std::regex re_strip_block_comments("/\\*.*\\*/");
static std::regex re_strip_space("\\s*");
static std::regex re_strip_trailing_semicolon(";$");
static std::regex re_add_optional_brackets("(module|task|function)\\s*(\\w+);");

// clang-format off
static direction_names_t kDirectionNames = {
  { vpiInput, "input" },
  { vpiOutput, "output" },
  { vpiInout, "inout" },
  { vpiMixedIO, "" },
  { vpiNoDirection, "" },
  { vpiRef, "ref" }
};

static net_type_names_t kNetTypeNames = {
  { vpiWire, "wire" }, { vpiWand, "wand" }, { vpiWor, "wor" }, { vpiTri, "" },   { vpiTri0, "" },
  { vpiTri1, "" },     { vpiTriReg, "" },   { vpiTriAnd, "" }, { vpiTriOr, "" }, { vpiSupply1, "" },
  { vpiSupply0, "" },  { vpiNone, "" },     { vpiUwire, "" },  { vpiReg, "reg" }
};

static const op_type_names_t kOpTypeNames = {
  { 0, "" },
  { vpiMinusOp, "-" },
  { vpiPlusOp, "+" },
  { vpiNotOp, "!" },
  { vpiBitNegOp, "~" },
  { vpiUnaryAndOp, "&" },
  { vpiUnaryNandOp, "~&" },
  { vpiUnaryOrOp, "|" },
  { vpiUnaryNorOp, "~|" },
  { vpiUnaryXorOp, "^" },
  { vpiUnaryXNorOp, "~^" },
  { vpiSubOp, "-" },
  { vpiDivOp, "/" },
  { vpiModOp, "%" },
  { vpiEqOp, "==" },
  { vpiNeqOp, "!=" },
  { vpiCaseEqOp, "===" },
  { vpiCaseNeqOp, "!==" },
  { vpiGtOp, ">" },
  { vpiGeOp, ">=" },
  { vpiLtOp, "<" },
  { vpiLeOp, "<=" },
  { vpiLShiftOp, "<<" },
  { vpiRShiftOp, ">>" },
  { vpiAddOp, "+" },
  { vpiMultOp, "*" },
  { vpiLogAndOp, "&&" },
  { vpiLogOrOp, "||" },
  { vpiBitAndOp, "&" },
  { vpiBitOrOp, "|" },
  { vpiBitXorOp, "^" },
  { vpiBitXNorOp, "^~" },
  { vpiConditionOp, "?" },
  { vpiConcatOp, "{}" },
  { vpiMultiConcatOp, "{{}}" },
  { vpiEventOrOp, "or" },
  { vpiNullOp, "" },
  { vpiListOp, "," },
  { vpiMinTypMaxOp, ":" },
  { vpiPosedgeOp, "posedge " },
  { vpiNegedgeOp, "negedge " },
  { vpiArithLShiftOp, "<<<" },
  { vpiArithRShiftOp, ">>>" },
  { vpiPowerOp, "**" },
  { vpiImplyOp, "->" },
  { vpiNonOverlapImplyOp, "|=>" },
  { vpiOverlapImplyOp, "|->" },
  { vpiAcceptOnOp, "accept_on" },
  { vpiRejectOnOp, "reject_on" },
  { vpiSyncAcceptOnOp, "sync_accept_on" },
  { vpiSyncRejectOnOp, "sync_reject_on" },
  { vpiOverlapFollowedByOp, "overlapped followed_by" },
  { vpiNonOverlapFollowedByOp, "nonoverlapped followed_by" },
  { vpiNexttimeOp, "nexttime" },
  { vpiAlwaysOp, "always" },
  { vpiEventuallyOp, "eventually" },
  { vpiUntilOp, "until" },
  { vpiUntilWithOp, "until_with" },
  { vpiUnaryCycleDelayOp, "##" },
  { vpiCycleDelayOp, "##" },
  { vpiIntersectOp, "intersection" },
  { vpiFirstMatchOp, "first_match" },
  { vpiThroughoutOp, "throughout" },
  { vpiWithinOp, "within" },
  { vpiRepeatOp, "[=]" },
  { vpiConsecutiveRepeatOp, "[*]" },
  { vpiGotoRepeatOp, "[->]" },
  { vpiPostIncOp, "++" },
  { vpiPreIncOp, "++" },
  { vpiPostDecOp, "--" },
  { vpiPreDecOp, "--" },
  { vpiMatchOp, "match" },
  { vpiCastOp, "type'" },
  { vpiIffOp, "iff" },
  { vpiWildEqOp, "==?" },
  { vpiWildNeqOp, "!=?" },
  { vpiStreamLROp, "{>>}" },
  { vpiStreamRLOp, "{<<}" },
  { vpiMatchedOp, ".matched" },
  { vpiTriggeredOp, ".triggered" },
  { vpiAssignmentPatternOp, "'{}" },
  { vpiMultiAssignmentPatternOp, "{n{}}" },
  { vpiIfOp, "if" },
  { vpiIfElseOp, "if–else" },
  { vpiCompAndOp, "and" },
  { vpiCompOrOp, "or" },
  { vpiImpliesOp, "implies" },
  { vpiInsideOp, "inside" },
  { vpiTypeOp, "type" },
  { vpiAssignmentOp, "=" },
};

static const typespec_names_t kTypespecNames = {
  { uhdm::UhdmType::ArrayTypespec, "" },
  { uhdm::UhdmType::BitTypespec, "bit" },
  { uhdm::UhdmType::ByteTypespec, "byte" },
  { uhdm::UhdmType::ChandleTypespec, "" },
  { uhdm::UhdmType::ClassTypespec, "" },
  { uhdm::UhdmType::EnumTypespec, "" },
  { uhdm::UhdmType::EventTypespec, "" },
  { uhdm::UhdmType::ImportTypespec, "import" },
  { uhdm::UhdmType::IntTypespec, "int" },
  { uhdm::UhdmType::IntegerTypespec, "integer" },
  { uhdm::UhdmType::InterfaceTypespec, "" },
  { uhdm::UhdmType::LogicTypespec, "logic" },
  { uhdm::UhdmType::LongIntTypespec, "longint" },
  { uhdm::UhdmType::PackedArrayTypespec, "" },
  { uhdm::UhdmType::PropertyTypespec, "" },
  { uhdm::UhdmType::RealTypespec, "real" },
  { uhdm::UhdmType::SequenceTypespec, "" },
  { uhdm::UhdmType::ShortIntTypespec, "shortint" },
  { uhdm::UhdmType::ShortRealTypespec, "shortreal" },
  { uhdm::UhdmType::StringTypespec, "string" },
  { uhdm::UhdmType::StructTypespec, "" },
  { uhdm::UhdmType::TimeTypespec, "time" },
  { uhdm::UhdmType::TypeParameter, "" },
  { uhdm::UhdmType::UnionTypespec, "" },
  { uhdm::UhdmType::UnsupportedTypespec, "" },
  { uhdm::UhdmType::VoidTypespec, "void" },
};

static const variable_type_names_t kVariableTypeNames = {
 { uhdm::UhdmType::ArrayVar, "" },
 { uhdm::UhdmType::BitVar, "bit" },
 { uhdm::UhdmType::ByteVar, "byte" },
 { uhdm::UhdmType::ChandleVar, "" },
 { uhdm::UhdmType::ClassVar, "" },
 { uhdm::UhdmType::EnumVar, "" },
 { uhdm::UhdmType::IntVar, "int" },
 { uhdm::UhdmType::IntegerVar, "int" },
 { uhdm::UhdmType::LogicVar, "logic" },
 { uhdm::UhdmType::LongIntVar, "longint" },
 { uhdm::UhdmType::PackedArrayVar, "" },
 { uhdm::UhdmType::RealVar, "float" },
 { uhdm::UhdmType::RefVar, "" },
 { uhdm::UhdmType::ShortIntVar, "shortint" },
 { uhdm::UhdmType::ShortRealVar, "shortfloat" },
 { uhdm::UhdmType::StringVar, "string" },
 { uhdm::UhdmType::StructVar, "" },
 { uhdm::UhdmType::TimeVar, "" },
 { uhdm::UhdmType::UnionVar, "" },
 { uhdm::UhdmType::VarBit, "" },
};

static const edge_names_t kEdgeNames = {
  { vpiNoEdge, "" },
  { vpiPosedge, "posedge" },
  { vpiNegedge, "negedge" },
  { vpiAnyEdge, "posnegedge" },
};

static const always_type_names_t kAlwaysTypeNames = {
  { 1, "always" },
  { vpiAlwaysComb, "always_comb" },
  { vpiAlwaysFF, "" },
  { vpiAlwaysLatch, "" },
};

static const case_type_names_t kCaseTypeNames = {
  { vpiCaseExact, "case" },
  { vpiCaseX, "casex" },
  { vpiCaseZ, "casez" }
};

static const case_qualifier_names_t kCaseQualifierNames = {
  { vpiUniqueQualifier, "unique" },
  // { vpiNoQualifier, "" },
  { vpiPriorityQualifier, "priority" }
};
// clang-format on

class RoundTripTracer final : public uhdm::UhdmListener {
 public:
  explicit RoundTripTracer(const uhdm::Design *const design) : design(design) {}
  ~RoundTripTracer() final = default;

 public:
  const uhdm::Design *const design = nullptr;
  design_content_t contents;

 private:
  inline static std::string &strReplaceAll(std::string &arg,
                                           std::string_view what,
                                           std::string_view with) {
    size_t pos = 0;
    while ((pos = arg.find(what, pos)) != std::string::npos) {
      arg.replace(pos, what.length(), with);
      pos += with.length();
    }
    return arg;
  }

  void insert(const std::filesystem::path &filepath, size_t line,
              uint16_t column, std::string_view data) {
    assert(column < (uint16_t(~0) / 2));

    if (filepath.empty() || (line < 1) || (column < 1) || data.empty()) {
      return;
    }

    design_content_t::iterator it = contents.find(filepath);
    if (it == contents.end())
      it = contents.emplace(filepath, file_content_t()).first;

    file_content_t &content = it->second;
    if (content.size() < line) content.resize(line);
    --line;
    --column;
    if (content[line].length() < (column + data.length()))
      content[line].resize(column + data.length(), ' ');

    for (int32_t i = column, j = 0, n = data.length(); j < n; ++i, ++j) {
      if ((content[line][i] != kOverwriteMarker) &&
          (data[j] != kOverwriteMarker)) {
        if (data[j] == '\n') {
          insert(filepath, line + 2, 1, data.substr(j + 1));
          return;
        }

        if ((content[line][i] == ' ') || (content[line][i] == data[j])) {
          content[line][i] = data[j];
        } else {
          content[line][i] = kOverwriteMarker;
        }
      }
    }
  }

  void append(const std::filesystem::path &filepath, size_t line,
              std::string_view data) {
    if (filepath.empty() || (line < 1) || data.empty()) {
      return;
    }

    design_content_t::iterator it = contents.find(filepath);
    if (it == contents.end())
      it = contents.emplace(filepath, file_content_t()).first;

    file_content_t &content = it->second;
    if (content.size() < line) content.resize(line);
    --line;
    content[line].reserve(content[line].size() + data.size());

    for (char c : data) {
      if (c == kOverwriteMarker) {
        content[line].push_back(' ');
      } else {
        content[line].push_back(c);
      }
    }
  }

  inline static bool isModuleDefinition(const uhdm::Module *const mdl) {
    return ((mdl->getParent() == nullptr) ||
            (mdl->getParent()->getUhdmType() != uhdm::UhdmType::Module)) &&
           mdl->getName().empty();
  }

  inline static bool isInterfaceDefinition(const uhdm::Interface *const mdl) {
    return ((mdl->getParent() == nullptr) ||
            (mdl->getParent()->getUhdmType() != uhdm::UhdmType::Interface)) &&
           mdl->getName().empty();
  }

  inline bool isWalkingModuleDefinition() const {
    for (any_stack_t::const_reverse_iterator it = m_callstack.rbegin(),
                                             rend = m_callstack.rend();
         it != rend; ++it) {
      const uhdm::Any *const any = *it;
      if (any->getUhdmType() == uhdm::UhdmType::Module) {
        return isModuleDefinition(static_cast<const uhdm::Module *>(any));
      }
    }
    return false;
  }

  inline std::string formatName(std::string_view varg) const {
    std::string sarg(varg);
    size_t pos1 = sarg.find("::");
    if (pos1 != std::string::npos) {
      sarg = sarg.substr(pos1 + 2);
    }

    size_t pos2 = sarg.find("work@");
    if (pos2 != std::string::npos) {
      sarg = sarg.substr(pos2 + 5);
    }
    return sarg;
  }

  std::string formatValue(std::string_view arg, bool decorate = true) const {
    constexpr std::string_view prefixes[] = {"\"", "", "", ""};
    constexpr std::string_view keywords[] = {
        "STRING:", "UINT:", "BIN:", "INT:"};
    constexpr std::string_view suffixes[] = {"\"", "", "'b1", ""};
    constexpr int32_t count = sizeof(keywords) / sizeof(keywords[0]);

    std::string sarg(arg);
    for (int32_t i = 0; i < count; ++i) {
      if (arg.find(keywords[i]) == 0) {
        const std::string value = sarg.substr(keywords[i].length());
        return decorate
                   ? sarg.assign(prefixes[i]).append(value).append(suffixes[i])
                   : value;
      }
    }

    return sarg;
  }

  inline std::string getTypespecName(const uhdm::Typespec *const object) {
    constexpr std::string_view keyword = "unsigned";

    if (const uhdm::RefTypespec *const rt =
            ((uhdm::TypedefTypespec *)object)->getTypedefAlias()) {
      if (const uhdm::Typespec *const alias = rt->getActual()) {
        return getTypespecName(alias);
      }
    }

    const std::string_view name = object->getName();
    if (!name.empty()) return formatName(name);

    std::string text;
    typespec_names_t::const_iterator it =
        kTypespecNames.find(object->getUhdmType());
    if (it != kTypespecNames.end()) {
      text.append(it->second);
      if (object->getUhdmType() != uhdm::UhdmType::LogicTypespec) {
        text.append(1, kOverwriteMarker);
      }
    }

    switch (object->getUhdmType()) {
      case uhdm::UhdmType::ByteTypespec: {
        if (!static_cast<const uhdm::ByteTypespec *>(object)->getSigned()) {
          text.append(keyword);
        }
      } break;

      case uhdm::UhdmType::IntTypespec: {
        if (!static_cast<const uhdm::IntTypespec *>(object)->getSigned()) {
          text.append(keyword);
        }
      } break;

      case uhdm::UhdmType::IntegerTypespec: {
        if (!static_cast<const uhdm::IntegerTypespec *>(object)->getSigned()) {
          text.append(keyword);
        }
      } break;

      case uhdm::UhdmType::LongIntTypespec: {
        if (!static_cast<const uhdm::LongIntTypespec *>(object)->getSigned()) {
          text.append(keyword);
        }
      } break;

      case uhdm::UhdmType::ShortIntTypespec: {
        if (!static_cast<const uhdm::ShortIntTypespec *>(object)->getSigned()) {
          text.append(keyword);
        }
      } break;

      case uhdm::UhdmType::BitTypespec:
      case uhdm::UhdmType::LogicTypespec: {
        const uhdm::RangeCollection *const ranges =
            static_cast<const uhdm::LogicTypespec *>(object)->getRanges();
        if ((ranges != nullptr) && !ranges->empty()) {
          text.resize(object->getEndColumn() - object->getStartColumn(),
                      kOverwriteMarker);
        }
      } break;

      default:
        break;
    }

    return text;
  }

  void enterVariables_(const uhdm::Variables *const object) {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "automatic";
    constexpr std::string_view keyword2 = "unsigned";
    const std::filesystem::path &filepath = object->getFile();

    std::string prefix;
    const std::string name = formatName(object->getName());

    const uhdm::Typespec *ts = nullptr;
    if (const uhdm::RefTypespec *const rt = object->getTypespec()) {
      ts = rt->getActual();
    }

    if (ts != nullptr) {
      prefix.append(getTypespecName(ts));
      if (ts->getStartColumn() != 0) {
        insert(filepath, ts->getStartLine(), ts->getStartColumn(), prefix);
        prefix.clear();
      } else {
        prefix.append(1, kOverwriteMarker);
      }
    } else if (object->getUhdmType() == uhdm::UhdmType::ArrayVar) {
      const uhdm::VariablesCollection *const variables =
          static_cast<const uhdm::ArrayVar *>(object)->getVariables();
      if ((variables != nullptr) && !variables->empty()) {
        const uhdm::Variables *const variable = variables->at(0);
        if (const uhdm::RefTypespec *const rt = variable->getTypespec()) {
          ts = rt->getActual();
        }
        if (ts != nullptr) {
          prefix.append(getTypespecName(ts));
          if (ts->getStartColumn() != 0) {
            insert(filepath, ts->getStartLine(), ts->getStartColumn(), prefix);
            prefix.clear();
          } else {
            prefix.append(1, kOverwriteMarker);
          }
        }
      }
    } else {
      if (object->getAutomatic()) {
        prefix.append(keyword1).append(1, kOverwriteMarker);
      }

      variable_type_names_t::const_iterator it =
          kVariableTypeNames.find(object->getUhdmType());
      if (it != kVariableTypeNames.end()) {
        prefix.append(it->second);
      }

      if (object->getUhdmType() == uhdm::UhdmType::LogicVar) {
        const uhdm::RangeCollection *const ranges =
            static_cast<const uhdm::LogicVar *>(object)->getRanges();
        if ((ranges != nullptr) && !ranges->empty()) {
          const uhdm::Range *const range0 = ranges->front();
          const uhdm::Range *const rangeN = ranges->back();
          prefix.append(rangeN->getEndColumn() - range0->getStartColumn(),
                        kOverwriteMarker);
        }
      } else if (!object->getSigned()) {
        switch (object->getUhdmType()) {
          case uhdm::UhdmType::ByteVar:
          case uhdm::UhdmType::IntVar:
          case uhdm::UhdmType::IntegerVar:
          case uhdm::UhdmType::LongIntVar:
          case uhdm::UhdmType::ShortIntVar: {
            prefix.append(keyword2);
          } break;
          default:
            break;
        }
      }
    }

    if (!prefix.empty()) prefix.append(1, kOverwriteMarker);

    std::string text = prefix;
    if (name.empty()) {
      prefix.clear();
    } else {
      text.append(name);
    }

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);

    if (const uhdm::Expr *const expr = object->getExpr()) {
      insert(filepath, expr->getStartLine(), expr->getStartColumn() - 1, "=");
    }
  }

  void enterTypespec(const uhdm::Typespec *const object) {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "unsigned";

    const std::filesystem::path &filepath = object->getFile();

    const uhdm::Typespec *typespec = object;
    if (object->getUhdmType() == uhdm::UhdmType::ArrayTypespec) {
      if (const uhdm::RefTypespec *const element_typespec =
              static_cast<const uhdm::ArrayTypespec *>(object)
                  ->getElemTypespec()) {
        typespec = element_typespec->getActual();
      }
    } else if (object->getUhdmType() == uhdm::UhdmType::PackedArrayTypespec) {
      if (const uhdm::RefTypespec *const element_typespec =
              static_cast<const uhdm::PackedArrayTypespec *>(object)
                  ->getElemTypespec()) {
        typespec = element_typespec->getActual();
      }
    }

    if (typespec == nullptr) return;

    std::string text(typespec->getName());
    if (text.empty()) {
      typespec_names_t::const_iterator it =
          kTypespecNames.find(typespec->getUhdmType());
      if (it != kTypespecNames.end()) {
        text.assign(it->second);
      }
    } else {
      text = formatName(text);
    }

    switch (typespec->getUhdmType()) {
      case uhdm::UhdmType::TypedefTypespec: {
        const uhdm::TypedefTypespec *const struct_typespec =
            static_cast<const uhdm::TypedefTypespec *>(typespec);
        if (const uhdm::RefTypespec *const rt =
                struct_typespec->getTypedefAlias()) {
          if (const uhdm::Typespec *const alias = rt->getActual()) {
            text = formatName(alias->getName());
          }
        }
      } break;

      case uhdm::UhdmType::ByteTypespec: {
        if (!static_cast<const uhdm::ByteTypespec *>(typespec)->getSigned()) {
          if (!text.empty()) text.append(1, kOverwriteMarker);
          text.append(keyword);
        }
      } break;

      case uhdm::UhdmType::IntTypespec: {
        if (!static_cast<const uhdm::IntTypespec *>(typespec)->getSigned()) {
          if (!text.empty()) text.append(1, kOverwriteMarker);
          text.append(keyword);
        }
      } break;

      case uhdm::UhdmType::IntegerTypespec: {
        if (!static_cast<const uhdm::IntegerTypespec *>(typespec)
                 ->getSigned()) {
          if (!text.empty()) text.append(1, kOverwriteMarker);
          text.append(keyword);
        }
      } break;

      case uhdm::UhdmType::LongIntTypespec: {
        if (!static_cast<const uhdm::LongIntTypespec *>(typespec)
                 ->getSigned()) {
          if (!text.empty()) text.append(1, kOverwriteMarker);
          text.append(keyword);
        }
      } break;

      case uhdm::UhdmType::ShortIntTypespec: {
        if (!static_cast<const uhdm::ShortIntTypespec *>(typespec)
                 ->getSigned()) {
          if (!text.empty()) text.append(1, kOverwriteMarker);
          text.append(keyword);
        }
      } break;

      default:
        break;
    }

    insert(filepath, typespec->getStartLine(), typespec->getStartColumn(),
           text);
  }

 public:
  void enterAny(const uhdm::Any *const object, uint32_t vpiRelation) override {
    if ((object->getUhdmType() == uhdm::UhdmType::Package) &&
        (static_cast<const uhdm::Package *>(object)->getName() == "builtin")) {
      // Ignore the built-in package
      m_visited.insert(object);
      return;
    }

    const uhdm::Any *parent = object->getParent();
    while (parent != nullptr) {
      if ((parent->getUhdmType() == uhdm::UhdmType::Package) &&
          static_cast<const uhdm::Package *>(parent)->getTop()) {
        m_visited.insert(object);
        return;
      }

      if ((parent->getUhdmType() == uhdm::UhdmType::Module) &&
          static_cast<const uhdm::Module *>(parent)->getTop()) {
        m_visited.insert(object);
        return;
      }

      parent = parent->getParent();
    }
  }

  void enterAttribute(const uhdm::Attribute *const object,
                      uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "(* ";
    constexpr std::string_view keyword2 = " *)";

    const std::filesystem::path &filepath = object->getFile();

    const std::string name = formatName(object->getName());
    if (name.empty()) return;

    std::string text;
    text.append(keyword1).append(name);
    std::string value = formatValue(object->getValue());
    if (!value.empty()) {
      text.append("=").append(value);
    }
    text.append(keyword2);
    insert(filepath, object->getStartLine(),
           object->getStartColumn() - keyword1.length(), text);
  }

  void enterVirtualInterfaceVar(const uhdm::VirtualInterfaceVar *const object,
                                uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterLetDecl(const uhdm::LetDecl *const object,
                    uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterAlways(const uhdm::Always *const object,
                   uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    always_type_names_t::const_iterator it =
        kAlwaysTypeNames.find(object->getAlwaysType());

    const std::filesystem::path &filepath = object->getFile();
    if (it != kAlwaysTypeNames.end()) {
      insert(filepath, object->getStartLine(), object->getStartColumn(),
             it->second);
    }
  }

  void enterFinalStmt(const uhdm::FinalStmt *const object,
                      uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterInitial(const uhdm::Initial *const object,
                    uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "initial";

    const std::filesystem::path &filepath = object->getFile();
    insert(filepath, object->getStartLine(), object->getStartColumn(), keyword);
  }

  void enterDelayControl(const uhdm::DelayControl *const object,
                         uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();
    insert(filepath, object->getStartLine(), object->getStartColumn(),
           object->getVpiDelay());
  }

  void enterDelayTerm(const uhdm::DelayTerm *const object,
                      uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterEventControl(const uhdm::EventControl *const object,
                         uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    if (const uhdm::Any *const condition = object->getCondition()) {
      insert(filepath, condition->getStartLine(),
             condition->getStartColumn() - 2, "@(");
      insert(filepath, condition->getEndLine(), condition->getEndColumn(), ")");
    } else {
      insert(filepath, object->getStartLine(), object->getStartColumn(),
             "@(*)");
    }
  }

  void enterRepeatControl(const uhdm::RepeatControl *const object,
                          uint32_t vpiRelation) final {}

  void enterBegin(const uhdm::Begin *const object, uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "begin";
    constexpr std::string_view keyword2 = "end";

    bool hasBeginEnd = true;
    if (const uhdm::Any *const parent = object->getParent()) {
      if ((parent->getUhdmType() == uhdm::UhdmType::Function) ||
          (parent->getUhdmType() == uhdm::UhdmType::Task)) {
        hasBeginEnd = false;
      }
    }

    const uhdm::AnyCollection *const stmts = object->getStmts();
    if ((stmts == nullptr) || (stmts->size() <= 1)) hasBeginEnd = false;

    if (hasBeginEnd) {
      const std::filesystem::path &filepath = object->getFile();
      insert(filepath, object->getStartLine(), object->getStartColumn(),
             keyword1);
      insert(filepath, object->getEndLine(),
             object->getEndColumn() - keyword2.length(), keyword2);
    }
  }

  void enterForkStmt(const uhdm::ForkStmt *const object,
                     uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "fork";
    constexpr std::string_view keyword2 = "join";

    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           keyword1);
    insert(filepath, object->getEndLine(),
           object->getEndColumn() - keyword2.length(), keyword2);
  }

  void enterForStmt(const uhdm::ForStmt *const object,
                    uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "for";
    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(), keyword);
    insert(filepath, object->getStartLine(), object->getEndColumn(), "(");

    const uhdm::AnyCollection *const inits = object->getForInitStmts();
    if ((inits != nullptr) && !inits->empty()) {
      for (int32_t i = 0, ni = inits->size() - 1; i < ni; ++i) {
        const uhdm::Any *const init = inits->at(i);
        insert(filepath, init->getStartLine(), init->getEndColumn(), ",");
      }

      const uhdm::Any *const initN = inits->back();
      insert(filepath, initN->getStartLine(), initN->getEndColumn(), ";");
    } else if (const uhdm::Any *const init = object->getForInitStmt()) {
      insert(filepath, init->getStartLine(), init->getEndColumn(), ";");
    }

    if (const uhdm::Any *const condition = object->getCondition()) {
      insert(filepath, condition->getStartLine(), condition->getEndColumn(),
             ";");
    }

    const uhdm::AnyCollection *const incs = object->getForIncStmts();
    if ((incs != nullptr) && !incs->empty()) {
      for (int32_t i = 0, ni = incs->size() - 1; i < ni; ++i) {
        const uhdm::Any *const inc = incs->at(i);
        insert(filepath, inc->getStartLine(), inc->getEndColumn(), ",");
      }

      const uhdm::Any *const incN = incs->back();
      insert(filepath, incN->getStartLine(), incN->getEndColumn(), ")");
    } else if (const uhdm::Any *const inc = object->getForIncStmt()) {
      insert(filepath, inc->getStartLine(), inc->getEndColumn(), ")");
    }
  }

  void enterIfStmt(const uhdm::IfStmt *const object,
                   uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "if";

    const std::filesystem::path &filepath = object->getFile();
    const uhdm::Expr *const condition = object->getCondition();

    insert(filepath, object->getStartLine(), object->getStartColumn(), keyword);
    insert(filepath, condition->getStartLine(), condition->getStartColumn() - 1,
           "(");
    insert(filepath, condition->getEndLine(), condition->getEndColumn(), ")");
  }

  void enterEventStmt(const uhdm::EventStmt *const object,
                      uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "->";
    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    text.append(keyword)
        .append(1, kOverwriteMarker)
        .append(formatName(object->getName()))
        .append(";");
    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
  }

  void enterThread(const uhdm::Thread *const object,
                   uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterForeverStmt(const uhdm::ForeverStmt *const object,
                        uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "forever";

    const std::filesystem::path &filepath = object->getFile();
    insert(filepath, object->getStartLine(), object->getStartColumn(), keyword);
  }

  void enterWaitStmt(const uhdm::WaitStmt *const object,
                     uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "wait";
    const std::filesystem::path &filepath = object->getFile();
    const uhdm::Any *const condition = object->getCondition();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           keyword1);
    insert(filepath, condition->getStartLine(), condition->getStartColumn() - 1,
           "(");
    insert(filepath, condition->getEndLine(), condition->getEndColumn(), ");");
  }

  void enterWaitFork(const uhdm::WaitFork *const object,
                     uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterOrderedWait(const uhdm::OrderedWait *const object,
                        uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterDisable(const uhdm::Disable *const object,
                    uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "disable";
    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    text.append(keyword1).append(1, kOverwriteMarker);

    if (const uhdm::Expr *const expr = object->getExpr<uhdm::Expr>()) {
      text.append(expr->getName());
    } else if (const uhdm::Scope *const scope =
                   object->getExpr<uhdm::Scope>()) {
      text.append(scope->getName());
    }

    text.append(";");

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
  }

  void enterDisableFork(const uhdm::DisableFork *const object,
                        uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "disable fork;";
    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           keyword1);
  }

  void enterContinueStmt(const uhdm::ContinueStmt *const object,
                         uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "continue;";
    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           keyword1);
  }

  void enterBreakStmt(const uhdm::BreakStmt *const object,
                      uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "break;";
    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           keyword1);
  }

  void enterReturnStmt(const uhdm::ReturnStmt *const object,
                       uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();
    insert(filepath, object->getStartLine(), object->getStartColumn(),
           "return");
  }

  void enterWhileStmt(const uhdm::WhileStmt *const object,
                      uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "while";
    const std::filesystem::path &filepath = object->getFile();
    const uhdm::Any *const condition = object->getCondition();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           keyword1);
    insert(filepath, condition->getStartLine(), condition->getStartColumn() - 1,
           "(");
    insert(filepath, condition->getEndLine(), condition->getEndColumn(), ")");
  }

  void enterRepeat(const uhdm::Repeat *const object,
                   uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "repeat";
    const std::filesystem::path &filepath = object->getFile();
    const uhdm::Any *const condition = object->getCondition();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           keyword1);
    insert(filepath, condition->getStartLine(), condition->getStartColumn() - 1,
           "(");
    insert(filepath, condition->getEndLine(), condition->getEndColumn(), ")");
  }

  void enterDoWhile(const uhdm::DoWhile *const object,
                    uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "do";
    constexpr std::string_view keyword2 = "while";

    const std::filesystem::path &filepath = object->getFile();

    const uhdm::Expr *const condition = object->getCondition();

    std::string text;
    text.append(keyword2).append("(");

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           keyword1);
    insert(filepath, condition->getStartLine(),
           condition->getStartColumn() - text.length(), text);
    insert(filepath, condition->getEndLine(), condition->getEndColumn(), ");");
  }

  void enterIfElse(const uhdm::IfElse *const object,
                   uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "if";
    constexpr std::string_view keyword2 = "else";

    const std::filesystem::path &filepath = object->getFile();

    const uhdm::Any *const ifStmt = object->getStmt();
    const uhdm::Any *const elseStmt = object->getElseStmt();
    const uhdm::Expr *const condition = object->getCondition();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           keyword1);
    if (condition->getStartColumn() > 0)
      insert(filepath, condition->getStartLine(),
             condition->getStartColumn() - 1, "(");
    insert(filepath, condition->getEndLine(), condition->getEndColumn(), ")");

    // Check if the "else" keyword is on its own line
    // If col is 0 then else is in previous line.
    int32_t col = elseStmt->getStartColumn() - keyword2.length() - 1;
    if (((elseStmt->getStartLine() - ifStmt->getEndLine()) >= 2) || (col < 1)) {
      insert(filepath, ifStmt->getEndLine() + 1, object->getStartColumn(),
             keyword2);
    } else {
      insert(filepath, elseStmt->getStartLine(),
             elseStmt->getStartColumn() - keyword2.length() - 1, keyword2);
    }
  }

  void enterCaseStmt(const uhdm::CaseStmt *const object,
                     uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "endcase";
    // constexpr std::string_view keyword2 = "inside";

    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    case_qualifier_names_t::const_iterator it1 =
        kCaseQualifierNames.find(object->getQualifier());
    if (it1 != kCaseQualifierNames.end()) {
      text.append(it1->second).append(1, kOverwriteMarker);
    }

    case_type_names_t::const_iterator it2 =
        kCaseTypeNames.find(object->getCaseType());
    if (it2 != kCaseTypeNames.end()) {
      text.append(it2->second);
    }

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
    insert(filepath, object->getEndLine(),
           object->getEndColumn() - keyword1.length(), keyword1);

    const uhdm::Expr *const condition = object->getCondition();
    insert(filepath, condition->getStartLine(), condition->getStartColumn() - 1,
           "(");
    insert(filepath, condition->getEndLine(), condition->getEndColumn(), ")");
  }

  void enterForce(const uhdm::Force *const object, uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "force";

    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(), keyword);

    const uhdm::Any *const lhs = object->getLhs();
    const uhdm::Any *const rhs = object->getRhs();
    if ((lhs != nullptr) && (rhs != nullptr)) {
      insert(filepath, rhs->getStartLine(), rhs->getStartColumn() - 1, "=");
    }
  }

  void enterAssignStmt(const uhdm::AssignStmt *const object,
                       uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    // constexpr std::string_view keyword1 = "assign";

    const std::filesystem::path &filepath = object->getFile();

    // TODO(HS): This should basically be a check for implicit vs. explicit
    // but, unfortunately, there is nothing in the model to identify that.
    // if ((object->getParent() == nullptr) ||
    //     (object->getParent()->getUhdmType() != uhdm::UhdmType::ForStmt)) {
    //   insert(filepath, object->getStartLine(), object->getStartColumn(),
    //   keyword1);
    // }

    const uhdm::Any *const lhs = object->getLhs();
    const uhdm::Any *const rhs = object->getRhs();
    if ((lhs != nullptr) && (rhs != nullptr)) {
      insert(filepath, rhs->getStartLine(), rhs->getStartColumn() - 1, "=");
    }
  }

  void enterDeassign(const uhdm::Deassign *const object,
                     uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "deassign";

    const std::filesystem::path &filepath = object->getFile();

    if (object->getLhs() != nullptr) {
      insert(filepath, object->getStartLine(), object->getStartColumn(),
             keyword);
    }
  }

  void enterRelease(const uhdm::Release *const object,
                    uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "release";

    const std::filesystem::path &filepath = object->getFile();

    if (object->getLhs() != nullptr) {
      insert(filepath, object->getStartLine(), object->getStartColumn(),
             keyword);
    }
  }

  void enterNullStmt(const uhdm::NullStmt *const object,
                     uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterExpectStmt(const uhdm::ExpectStmt *const object,
                       uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "expect";
    constexpr std::string_view keyword2 = ");";

    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    text.append(keyword1).append("(");

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
    insert(filepath, object->getEndLine(),
           object->getEndColumn() - keyword2.length(), keyword2);
  }

  void enterForeachStmt(const uhdm::ForeachStmt *const object,
                        uint32_t vpiRelation) final {
    // tests\DollarRoot, tests\UnitForeach
    // @todo: variables info is missing while decoding in foreach.
    // Need to revisit later.

    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "foreach";
    constexpr std::string_view keyword2 = ")";

    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    text.append(keyword1).append("(");
    insert(filepath, object->getStartLine(), object->getStartColumn(), text);

    if (const uhdm::Any *const stmt = object->getStmt()) {
      insert(filepath, stmt->getStartLine(),
             stmt->getStartColumn() - keyword2.length() - 1, keyword2);
    }
  }

  void enterGenScope(const uhdm::GenScope *const object,
                     uint32_t vpiRelation) final {
    // tests\BindStmt, tests\Bindings, tests\ArianeElab
  }

  void enterGenVar(const uhdm::GenVar *const object,
                   uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterGenScopeArray(const uhdm::GenScopeArray *const object,
                          uint32_t vpiRelation) final {
    // tests\BindStmt, tests\Bindings, tests\ArianeElab, tests\Cell ..
  }

  void enterAssert(const uhdm::Assert *const object,
                   uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "assert";
    constexpr std::string_view keyword2 = "else";

    const std::filesystem::path &filepath = object->getFile();
    const std::string name = formatName(object->getName());

    std::string prefix;
    if (!name.empty()) {
      prefix.append(name).append(":");
    }

    std::string text = prefix;
    text.append(keyword1);

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
    insert(filepath, object->getStartLine(), object->getEndColumn() - 1, ";");

    if (object->getElseStmt() != nullptr) {
      const uhdm::Any *const property = object->getProperty();
      insert(filepath, property->getEndLine(), property->getEndColumn() + 1,
             keyword2);
    }
  }

  void enterCover(const uhdm::Cover *const object, uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterAssume(const uhdm::Assume *const object,
                   uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "assume";
    constexpr std::string_view keyword2 = "else";

    const std::filesystem::path &filepath = object->getFile();
    const std::string name = formatName(object->getName());

    std::string prefix;
    if (!name.empty()) {
      prefix.append(name).append(": ");
    }

    std::string text = prefix;
    text.append(keyword1);

    insert(filepath, object->getStartLine(),
           object->getStartColumn() - prefix.length(), text);

    if (object->getStmt() != nullptr) {
      const uhdm::Any *const property = object->getProperty();
      insert(filepath, property->getEndLine(), property->getEndColumn() + 1,
             keyword2);
    }
  }

  void enterRestrict(const uhdm::Restrict *const object,
                     uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterImmediateAssert(const uhdm::ImmediateAssert *const object,
                            uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "assert";

    const std::filesystem::path &filepath = object->getFile();
    const std::string name = formatName(object->getName());

    std::string text;
    if (!name.empty()) {
      text.append(name).append(":");
    }
    text.append(keyword).append("(");

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
    insert(filepath, object->getEndLine(), object->getEndColumn() - 2, ");");
  }

  void enterImmediateAssume(const uhdm::ImmediateAssume *const object,
                            uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterImmediateCover(const uhdm::ImmediateCover *const object,
                           uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterCaseItem(const uhdm::CaseItem *const object,
                     uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "default:";

    const std::filesystem::path &filepath = object->getFile();

    const uhdm::AnyCollection *const exprs = object->getExprs();
    if ((exprs != nullptr) && !exprs->empty()) {
      for (int32_t i = 0, ni = exprs->size() - 1; i < ni; ++i) {
        const uhdm::Any *const expr = exprs->at(i);
        insert(filepath, expr->getEndLine(), expr->getEndColumn(), ",");
      }

      const uhdm::Any *const exprN = exprs->back();
      insert(filepath, exprN->getEndLine(), exprN->getEndColumn(), ":");
    } else {
      insert(filepath, object->getStartLine(), object->getStartColumn(),
             keyword);
    }
  }

  void enterAssignment(const uhdm::Assignment *const object,
                       uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "=";
    constexpr std::string_view keyword2 = "<";

    const std::filesystem::path &filepath = object->getFile();

    const uhdm::Any *const rhs = object->getRhs();
    uint32_t column = (rhs != nullptr) ? rhs->getStartColumn() : 0;
    // In case of delay, might be need to add one space.
    // Will revisit once get any test file.
    if (const uhdm::Any *const delayCtrl = object->getDelayControl()) {
      column = delayCtrl->getStartColumn();
    }

    std::string text;
    op_type_names_t::const_iterator it = kOpTypeNames.find(object->getOpType());
    if ((it != kOpTypeNames.end()) &&
        (object->getOpType() != vpiAssignmentOp)) {
      text.assign(it->second);
    }
    if (!object->getBlocking()) {
      text.append(keyword2);
    }
    text.append(keyword1);
    if (rhs != nullptr) {
      insert(filepath, rhs->getEndLine(), column - text.length(), text);
    }
  }

  void enterAnyPattern(const uhdm::AnyPattern *const object,
                       uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterTaggedPattern(const uhdm::TaggedPattern *const object,
                          uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    const uhdm::Typespec *typespec = nullptr;
    if (const uhdm::RefTypespec *const rt = object->getTypespec()) {
      typespec = rt->getActual();
    }

    const uhdm::Any *const pattern = object->getPattern();
    if ((typespec != nullptr) && (pattern != nullptr)) {
      std::string value;
      switch (typespec->getUhdmType()) {
        case uhdm::UhdmType::IntTypespec:
          value = static_cast<const uhdm::IntTypespec *>(typespec)->getValue();
          break;
        case uhdm::UhdmType::IntegerTypespec:
          value = static_cast<const uhdm::IntTypespec *>(typespec)->getValue();
          break;
        default:
          break;
      };

      if (value.empty()) {
        insert(filepath, typespec->getStartLine(), typespec->getStartColumn(),
               getTypespecName(typespec));
      } else {
        value = formatValue(value, false);
        insert(filepath, typespec->getStartLine(), typespec->getStartColumn(),
               value);
      }

      insert(filepath, typespec->getStartLine(), typespec->getEndColumn(), ":");

      listenAny(pattern);
      m_visited.insert(object);
    }
  }

  void enterStructPattern(const uhdm::StructPattern *const object,
                          uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterUnsupportedExpr(const uhdm::UnsupportedExpr *const object,
                            uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterUnsupportedStmt(const uhdm::UnsupportedStmt *const object,
                            uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterSequenceInst(const uhdm::SequenceInst *const object,
                         uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    text.append(formatName(object->getName())).append("(");

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
    insert(filepath, object->getEndLine(), object->getEndColumn() - 1, ")");

    const uhdm::AnyCollection *const args = object->getArguments();
    if ((args != nullptr) && !args->empty()) {
      for (int32_t i = 0, n = args->size() - 1; i < n; ++i) {
        uhdm::AnyCollection::const_reference arg = args->at(i);
        insert(filepath, arg->getStartLine(), arg->getEndColumn(), ",");
      }
    }
  }

  void enterSeqFormalDecl(const uhdm::SeqFormalDecl *const object,
                          uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterSequenceDecl(const uhdm::SequenceDecl *const object,
                         uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterPropFormalDecl(const uhdm::PropFormalDecl *const object,
                           uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterPropertyInst(const uhdm::PropertyInst *const object,
                         uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    text.append(formatName(object->getName())).append("(");

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
    insert(filepath, object->getEndLine(), object->getEndColumn() - 1, ")");

    const uhdm::AnyCollection *const args = object->getArguments();
    if ((args != nullptr) && !args->empty()) {
      for (int32_t i = 0, n = args->size() - 1; i < n; ++i) {
        uhdm::AnyCollection::const_reference arg = args->at(i);
        insert(filepath, arg->getStartLine(), arg->getEndColumn(), ",");
      }
    }
  }

  void enterPropertySpec(const uhdm::PropertySpec *const object,
                         uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    // constexpr std::string_view keyword1 = "property(";
    constexpr std::string_view keyword2 = "@(";
    constexpr std::string_view keyword3 = ")";
    // constexpr std::string_view keyword4 = ")";

    const std::filesystem::path &filepath = object->getFile();

    // insert(filepath, object->getStartLine(),
    //        object->getStartColumn() - keyword1.length(), keyword1);
    // insert(filepath, object->getEndLine(), object->getEndColumn(),
    //        keyword4);

    if (const uhdm::Expr *const clockingEvent = object->getClockingEvent()) {
      insert(filepath, clockingEvent->getStartLine(),
             clockingEvent->getStartColumn() - keyword2.length(), keyword2);
      insert(filepath, clockingEvent->getEndLine(),
             clockingEvent->getEndColumn(), keyword3);
    }
  }

  void enterPropertyDecl(const uhdm::PropertyDecl *const object,
                         uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterClockedProperty(const uhdm::ClockedProperty *const object,
                            uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterCasePropertyItem(const uhdm::CasePropertyItem *const object,
                             uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterCaseProperty(const uhdm::CaseProperty *const object,
                         uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterMulticlockSequenceExpr(
      const uhdm::MulticlockSequenceExpr *const object,
      uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterClockedSeq(const uhdm::ClockedSeq *const object,
                       uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterConstant(const uhdm::Constant *const object,
                     uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    std::string text = formatValue(object->getDecompile());
    if (object->getConstType() == vpiStringConst) {
      if ((text.size() < 2) || (text.front() != '\"') ||
          (text.back() != '\"')) {
        const std::string tmp_text = text;
        text.assign("\"").append(tmp_text).append("\"");
      }
    }
    insert(filepath, object->getStartLine(), object->getStartColumn(), text);

    if (const uhdm::RefTypespec *const rt = object->getTypespec()) {
      if (const uhdm::Typespec *const typespec = rt->getActual()) {
        m_visited.insert(typespec);
      }
    }
  }

  void enterLetExpr(const uhdm::LetExpr *const object,
                    uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterOperation(const uhdm::Operation *const object,
                      uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    op_type_names_t::const_iterator it = kOpTypeNames.find(object->getOpType());
    if (it == kOpTypeNames.end()) return;

    const uhdm::AnyCollection *const operands = object->getOperands();
    if ((operands == nullptr) || operands->empty()) return;

    const std::filesystem::path &filepath = object->getFile();

    switch (object->getOpType()) {
      case vpiConditionOp: {
        const uhdm::Any *const operand0 = operands->at(0);
        const uhdm::Any *const operand1 = operands->at(1);
        insert(filepath, operand0->getEndLine(), operand0->getEndColumn(),
               it->second);
        insert(filepath, operand1->getEndLine(), operand1->getEndColumn(), ":");
      } break;

      case vpiMinTypMaxOp:
      case vpiListOp: {
        for (int32_t i = 0, n = operands->size() - 1; i < n; ++i) {
          uhdm::AnyCollection::const_reference operand = operands->at(i);
          insert(filepath, operand->getEndLine(), operand->getEndColumn(),
                 it->second);
        }
      } break;

      case vpiConcatOp: {
        insert(filepath, object->getStartLine(), object->getStartColumn(), "{");
        uhdm::AnyCollection ordered(operands->begin(), operands->end());
        if (object->getReordered()) {
          std::stable_sort(
              ordered.begin(), ordered.end(),
              [](const uhdm::Any *const lhs, const uhdm::Any *const rhs) {
                int32_t r = lhs->getStartLine() - rhs->getStartLine();
                if (r != 0) return r < 0;

                r = lhs->getStartColumn() - rhs->getStartColumn();
                if (r != 0) return r < 0;

                r = lhs->getEndLine() - rhs->getEndLine();
                if (r != 0) return r < 0;

                r = lhs->getEndColumn() - rhs->getEndColumn();
                return r < 0;
              });
        }

        for (int32_t i = 0, ni = ordered.size() - 1; i < ni; ++i) {
          const uhdm::Any *const operand = ordered[i];
          insert(filepath, operand->getEndLine(), operand->getEndColumn(), ",");
        }
        insert(filepath, object->getEndLine(), object->getEndColumn() - 1, "}");
      } break;

      case vpiMultiConcatOp: {
        insert(filepath, object->getStartLine(), object->getStartColumn(), "{");
        insert(filepath, object->getEndLine(), object->getEndColumn() - 1, "}");
      } break;

      case vpiMultiAssignmentPatternOp: {
        insert(filepath, object->getStartLine(), object->getStartColumn(),
               "'{");
        insert(filepath, object->getEndLine(), object->getEndColumn() - 1,
               "};");
      } break;

      case vpiAssignmentPatternOp: {
        insert(filepath, object->getStartLine(), object->getStartColumn(),
               "'{");
        for (int32_t i = 0, ni = operands->size() - 1; i < ni; ++i) {
          const uhdm::Any *const operand = operands->at(i);
          insert(filepath, operand->getEndLine(), operand->getEndColumn(), ",");
        }
        insert(filepath, object->getEndLine(), object->getEndColumn() - 1,
               "};");
      } break;

      case vpiPostIncOp: {
        const uhdm::Any *const operand0 = operands->at(0);
        insert(filepath, operand0->getEndLine(), operand0->getEndColumn(),
               it->second);
      } break;

      case vpiEqOp: {
        const uhdm::Any *const operand1 = operands->at(1);
        insert(filepath, operand1->getStartLine(),
               operand1->getStartColumn() - it->second.length(), it->second);
      } break;

      case vpiEventOrOp: {
        const uhdm::Any *const operand0 = operands->at(0);
        insert(filepath, operand0->getEndLine(), operand0->getEndColumn() + 1,
               it->second);
      } break;

      case vpiCycleDelayOp: {
        const uhdm::Any *const operand1 = operands->at(1);
        insert(filepath, operand1->getStartLine(),
               operand1->getStartColumn() - it->second.length(), it->second);
      } break;

      default: {
        if (operands->size() == 1) {
          const uhdm::Any *const operand0 = operands->at(0);
          /* Handle operation in multiple line
          * @(
            posedge
             in)
          */
          uint32_t colLine = operand0->getStartLine();
          int32_t colDiff = operand0->getStartColumn() - it->second.length();
          if ((colLine > 0) && (colDiff > 0)) {
            if ((colDiff < 0) && (object->getStartLine() != colLine))
              insert(filepath, operand0->getStartLine() - 1, 1, it->second);
            else
              insert(filepath, operand0->getStartLine(), colDiff, it->second);
          }
        } else if (operands->size() == 2) {
          const uhdm::Any *const operand1 = operands->at(1);
          insert(filepath, operand1->getStartLine(),
                 operand1->getStartColumn() - it->second.length(), it->second);
        }
      } break;
    }
  }

  void enterPartSelect(const uhdm::PartSelect *const object,
                       uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    if (const uhdm::Any *const parent = object->getParent()) {
      insert(filepath, object->getStartLine(), object->getStartColumn(),
             formatName(parent->getName()));
    }

    const uhdm::Expr *const lr = object->getLeftExpr();
    const uhdm::Expr *const rr = object->getRightExpr();

    if ((lr != nullptr) && (rr != nullptr)) {
      insert(filepath, lr->getStartLine(), lr->getStartColumn() - 1, "[");
      insert(filepath, lr->getEndLine(), lr->getEndColumn(), ":");
      insert(filepath, rr->getEndLine(), rr->getEndColumn(), "]");
    }
  }

  void enterIndexedPartSelect(const uhdm::IndexedPartSelect *const object,
                              uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view kPosIndexed = "+:";
    constexpr std::string_view kNegIndexed = "-:";

    const uhdm::Any *const parent = object->getParent();
    if (parent == nullptr) return;

    const std::filesystem::path &filepath = object->getFile();
    const std::string text = formatName(parent->getDefName());
    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
    insert(filepath, object->getStartLine(),
           object->getStartColumn() + text.length(), "[");
    insert(filepath, object->getEndLine(), object->getEndColumn() - 1, "]");

    const uhdm::Expr *const width = object->getWidthExpr();
    switch (object->getIndexedPartSelectType()) {
      case vpiPosIndexed: {
        insert(filepath, width->getStartLine(),
               width->getStartColumn() - kPosIndexed.length(), kPosIndexed);
      } break;

      case vpiNegIndexed: {
        insert(filepath, width->getStartLine(),
               width->getStartColumn() - kNegIndexed.length(), kNegIndexed);
      } break;
    };
  }

  void enterRefObj(const uhdm::RefObj *const object,
                   uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           formatName(object->getName()));
  }

  void enterHierPath(const uhdm::HierPath *const object,
                     uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    const uhdm::AnyCollection *const elements = object->getPathElems();
    if ((elements != nullptr) && !elements->empty()) {
      for (size_t i = 1, n = elements->size(); i < n; ++i) {
        const uhdm::Any *const element = elements->at(i);
        if (element->getStartColumn() > 0) {
          insert(filepath, element->getStartLine(),
                 element->getStartColumn() - 1, ".");
        }
      }
    }
  }

  void enterVarSelect(const uhdm::VarSelect *const object,
                      uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();
    const std::string text = formatName(object->getName());

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
  }

  void enterBitSelect(const uhdm::BitSelect *const object,
                      uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();
    std::string text = formatName(object->getName());

    if (const uhdm::Expr *const index = object->getIndex()) {
      insert(filepath, index->getStartLine(), index->getStartColumn() - 1, "[");
      insert(filepath, index->getStartLine(), index->getEndColumn(), "]");
    }

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
  }

  void enterRefVar(const uhdm::RefVar *const object,
                   uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterShortRealVar(const uhdm::ShortRealVar *const object,
                         uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterRealVar(const uhdm::RealVar *const object,
                    uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterByteVar(const uhdm::ByteVar *const object,
                    uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterShortIntVar(const uhdm::ShortIntVar *const object,
                        uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterIntVar(const uhdm::IntVar *const object,
                   uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterLongIntVar(const uhdm::LongIntVar *const object,
                       uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterIntegerVar(const uhdm::IntegerVar *const object,
                       uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterTimeVar(const uhdm::TimeVar *const object,
                    uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterArrayVar(const uhdm::ArrayVar *const object,
                     uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    enterVariables_(object);

    const std::filesystem::path &filepath = object->getFile();

    if (const uhdm::RefTypespec *const rt = object->getTypespec()) {
      if (const uhdm::Typespec *const typespec = rt->getActual()) {
        insert(filepath, typespec->getStartLine(),
               typespec->getStartColumn() - 1, "[");
        insert(filepath, typespec->getEndLine(), typespec->getEndColumn(), "]");
      }
    }

    if (const uhdm::VariablesCollection *const variables =
            object->getVariables()) {
      std::copy(variables->begin(), variables->end(),
                std::inserter(m_visited, m_visited.end()));
    }
  }

  void enterRegArray(const uhdm::RegArray *const object,
                     uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterReg(const uhdm::Reg *const object, uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterPackedArrayVar(const uhdm::PackedArrayVar *const object,
                           uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterBitVar(const uhdm::BitVar *const object,
                   uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterLogicVar(const uhdm::LogicVar *const object,
                     uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterStructVar(const uhdm::StructVar *const object,
                      uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterUnionVar(const uhdm::UnionVar *const object,
                     uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterEnumVar(const uhdm::EnumVar *const object,
                    uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterStringVar(const uhdm::StringVar *const object,
                      uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterChandleVar(const uhdm::ChandleVar *const object,
                       uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterVarBit(const uhdm::VarBit *const object,
                   uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterTask(const uhdm::Task *const object, uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "task";
    constexpr std::string_view keyword2 = "endtask";
    constexpr std::string_view keyword3 = "virtual";
    constexpr std::string_view keyword4 = "pure";

    const std::filesystem::path &filepath = object->getFile();
    const bool isPureVirtual = object->getDPIPure();

    std::string text;
    if (isPureVirtual) {
      text.append(keyword4).append(1, kOverwriteMarker);
    }
    if (object->getVirtual()) {
      text.append(keyword3).append(1, kOverwriteMarker);
    }
    text.append(keyword1)
        .append(1, kOverwriteMarker)
        .append(formatName(object->getName()))
        .append("(");

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);

    if (!isPureVirtual) {
      insert(filepath, object->getEndLine(),
             object->getEndColumn() - keyword2.length(), keyword2);
    }

    int32_t end_line = object->getStartLine();
    int32_t end_column = object->getStartColumn() + text.length();
    const uhdm::IODeclCollection *const io_decls = object->getIODecls();
    if ((io_decls != nullptr) && !io_decls->empty()) {
      for (int32_t i = 0, ni = io_decls->size() - 1; i < ni; ++i) {
        const uhdm::IODecl *const io_decl = io_decls->at(i);
        if (const uhdm::Any *const expr = io_decl->getExpr()) {
          insert(filepath, expr->getStartLine(), expr->getStartColumn() - 1,
                 "=");
          insert(filepath, expr->getEndLine(), expr->getEndColumn(), ",");
        } else {
          insert(filepath, io_decl->getEndLine(), io_decl->getEndColumn(), ",");
        }
      }

      const uhdm::IODecl *const io_declN = io_decls->back();
      if (const uhdm::Any *const exprN = io_declN->getExpr()) {
        insert(filepath, exprN->getStartLine(), exprN->getStartColumn() - 1,
               "=");
        end_line = exprN->getEndLine();
        end_column = exprN->getEndColumn();
      } else {
        end_line = io_declN->getEndLine();
        end_column = io_declN->getEndColumn();
      }
    }

    insert(filepath, end_line, end_column, ");");
  }

  void enterFunction(const uhdm::Function *const object,
                     uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "function";
    constexpr std::string_view keyword2 = "automatic";
    constexpr std::string_view keyword3 = "endfunction";
    constexpr std::string_view keyword4 = "void";
    constexpr std::string_view keyword5 = "virtual";
    // constexpr std::string_view keyword6 = "pure";
    constexpr std::string_view keyword7 = "extern";
    const std::filesystem::path &filepath = object->getFile();

    bool isExtern = false;
    std::string text;
    if (object->getAccessType() == vpiExternAcc) {
      text.append(keyword7).append(1, kOverwriteMarker);
      isExtern = true;
    }
    if (object->getVirtual()) {
      text.append(keyword5).append(1, kOverwriteMarker);
    }
    text.append(keyword1);
    if (object->getAutomatic()) {
      text.append(1, kOverwriteMarker).append(keyword2);
    }

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);

    int32_t end_column = object->getStartColumn() + text.length();

    // NOTE(HS): For implicit return, the location data is never set
    if (const uhdm::Variables *const returnValue = object->getReturn()) {
      if (returnValue->getEndColumn() > 0) {
        end_column = returnValue->getEndColumn();
      }
    } else {
      insert(filepath, object->getStartLine(), end_column + 1, keyword4);
      end_column += keyword4.length() + 1;
    }

    const std::string name = formatName(object->getName());
    insert(filepath, object->getStartLine(), end_column + 1, name);
    end_column += name.length() + 1;

    insert(filepath, object->getStartLine(), end_column, "(");

    const uhdm::IODeclCollection *const io_decls = object->getIODecls();
    if ((io_decls != nullptr) && !io_decls->empty()) {
      for (int32_t i = 0, ni = io_decls->size() - 1; i < ni; ++i) {
        uhdm::IODeclCollection::const_reference ioDecl = io_decls->at(i);
        if (const uhdm::Any *const expr = ioDecl->getExpr()) {
          insert(filepath, expr->getStartLine(), expr->getStartColumn() - 1,
                 "=");
          insert(filepath, expr->getEndLine(), expr->getEndColumn(), ",");
        } else {
          insert(filepath, ioDecl->getEndLine(), ioDecl->getEndColumn(), ",");
        }
      }

      uhdm::IODeclCollection::const_reference io_declN = io_decls->back();
      if (const uhdm::Any *const exprN = io_declN->getExpr()) {
        insert(filepath, exprN->getStartLine(), exprN->getStartColumn() - 1,
               "=");
        insert(filepath, exprN->getEndLine(), exprN->getEndColumn(), ");");
      } else {
        const uhdm::RangeCollection *const ranges = io_declN->getRanges();
        if ((ranges != nullptr) && !ranges->empty()) {
          const uhdm::Range *const rangeN = ranges->back();
          insert(filepath, io_declN->getEndLine(), rangeN->getEndColumn(),
                 ");");
        } else {
          insert(filepath, io_declN->getEndLine(), io_declN->getEndColumn(),
                 ");");
        }
      }
    } else {
      insert(filepath, object->getStartLine(), end_column + 1, ");");
    }
    if (!isExtern) {
      insert(filepath, object->getEndLine(), object->getStartColumn(),
             keyword3);
    }
  }

  void enterModport(const uhdm::Modport *const object,
                    uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "modport";

    const std::filesystem::path &filepath = object->getFile();

    std::string prefix(keyword);
    prefix.append(1, kOverwriteMarker);

    std::string text = prefix;
    text.append(formatName(object->getName()));

    insert(filepath, object->getStartLine(),
           object->getStartColumn() - prefix.length(), text);

    const uhdm::IODeclCollection *const io_decls = object->getIODecls();
    if ((io_decls != nullptr) && !io_decls->empty()) {
      insert(filepath, object->getEndLine(), object->getEndColumn(), "(");

      for (int32_t i = 0, ni = io_decls->size() - 1; i < ni; ++i) {
        uhdm::IODeclCollection::const_reference io_decl = io_decls->at(i);
        insert(filepath, io_decl->getEndLine(), io_decl->getEndColumn(), ",");
      }

      uhdm::IODeclCollection::const_reference io_declN = io_decls->back();
      insert(filepath, io_declN->getEndLine(), io_declN->getEndColumn(), ")");
    } else {
      insert(filepath, object->getEndLine(), object->getEndColumn(), "()");
    }
  }

  void enterInterfaceTFDecl(const uhdm::InterfaceTFDecl *const object,
                            uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterContAssign(const uhdm::ContAssign *const object,
                       uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "assign";

    const std::filesystem::path &filepath = object->getFile();

    std::string text(keyword);

    if (const uhdm::Any *const lhs = object->getLhs()) {
      text.resize(keyword.length() + 1 + lhs->getEndColumn() -
                      object->getStartColumn() + 1,
                  kOverwriteMarker);
      text[keyword.length() + 1 + lhs->getEndColumn() -
           object->getStartColumn()] = '=';
    }
    const int32_t column = object->getStartColumn() - keyword.length() - 1;
    if (column > 0) {
      insert(filepath, object->getStartLine(),
             object->getStartColumn() - keyword.length() - 1, text);
    }
  }

  void enterContAssignBit(const uhdm::ContAssignBit *const object,
                          uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterPort(const uhdm::Port *const object, uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           formatName(object->getName()));
  }

  void enterPortBit(const uhdm::PortBit *const object,
                    uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterCheckerPort(const uhdm::CheckerPort *const object,
                        uint32_t vpiRelation) final {
    // Test file not available. Need to try with tests\CheckerInst
  }

  void enterCheckerInstPort(const uhdm::CheckerInstPort *const object,
                            uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterGate(const uhdm::Gate *const object, uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    text.assign(formatName(object->getName()));

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);

    uint32_t column = object->getStartColumn();
    text.assign(formatName(object->getDefName()));

    if (const uhdm::Expr *expr = object->getDelay()) {
      if (expr->getUhdmType() == uhdm::UhdmType::Operation) {
        const uhdm::AnyCollection *const operands =
            static_cast<const uhdm::Operation *>(expr)->getOperands();
        if ((operands != nullptr) && !operands->empty()) {
          uhdm::AnyCollection::const_reference operand0 = operands->front();
          uhdm::AnyCollection::const_reference operandN = operands->back();

          insert(filepath, operand0->getStartLine(),
                 operand0->getStartColumn() - 2, "#(");
          insert(filepath, operandN->getEndLine(), operandN->getEndColumn(),
                 ")");
        }
      }
      column = expr->getStartColumn();
    }
    insert(filepath, object->getStartLine(), column - text.length() - 1, text);

    column = object->getEndColumn();
    uint32_t endColumn = object->getEndColumn() + 1;
    const uhdm::PrimTermCollection *const prims = object->getPrimTerms();
    if ((prims != nullptr) && !prims->empty()) {
      for (int32_t i = 0, ni = prims->size() - 1; i < ni; ++i) {
        uhdm::PrimTermCollection::const_reference prim = prims->at(i);
        insert(filepath, prim->getEndLine(), prim->getEndColumn(), ",");
      }

      uhdm::PrimTermCollection::const_reference prim0 = prims->front();
      uhdm::PrimTermCollection::const_reference primN = prims->back();
      column = prim0->getStartColumn() - 1;
      endColumn = primN->getEndColumn();
    }

    insert(filepath, object->getStartLine(), column, "(");
    insert(filepath, object->getEndLine(), endColumn, ");");
  }

  void enterSwitchTran(const uhdm::SwitchTran *const object,
                       uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    text.assign(formatName(object->getName())).append("(");
    insert(filepath, object->getStartLine(), object->getStartColumn(), text);

    text.assign(formatName(object->getDefName())).append(1, kOverwriteMarker);
    insert(filepath, object->getStartLine(),
           object->getStartColumn() - text.length(), text);

    uint32_t column = object->getEndColumn();
    const uhdm::PrimTermCollection *const prims = object->getPrimTerms();
    if ((prims != nullptr) && !prims->empty()) {
      for (int32_t i = 0, ni = prims->size() - 1; i < ni; ++i) {
        uhdm::PrimTermCollection::const_reference prim = prims->at(i);
        insert(filepath, prim->getEndLine(), prim->getEndColumn(), ",");
      }

      uhdm::PrimTermCollection::const_reference primN = prims->back();
      column = primN->getEndColumn();
    }
    insert(filepath, object->getEndLine(), column, ");");
  }

  void enterUdp(const uhdm::Udp *const object, uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "primitive";
    constexpr std::string_view keyword2 = "endprimitive";

    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    text.append(keyword1)
        .append(1, kOverwriteMarker)
        .append(formatName(object->getDefName()));

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
    insert(filepath, object->getEndLine(),
           object->getEndColumn() - keyword2.length(), keyword2);
  }

  void enterModPath(const uhdm::ModPath *const object,
                    uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterTchk(const uhdm::Tchk *const object, uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterRange(const uhdm::Range *const object, uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "unsized";

    const std::filesystem::path &filepath = object->getFile();

    uint32_t column = object->getStartColumn();
    uint32_t endColumn = object->getEndColumn();

    const uhdm::Expr *const rexpr = object->getRightExpr();
    if (rexpr->getUhdmType() == uhdm::UhdmType::Operation) {  // single-range
      const uhdm::AnyCollection *const operands =
          static_cast<const uhdm::Operation *>(rexpr)->getOperands();
      if ((operands != nullptr) &&
          (operands->at(0)->getUhdmType() == uhdm::UhdmType::Constant)) {
        std::string_view loperand =
            static_cast<const uhdm::Constant *>(operands->at(0))
                ->getDecompile();
        insert(filepath, object->getStartLine(), object->getStartColumn(),
               loperand);
        m_visited.insert(rexpr);
        m_visited.insert(object->getLeftExpr());

        column -= 1;  // It's a single range so set the start "[" to column - 1.
        endColumn += 1;
      }
    } else if (rexpr->getDecompile() == keyword) {  // unsized-range
      m_visited.insert(rexpr);
      m_visited.insert(object->getLeftExpr());
    } else {  // double-range
      if (rexpr->getStartColumn() > 0) {
        insert(filepath, rexpr->getStartLine(), rexpr->getStartColumn() - 1,
               ":");
      }
    }
    insert(filepath, object->getStartLine(), column, "[");
    insert(filepath, object->getEndLine(), endColumn - 1, "]");
  }

  void enterUdpDefn(const uhdm::UdpDefn *const object,
                    uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "primitive";
    constexpr std::string_view keyword2 = "endprimitive";

    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    text.append(keyword1)
        .append(1, kOverwriteMarker)
        .append(formatName(object->getDefName()))
        .append("(");

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
    insert(filepath, object->getEndLine(),
           object->getEndColumn() - keyword2.length(), keyword2);

    const uhdm::IODeclCollection *const io_decls = object->getIODecls();
    if ((io_decls != nullptr) && !io_decls->empty()) {
      for (int32_t i = 0, ni = io_decls->size() - 1; i < ni; ++i) {
        uhdm::IODeclCollection::const_reference io_decl = io_decls->at(i);
        insert(filepath, io_decl->getEndLine(), io_decl->getEndColumn(), ",");
      }
      uhdm::IODeclCollection::const_reference io_declN = io_decls->back();
      insert(filepath, io_declN->getEndLine(), io_declN->getEndColumn(), ")");
    } else {
      insert(filepath, object->getEndLine(), object->getEndColumn() + 1, ")");
    }
  }

  void enterTableEntry(const uhdm::TableEntry *const object,
                       uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    const std::string text = formatValue(object->getValue(), false);
    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
  }

  void enterIODecl(const uhdm::IODecl *const object,
                   uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    if (const uhdm::RefTypespec *const rt = object->getTypespec()) {
      if (const uhdm::Typespec *const typespec = rt->getActual()) {
        const std::string name = getTypespecName(typespec);
        switch (typespec->getUhdmType()) {
          case uhdm::UhdmType::ClassTypespec:
          case uhdm::UhdmType::EnumTypespec:
          case uhdm::UhdmType::StructTypespec: {
            insert(filepath, object->getStartLine(), object->getStartColumn(),
                   name);
          } break;

          default: {
            insert(filepath, typespec->getStartLine(),
                   typespec->getStartColumn(), name);
          } break;
        }
      }
    }

    std::string text = formatName(object->getName());
    insert(filepath, object->getStartLine(), object->getEndColumn(), text);
  }

  void enterAlias(const uhdm::Alias *const object, uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterClockingBlock(const uhdm::ClockingBlock *const object,
                          uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const uhdm::Any *const parent = object->getParent();
    if ((parent == nullptr) ||
        (parent->getUhdmType() != uhdm::UhdmType::Module))
      return;

    constexpr std::string_view keyword1 = "unnamed_clocking_block";
    constexpr std::string_view keyword2 = "default";
    constexpr std::string_view keyword3 = "global";
    constexpr std::string_view keyword4 = "clocking";
    constexpr std::string_view keyword5 = "endclocking";
    constexpr std::string_view keyword6 = "input";
    constexpr std::string_view keyword7 = "output";

    const std::filesystem::path &filepath = object->getFile();
    const std::string name = formatName(object->getName());

    const uhdm::Module *const mdl = static_cast<const uhdm::Module *>(parent);
    std::string text;
    if (mdl->getGlobalClocking() == object) {
      text.append(keyword3).append(1, kOverwriteMarker);
    } else if (mdl->getDefaultClocking() == object) {
      text.append(keyword2).append(1, kOverwriteMarker);
    }
    text.append(keyword4);

    if (name != keyword1) {
      text.append(1, kOverwriteMarker).append(name);
    }

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
    insert(filepath, object->getEndLine(),
           object->getEndColumn() - keyword5.length(), keyword5);

    const uhdm::DelayControl *const inputSkew = object->getInputSkew();
    const uhdm::DelayControl *const outputSkew = object->getOutputSkew();
    if (inputSkew != nullptr) {
      insert(filepath, inputSkew->getStartLine(),
             inputSkew->getStartColumn() - keyword2.length() - 1 -
                 keyword6.length() - 1,
             keyword2);
      insert(filepath, inputSkew->getStartLine(),
             inputSkew->getStartColumn() - keyword6.length() - 1, keyword6);

      edge_names_t::const_iterator it =
          kEdgeNames.find(object->getOutputEdge());
      if (it != kEdgeNames.end()) {
        text.assign(keyword7).append(1, kOverwriteMarker).append(it->second);
        insert(filepath, inputSkew->getEndLine(), inputSkew->getEndColumn() + 1,
               text);
      }
    }

    if (outputSkew != nullptr) {
      if ((inputSkew == nullptr) ||
          (inputSkew->getStartLine() != outputSkew->getStartLine())) {
        insert(filepath, outputSkew->getStartLine(),
               outputSkew->getStartColumn() - keyword2.length() - 1 -
                   keyword6.length() - 1,
               keyword2);
      }

      insert(filepath, outputSkew->getStartLine(),
             outputSkew->getStartColumn() - keyword7.length() - 1, keyword7);
    }
  }

  void enterClockingIODecl(const uhdm::ClockingIODecl *const object,
                           uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           formatName(object->getName()));

    std::string text;
    direction_names_t::const_iterator it1 =
        kDirectionNames.find(object->getDirection());
    if (it1 != kDirectionNames.end()) {
      text.append(it1->second).append(1, kOverwriteMarker);
    }
    if ((object->getDirection() == vpiInput) &&
        (object->getInputEdge() != vpiNoEdge)) {
      edge_names_t::const_iterator it2 =
          kEdgeNames.find(object->getInputEdge());
      if (it2 != kEdgeNames.end()) {
        text.append(it2->second).append(1, kOverwriteMarker);
      }
    } else if ((object->getDirection() == vpiOutput) &&
               (object->getOutputEdge() != vpiNoEdge)) {
      edge_names_t::const_iterator it2 =
          kEdgeNames.find(object->getOutputEdge());
      if (it2 != kEdgeNames.end()) {
        text.append(it2->second).append(1, kOverwriteMarker);
      }
    }

    const uhdm::DelayControl *const inputSkew = object->getInputSkew();
    const uhdm::DelayControl *const outputSkew = object->getOutputSkew();
    if (inputSkew != nullptr) {
      insert(filepath, inputSkew->getStartLine(),
             inputSkew->getStartColumn() - text.length(), text);
    } else if (outputSkew != nullptr) {
      insert(filepath, outputSkew->getStartLine(),
             outputSkew->getStartColumn() - text.length(), text);
    } else {
      insert(filepath, object->getStartLine(),
             object->getStartColumn() - text.length(), text);
    }

    const uhdm::Any *const expr = object->getExpr();
    if (expr != nullptr) {
      insert(filepath, expr->getStartLine(), expr->getStartColumn() - 1, "=");
    }
  }

  void enterParamAssign(const uhdm::ParamAssign *const object,
                        uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    const uhdm::Any *const lhs = object->getLhs();
    const uhdm::Any *const rhs = object->getRhs();
    if ((lhs != nullptr) && (rhs != nullptr)) {
      insert(filepath, rhs->getStartLine(), rhs->getStartColumn() - 1, "=");
    }
  }

  void enterInterfaceArray(const uhdm::InterfaceArray *const object,
                           uint32_t vpiRelation) final {
    //@todo: Ideally it should have information related to type of interface.
    // Ex. MyInterface.MyModport my_port2. It only has "my_port2" info not
    // MyInterface.MyModport File: test\ModportRange\dut.sv
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           formatName(object->getName()));
  }

  void enterProgramArray(const uhdm::ProgramArray *const object,
                         uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterModuleArray(const uhdm::ModuleArray *const object,
                        uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           formatName(object->getName()));

    const uhdm::RangeCollection *const ranges = object->getRanges();
    if ((ranges != nullptr) && !ranges->empty()) {
      const uhdm::Range *const rangeN = ranges->back();
      insert(filepath, rangeN->getStartLine(), rangeN->getEndColumn(), "();");
    }
  }

  void enterModuleTypespec(const uhdm::ModuleTypespec *const object,
                           uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterSwitchArray(const uhdm::SwitchArray *const object,
                        uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterUdpArray(const uhdm::UdpArray *const object,
                     uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterPrimTerm(const uhdm::PrimTerm *const object,
                     uint32_t vpiRelation) final {
    // third_party\tests\SimpleParserTest\jkff_udp.v
    // No data available. Also taken care by entergate() and enterRef_obj().
  }

  void enterPathTerm(const uhdm::PathTerm *const object,
                     uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterTchkTerm(const uhdm::TchkTerm *const object,
                     uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterNetBit(const uhdm::NetBit *const object,
                   uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterStructNet(const uhdm::StructNet *const object,
                      uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    std::string prefix;

    net_type_names_t::const_iterator it =
        kNetTypeNames.find(object->getNetType());
    if (it != kNetTypeNames.end()) {
      prefix.append(it->second).append(1, kOverwriteMarker);
    }

    if (const uhdm::RefTypespec *const rt = object->getTypespec()) {
      if (const uhdm::Typespec *const typespec = rt->getActual()) {
        prefix.append(getTypespecName(typespec)).append(1, kOverwriteMarker);
      }
    }

    std::string text = prefix;
    text.append(formatName(object->getName()));

    insert(filepath, object->getStartLine(),
           object->getStartColumn() - prefix.length(), text);
  }

  void enterEnumNet(const uhdm::EnumNet *const object,
                    uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();
    std::string prefix;

    net_type_names_t::const_iterator it =
        kNetTypeNames.find(object->getNetType());
    if (it != kNetTypeNames.end()) {
      prefix.append(it->second).append(1, kOverwriteMarker);
    }

    if (const uhdm::RefTypespec *const rt = object->getTypespec()) {
      if (const uhdm::Typespec *const typespec = rt->getActual()) {
        prefix.append(getTypespecName(typespec)).append(1, kOverwriteMarker);
      }
    }

    std::string text = prefix;
    text.append(formatName(object->getName()));

    insert(filepath, object->getStartLine(),
           object->getStartColumn() - prefix.length(), text);
  }

  void enterIntegerNet(const uhdm::IntegerNet *const object,
                       uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();
    std::string prefix;

    net_type_names_t::const_iterator it =
        kNetTypeNames.find(object->getNetType());
    if (it != kNetTypeNames.end()) {
      prefix.append(it->second).append(1, kOverwriteMarker);
    }

    if (const uhdm::RefTypespec *const rt = object->getTypespec()) {
      if (const uhdm::Typespec *const typespec = rt->getActual()) {
        prefix.append(getTypespecName(typespec)).append(1, kOverwriteMarker);
      }
    }

    std::string text = prefix;
    text.append(formatName(object->getName()));

    insert(filepath, object->getStartLine(),
           object->getStartColumn() - prefix.length(), text);
  }

  void enterTimeNet(const uhdm::TimeNet *const object,
                    uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterLogicNet(const uhdm::LogicNet *const object,
                     uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           formatName(object->getName()));

    const uhdm::RangeCollection *const ranges = object->getRanges();
    if ((ranges != nullptr) && !ranges->empty()) {
      net_type_names_t::const_iterator it =
          kNetTypeNames.find(object->getNetType());
      if (it != kNetTypeNames.end()) {
        const uhdm::Range *const range0 = ranges->at(0);
        insert(filepath, range0->getStartLine(),
               range0->getStartColumn() - it->second.length() - 2, it->second);
      }
    }
  }

  void enterArrayNet(const uhdm::ArrayNet *const object,
                     uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           formatName(object->getName()));
  }

  void enterPackedArrayNet(const uhdm::PackedArrayNet *const object,
                           uint32_t vpiRelation) final {}

  void enterEventTypespec(const uhdm::EventTypespec *const object,
                          uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterNamedEvent(const uhdm::NamedEvent *const object,
                       uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword = "event";
    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    text.append(keyword)
        .append(1, kOverwriteMarker)
        .append(formatName(object->getName()))
        .append(";");
    insert(filepath, object->getStartLine(),
           object->getStartColumn() - keyword.length() - 1, text);
  }

  void enterNamedEventArray(const uhdm::NamedEventArray *const object,
                            uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterParameter(const uhdm::Parameter *const object,
                      uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    // constexpr std::string_view keyword1 = "localparam";
    // constexpr std::string_view keyword2 = "parameter";

    const std::filesystem::path &filepath = object->getFile();

    int32_t line = object->getStartLine();
    int32_t column = object->getStartColumn();
    if (const uhdm::RefTypespec *const rt = object->getTypespec()) {
      if (const uhdm::Typespec *const typespec = rt->getActual()) {
        if ((typespec->getUhdmType() == uhdm::UhdmType::EnumTypespec) ||
            (typespec->getUhdmType() == uhdm::UhdmType::StructTypespec)) {
          const std::string name = getTypespecName(typespec);
          column = object->getStartColumn() - name.length() - 1;
          insert(filepath, line, column, name);
        } else if (typespec->getStartColumn() != 0) {
          // TODO(HS): This check needs to go!
          column = typespec->getStartColumn();
        }
      }
    }

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           formatName(object->getName()));
  }

  void enterDefParam(const uhdm::DefParam *const object,
                     uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterSpecParam(const uhdm::SpecParam *const object,
                      uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterClassTypespec(const uhdm::ClassTypespec *const object,
                          uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterExtends(const uhdm::Extends *const object,
                    uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "extends";
    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           keyword1);

    if (const uhdm::RefTypespec *const rt = object->getClassTypespec()) {
      insert(filepath, rt->getStartLine(), rt->getStartColumn(),
             formatName(rt->getName()));
    }
  }

  void enterClassDefn(const uhdm::ClassDefn *const object,
                      uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "class";
    constexpr std::string_view keyword2 = "endclass";

    const std::filesystem::path &filepath = object->getFile();
    const std::string name = formatName(object->getName());

    std::string text;
    text.append(keyword1)
        .append(1, kOverwriteMarker)
        .append(formatName(object->getName()));

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
    insert(filepath, object->getEndLine(),
           object->getEndColumn() - keyword2.length(), keyword2);

    if (const uhdm::Extends *const extends = object->getExtends()) {
      enterExtends(extends, vpiExtends);
    }
  }

  void enterClassObj(const uhdm::ClassObj *const object,
                     uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterClassVar(const uhdm::ClassVar *const object,
                     uint32_t vpiRelation) final {
    enterVariables_(object);
  }

  void enterInterface(const uhdm::Interface *const object,
                      uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    if (isInterfaceDefinition(object)) {
      constexpr std::string_view keyword1 = "interface";
      constexpr std::string_view keyword2 = "endinterface";

      std::string text;
      text.append(keyword1)
          .append(1, kOverwriteMarker)
          .append(formatName(object->getDefName()));

      insert(filepath, object->getStartLine(), object->getStartColumn(), text);
      insert(filepath, object->getEndLine(),
             object->getEndColumn() - keyword2.length(), keyword2);
    } else {
      insert(filepath, object->getStartLine(), object->getStartColumn(),
             formatName(object->getName()));
    }
  }

  void enterProgram(const uhdm::Program *const object,
                    uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "program";
    constexpr std::string_view keyword2 = "endprogram";

    const std::filesystem::path &filepath = object->getFile();
    const std::string name = formatName(object->getName());

    std::string text;
    if (name.empty()) {
      text.append(keyword1)
          .append(1, kOverwriteMarker)
          .append(formatName(object->getDefName()));

      insert(filepath, object->getStartLine(), object->getStartColumn(), text);
      insert(filepath, object->getEndLine(),
             object->getEndColumn() - keyword2.length(), keyword2);
    } else {
      text.append(formatName(object->getDefName()))
          .append(" #() ")
          .append(name)
          .append("(");

      insert(filepath, object->getStartLine(), object->getStartColumn(), text);
      insert(filepath, object->getEndLine(), object->getEndColumn() - 1, ")");
    }
  }

  void enterPackage(const uhdm::Package *const object,
                    uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "package";
    constexpr std::string_view keyword2 = "endpackage";
    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    text.append(keyword1)
        .append(1, kOverwriteMarker)
        .append(formatName(object->getName()));

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
    insert(filepath, object->getEndLine(),
           object->getEndColumn() - keyword2.length(), keyword2);
  }

  void enterModule(const uhdm::Module *const object,
                   uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    uint32_t end_column = 0;
    if (isModuleDefinition(object)) {
      constexpr std::string_view keyword1("module");
      constexpr std::string_view keyword2("endmodule");

      std::string text;
      text.append(keyword1)
          .append(1, kOverwriteMarker)
          .append(formatName(object->getDefName()));

      insert(filepath, object->getStartLine(), object->getStartColumn(), text);
      insert(filepath, object->getEndLine(),
             object->getEndColumn() - keyword2.length(), keyword2);
      end_column = object->getStartColumn() + text.length();

      insert(filepath, object->getStartLine(), end_column, "(");

      uint32_t end_line = object->getStartLine();
      const uhdm::PortCollection *const ports = object->getPorts();
      if ((ports != nullptr) && !ports->empty()) {
        for (int32_t i = 0, ni = ports->size(); i < ni; ++i) {
          const uhdm::Port *const port = ports->at(i);

          const uhdm::RangeCollection *ranges = nullptr;
          if (const uhdm::RefTypespec *const rt = port->getTypespec()) {
            if (const uhdm::Typespec *const typespec = rt->getActual()) {
              if (typespec->getUhdmType() == uhdm::UhdmType::ArrayTypespec) {
                ranges = static_cast<const uhdm::ArrayTypespec *>(typespec)
                             ->getRanges();
              } else if (typespec->getUhdmType() ==
                         uhdm::UhdmType::PackedArrayTypespec) {
                ranges =
                    static_cast<const uhdm::PackedArrayTypespec *>(typespec)
                        ->getRanges();
              }
            }
          }

          if ((ranges == nullptr) || ranges->empty()) {
            end_line = port->getEndLine();
            end_column = port->getEndColumn();
          } else {
            const uhdm::Range *const rangeN = ranges->back();

            end_line = rangeN->getEndLine();
            end_column = rangeN->getEndColumn();
          }

          if (i != (ni - 1)) {
            insert(filepath, end_line, end_column, ",");
          }
        }
      } else {
        ++end_column;
      }
      insert(filepath, end_line, end_column, ");");
    } else {
      std::string text;
      text.append(formatName(object->getDefName()))
          .append(1, kOverwriteMarker)
          .append(formatName(object->getName()));

      insert(filepath, object->getStartLine(), object->getStartColumn(), text);
      end_column = object->getStartColumn() + text.length();

      insert(filepath, object->getStartLine(), end_column, "(");

      const uhdm::PortCollection *const ports = object->getPorts();
      if ((ports != nullptr) && !ports->empty()) {
        for (int32_t i = 0, ni = ports->size() - 1; i < ni; ++i) {
          const uhdm::Port *const port = ports->at(i);
          if (const uhdm::Any *const high_conn = port->getHighConn()) {
            insert(filepath, high_conn->getEndLine(),
                   high_conn->getEndColumn() + 1, ",");
          }
        }
        const uhdm::Port *const portN = ports->back();
        if (const uhdm::Any *const high_connN = portN->getHighConn()) {
          end_column = high_connN->getEndColumn() + 1;
        }
      }
      insert(filepath, object->getEndLine(), end_column + 1, ");");
    }

    const uhdm::ParamAssignCollection *const param_assigns =
        object->getParamAssigns();
    if ((param_assigns != nullptr) && !param_assigns->empty()) {
      uhdm::ParamAssignCollection ordered(*param_assigns);
      std::stable_sort(ordered.begin(), ordered.end(),
                       [](uhdm::ParamAssignCollection::const_reference lhs,
                          uhdm::ParamAssignCollection::const_reference rhs) {
                         int32_t r = lhs->getStartLine() - rhs->getStartLine();
                         if (r != 0) return r < 0;

                         r = lhs->getStartColumn() - rhs->getStartColumn();
                         if (r != 0) return r < 0;

                         r = lhs->getEndLine() - rhs->getEndLine();
                         if (r != 0) return r < 0;

                         r = lhs->getEndColumn() - rhs->getEndColumn();
                         return r < 0;
                       });
      for (int32_t i = 0, j = 1, nj = ordered.size(); j < nj; ++i, ++j) {
        const uhdm::Any *const ilhs = ordered[i]->getLhs();
        const uhdm::Any *const jlhs = ordered[j]->getLhs();
        if ((ilhs->getUhdmType() == uhdm::UhdmType::Parameter) &&
            (jlhs->getUhdmType() == uhdm::UhdmType::Parameter)) {
          const uhdm::Typespec *itypespec = nullptr;
          if (const uhdm::RefTypespec *const rt =
                  static_cast<const uhdm::Parameter *>(ilhs)->getTypespec()) {
            itypespec = rt->getActual();
          }

          const uhdm::Typespec *jtypespec = nullptr;
          if (const uhdm::RefTypespec *const rt =
                  static_cast<const uhdm::Parameter *>(jlhs)->getTypespec()) {
            jtypespec = rt->getActual();
          }

          if ((itypespec != nullptr) && (jtypespec != nullptr) &&
              (itypespec->getStartLine() != 0) &&
              (itypespec->getStartColumn() != 0) &&
              (itypespec->getEndLine() != 0) &&
              (itypespec->getEndColumn() != 0) &&
              (itypespec->getUhdmType() == jtypespec->getUhdmType()) &&
              (itypespec->getStartLine() == jtypespec->getStartLine()) &&
              (itypespec->getStartColumn() == jtypespec->getStartColumn()) &&
              (itypespec->getEndLine() == jtypespec->getEndLine()) &&
              (itypespec->getEndColumn() == jtypespec->getEndColumn())) {
            uhdm::ParamAssignCollection::const_reference iparam_assign =
                ordered[i];
            insert(filepath, iparam_assign->getEndLine(),
                   iparam_assign->getEndColumn(), ",");
          }
        }
      }
    }
  }

  void enterCheckerDecl(const uhdm::CheckerDecl *const object,
                        uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterCheckerInst(const uhdm::CheckerInst *const object,
                        uint32_t vpiRelation) final {
    // TODO(KS): In case of checker intance, other data is not available. Only
    // checker instance and instance name with start and end line and col is
    // available. tests\CheckerInst\dut.sv

    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    std::string text;
    text.append(formatName(object->getDefName()))
        .append(1, kOverwriteMarker)
        .append(formatName(object->getName()))
        .append("(");

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);
    insert(filepath, object->getEndLine(), object->getEndColumn(), ")");
  }

  void enterShortRealTypespec(const uhdm::ShortRealTypespec *const object,
                              uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterRealTypespec(const uhdm::RealTypespec *const object,
                         uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterByteTypespec(const uhdm::ByteTypespec *const object,
                         uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterShortIntTypespec(const uhdm::ShortIntTypespec *const object,
                             uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterIntTypespec(const uhdm::IntTypespec *const object,
                        uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterLongIntTypespec(const uhdm::LongIntTypespec *const object,
                            uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterIntegerTypespec(const uhdm::IntegerTypespec *const object,
                            uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterTimeTypespec(const uhdm::TimeTypespec *const object,
                         uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterStringTypespec(const uhdm::StringTypespec *const object,
                           uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterChandleTypespec(const uhdm::ChandleTypespec *const object,
                            uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterLogicTypespec(const uhdm::LogicTypespec *const object,
                          uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const uhdm::Any *const parent = object->getParent();
    if ((parent != nullptr) &&
        (parent->getUhdmType() != uhdm::UhdmType::Parameter) &&
        (parent->getUhdmType() != uhdm::UhdmType::ParamAssign) &&
        (parent->getUhdmType() != uhdm::UhdmType::TypespecMember)) {
      constexpr std::string_view keyword = "logic";
      const std::filesystem::path &filepath = object->getFile();

      insert(filepath, object->getStartLine(), object->getStartColumn(),
             keyword);

      insert(filepath, object->getEndLine(), object->getEndColumn() + 1,
             formatName(object->getName()));
    } else if (object->getName().empty()) {
      enterTypespec(object);
    }
  }

  void enterPackedArrayTypespec(const uhdm::PackedArrayTypespec *const object,
                                uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterArrayTypespec(const uhdm::ArrayTypespec *const object,
                          uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterVoidTypespec(const uhdm::VoidTypespec *const object,
                         uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterSequenceTypespec(const uhdm::SequenceTypespec *const object,
                             uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterPropertyTypespec(const uhdm::PropertyTypespec *const object,
                             uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterInterfaceTypespec(const uhdm::InterfaceTypespec *const object,
                              uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterEnumTypespec(const uhdm::EnumTypespec *const object,
                         uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    std::string text("enum ");

    if (const uhdm::RefTypespec *const rt = object->getBaseTypespec()) {
      if (const uhdm::Typespec *const base_typespec = rt->getActual()) {
        text.append(getTypespecName(base_typespec)).append(1, kOverwriteMarker);
      }
    }

    text.append("{");
    insert(filepath, object->getStartLine(), object->getStartColumn(), text);

    text.assign("} ").append(getTypespecName(object)).append(";");
    insert(filepath, object->getEndLine(), object->getEndColumn() + 1, text);

    const uhdm::EnumConstCollection *const enum_consts =
        object->getEnumConsts();
    if ((enum_consts != nullptr) && !enum_consts->empty()) {
      for (int32_t i = 0, ni = enum_consts->size() - 1; i < ni; ++i) {
        insert(filepath, enum_consts->at(i)->getEndLine(),
               enum_consts->at(i)->getEndColumn(), ",");
      }
    }
  }

  void enterStructTypespec(const uhdm::StructTypespec *const object,
                           uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    // TODO: struct_typespec/endline is wrong!
    // Need to verify more. Now struct_typespec/endline looks good!
    const uhdm::TypespecMemberCollection *const members = object->getMembers();
    if ((members != nullptr) && !members->empty()) {
      constexpr std::string_view keyword1 = "typedef";
      constexpr std::string_view keyword2 = "struct";
      const std::filesystem::path &filepath = object->getFile();

      std::string text;
      const std::string name = formatName(object->getName());
      if (!name.empty()) text.append(keyword1).append(1, kOverwriteMarker);

      text.append(keyword2);
      if (object->getPacked()) {
        text.append(" packed");
      }
      text.append(" {");
      insert(filepath, object->getStartLine(), object->getStartColumn(), text);
      text.assign("} ").append(name);
      insert(filepath, object->getEndLine(), 1, text);
    }
  }

  void enterUnionTypespec(const uhdm::UnionTypespec *const object,
                          uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    // TODO: union_typespec/endline is wrong!
    const uhdm::TypespecMemberCollection *const members = object->getMembers();
    if ((members != nullptr) && !members->empty()) {
      constexpr std::string_view keyword = "typedef";

      std::string text;
      const std::string name = formatName(object->getName());
      if (!name.empty()) text.append(keyword).append(1, kOverwriteMarker);

      text.append("union");
      if (object->getPacked()) {
        text.append(" packed");
      }
      text.append(" {");
      insert(filepath, object->getStartLine(), object->getStartColumn(), text);

      text.assign("} ").append(name);
      insert(filepath, object->getEndLine(), 1, text);
    }
  }

  void enterUnsupportedTypespec(const uhdm::UnsupportedTypespec *const object,
                                uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           formatName(object->getName()));
  }

  void enterTypeParameter(const uhdm::TypeParameter *const object,
                          uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "parameter";
    constexpr std::string_view keyword2 = "=logic";
    constexpr std::string_view keyword3 = "type";

    const std::filesystem::path &filepath = object->getFile();
    if (const uhdm::RefTypespec *const rt = object->getTypespec()) {
      if (const uhdm::Typespec *const typespec = rt->getActual()) {
        switch (typespec->getUhdmType()) {
          case uhdm::UhdmType::LogicTypespec: {
            insert(filepath, typespec->getStartLine(),
                   typespec->getStartColumn() - 1, keyword2);
          } break;

          default:
            break;
        }
      }
    }
    insert(filepath, object->getStartLine(),
           object->getStartColumn() - keyword1.length() - 1, keyword1);
    insert(filepath, object->getStartLine(), object->getStartColumn(),
           keyword3);
    insert(filepath, object->getStartLine(),
           object->getStartColumn() + keyword3.length() + 1,
           formatName(object->getName()));
  }

  void enterTypespecMember(const uhdm::TypespecMember *const object,
                           uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    if (const uhdm::RefTypespec *const rt = object->getTypespec()) {
      if (const uhdm::Typespec *typespec = rt->getActual()) {
        insert(filepath, rt->getStartLine(), rt->getStartColumn(),
               getTypespecName(typespec));
      }
    }
    const std::string name = formatName(object->getName());
    insert(filepath, object->getEndLine(),
           object->getEndColumn() - name.length() - 1, name);
  }

  void enterEnumConst(const uhdm::EnumConst *const object,
                      uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();
    const std::string name = formatName(object->getName());
    insert(filepath, object->getStartLine(), object->getStartColumn(), name);

    if (static_cast<uint16_t>(object->getStartColumn() + name.length()) <
        object->getEndColumn()) {
      std::string text;
      text.append("=").append(object->getDecompile());
      insert(filepath, object->getStartLine(),
             object->getEndColumn() - text.length(), text);
    }
    m_visited.insert(object);
  }

  void enterBitTypespec(const uhdm::BitTypespec *const object,
                        uint32_t vpiRelation) final {
    enterTypespec(object);
  }

  void enterUserSystf(const uhdm::UserSystf *const object,
                      uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterSysFuncCall(const uhdm::SysFuncCall *const object,
                        uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    const std::string text = formatName(object->getName());

    insert(filepath, object->getStartLine(), object->getStartColumn(), text);

    const uhdm::AnyCollection *const call_args = object->getArguments();
    if ((call_args != nullptr) && !call_args->empty()) {
      uhdm::AnyCollection::const_reference call_arg0 = call_args->front();
      uhdm::AnyCollection::const_reference call_argN = call_args->back();

      insert(filepath, call_arg0->getStartLine(),
             call_arg0->getStartColumn() - 1, "(");
      insert(filepath, call_argN->getEndLine(), call_argN->getEndColumn(), ")");

      for (int32_t i = 0, n = call_args->size() - 1; i < n; ++i) {
        uhdm::AnyCollection::const_reference call_arg = call_args->at(i);
        insert(filepath, call_arg->getEndLine(), call_arg->getEndColumn(), ",");
      }
    }
  }

  void enterSysTaskCall(const uhdm::SysTaskCall *const object,
                        uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterMethodFuncCall(const uhdm::MethodFuncCall *const object,
                           uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    if (object->getPrefix() != nullptr) {
      insert(filepath, object->getStartLine(), object->getStartColumn() - 1,
             ".");
    }
    insert(filepath, object->getStartLine(), object->getStartColumn(),
           formatName(object->getName()));
    insert(filepath, object->getStartLine(), object->getEndColumn(), "(");

    uint32_t closing_bracket_line = object->getStartLine();
    uint32_t closing_bracket_column = object->getEndColumn() + 1;
    const uhdm::AnyCollection *const call_args = object->getArguments();
    if ((call_args != nullptr) && !call_args->empty()) {
      for (size_t i = 0, n = call_args->size() - 1; i < n; ++i) {
        const uhdm::Any *const arg = call_args->at(i);
        if ((arg->getStartLine() > 0) && (arg->getStartColumn() > 0) &&
            (arg->getEndLine() > 0) && (arg->getEndColumn() > 0)) {
          insert(filepath, arg->getEndLine(), arg->getEndColumn(), ",");
        }
      }
      closing_bracket_line = call_args->back()->getStartLine();
      closing_bracket_column = call_args->back()->getEndColumn();
    }
    insert(filepath, closing_bracket_line, closing_bracket_column, ")");
  }

  void enterMethodTaskCall(const uhdm::MethodTaskCall *const object,
                           uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();

    insert(filepath, object->getStartLine(), object->getStartColumn(),
           formatName(object->getName()));

    const uhdm::AnyCollection *const args = object->getArguments();
    if ((args != nullptr) && !args->empty()) {
      const uhdm::Any *const arg0 = args->front();
      insert(filepath, arg0->getStartLine(), arg0->getStartColumn() - 1, "(");
      for (int32_t i = 0, ni = args->size() - 1; i < ni; ++i) {
        const uhdm::Any *const arg = args->at(i);
        insert(filepath, arg->getEndLine(), arg->getEndColumn(), ",");
      }
      const uhdm::Any *const argN = args->back();
      insert(filepath, argN->getEndLine(), argN->getEndColumn(), ")");
    } else {
      insert(filepath, object->getStartLine(), object->getEndColumn(), "()");
    }
  }

  void enterFuncCall(const uhdm::FuncCall *const object,
                     uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();
    insert(filepath, object->getStartLine(), object->getStartColumn(),
           formatName(object->getName()));

    const uhdm::AnyCollection *const args = object->getArguments();
    if ((args != nullptr) && !args->empty()) {
      const uhdm::Any *const arg0 = args->front();
      insert(filepath, arg0->getStartLine(), arg0->getStartColumn() - 1, "(");
      for (int32_t i = 0, ni = args->size() - 1; i < ni; ++i) {
        const uhdm::Any *const arg = args->at(i);
        insert(filepath, arg->getEndLine(), arg->getEndColumn(), ",");
      }
      const uhdm::Any *const argN = args->back();
      insert(filepath, argN->getEndLine(), argN->getEndColumn(), ")");
    } else {
      insert(filepath, object->getStartLine(), object->getEndColumn(), "()");
    }
  }

  void enterTaskCall(const uhdm::TaskCall *const object,
                     uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    const std::filesystem::path &filepath = object->getFile();
    insert(filepath, object->getStartLine(), object->getStartColumn(),
           formatName(object->getName()));

    const uhdm::AnyCollection *const args = object->getArguments();
    if ((args != nullptr) && !args->empty()) {
      const uhdm::Any *const arg0 = args->front();
      insert(filepath, arg0->getStartLine(), arg0->getStartColumn() - 1, "(");
      for (int32_t i = 0, ni = args->size() - 1; i < ni; ++i) {
        const uhdm::Any *const arg = args->at(i);
        insert(filepath, arg->getEndLine(), arg->getEndColumn(), ",");
      }
      const uhdm::Any *const argN = args->back();
      insert(filepath, argN->getEndLine(), argN->getEndColumn(), ")");
    } else {
      insert(filepath, object->getStartLine(), object->getEndColumn(), "()");
    }
  }

  void enterConstraintOrdering(const uhdm::ConstraintOrdering *const object,
                               uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterConstraint(const uhdm::Constraint *const object,
                       uint32_t vpiRelation) final {
    // tests\SimpleClass
  }

  void enterImportTypespec(const uhdm::ImportTypespec *const object,
                           uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;

    constexpr std::string_view keyword1 = "import";
    constexpr std::string_view keyword2 = "STRING:";

    const std::filesystem::path &filepath = object->getFile();
    const uhdm::Constant *const constant = object->getItem();

    std::string value(constant->getValue());
    size_t pos = value.find(keyword2);
    if (pos == 0) {
      value = value.substr(keyword2.length());
    }

    std::string text;
    text.append(keyword1)
        .append(1, kOverwriteMarker)
        .append(object->getName())
        .append("::")
        .append(value)
        .append(";");

    insert(filepath, object->getStartLine(),
           object->getStartColumn() - keyword1.length() - 1, text);
  }

  void enterDistItem(const uhdm::DistItem *const object,
                     uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterDistribution(const uhdm::Distribution *const object,
                         uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterImplication(const uhdm::Implication *const object,
                        uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterConstrIf(const uhdm::ConstrIf *const object,
                     uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterConstrIfElse(const uhdm::ConstrIfElse *const object,
                         uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterConstrForeach(const uhdm::ConstrForeach *const object,
                          uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterSoftDisable(const uhdm::SoftDisable *const object,
                        uint32_t vpiRelation) final {
    // Test file not available.
  }

  void enterSourceFile(const uhdm::SourceFile *const object,
                       uint32_t vpiRelation) final {
    if (m_visited.find(object) != m_visited.end()) return;
    if ((object->getStartLine() == 0) || (object->getStartColumn() == 0))
      return;

    constexpr std::string_view keyword = "`include";

    const std::filesystem::path &filepath = object->getFile();

    if (uhdm::SourceFileCollection *includes = object->getIncludes()) {
      for (const uhdm::SourceFile *included : *includes) {
        std::string text;
        text.assign(keyword)
            .append(" \"")
            .append(included->getName())
            .append("\"");

        insert(filepath, object->getStartLine(),
               object->getStartColumn() - keyword.length() - 1, text);
      }
    }
  }

  void enterDesign(const uhdm::Design *const object,
                   uint32_t vpiRelation) final {}

  void enterPackageCollection(const uhdm::Any *const object,
                              const uhdm::PackageCollection &objects,
                              uint32_t vpiRelation) final {
    if (vpiRelation == vpiAllPackages) {
      for (uhdm::PackageCollection::const_reference package : objects) {
        package->setTop(false);
      }
    } else if (vpiRelation == vpiTopPackages) {
      for (uhdm::PackageCollection::const_reference package : objects) {
        package->setTop(true);
        m_visited.insert(package);
      }
    }
  }

  void enterModuleCollection(const uhdm::Any *const object,
                             const uhdm::ModuleCollection &objects,
                             uint32_t vpiRelation) final {
    if (vpiRelation == vpiAllModules) {
      for (uhdm::ModuleCollection::const_reference module : objects) {
        module->setTop(false);
      }
    } else if (vpiRelation == vpiTopModules) {
      for (uhdm::ModuleCollection::const_reference module : objects) {
        module->setTop(true);
        m_visited.insert(module);
      }
    }
  }

  void enterTableEntryCollection(const uhdm::Any *const object,
                                 const uhdm::TableEntryCollection &objects,
                                 uint32_t vpiRelation) final {
    const std::filesystem::path &filepath = object->getFile();

    const uhdm::TableEntry *const entry0 = objects.front();
    insert(filepath, entry0->getStartLine() - 1, entry0->getStartColumn(),
           "table");

    const uhdm::TableEntry *const entryN = objects.back();
    insert(filepath, entryN->getEndLine() + 1, entry0->getStartColumn(),
           "endtable");
  }
};

static std::string stripDecorations(const std::string &arg) {
  std::string result = arg;
  result = std::regex_replace(result, re_add_optional_brackets, "$1 $2();");
  result = std::regex_replace(result, re_strip_space, "");
  result = std::regex_replace(result, re_strip_single_line_comments, "");
  result = std::regex_replace(result, re_strip_block_comments, "");
  result = std::regex_replace(result, re_strip_trailing_semicolon, "");
  return result;
}

static comparison_result_t compare(const std::filesystem::path &filepath,
                                   const file_content_t &content) {
  size_t diffCount = 0;
  size_t index = 0;
  std::ifstream strm;
  strm.open(filepath);
  if (strm.good()) {
    std::string pristine;
    while (std::getline(strm, pristine) && (index < content.size())) {
      const std::string lhs = stripDecorations(pristine);

      const std::string &generated = content[index++];
      const std::string rhs = stripDecorations(generated);

      if (lhs != rhs) {
        ++diffCount;
      }
    }
    strm.close();
  }

  return comparison_result_t(diffCount, index);
}

static int32_t run(const std::vector<vpiHandle> &designHandles,
                   const std::filesystem::path &baseDir,
                   const std::filesystem::path &outDir) {
  std::error_code ec;
  std::filesystem::create_directories(outDir, ec);

  design_statistics_t designStatistics;
  std::unordered_set<std::string> filenames;
  int32_t longestLHSFilepath = 0;
  int32_t longestRHSFilepath = 0;
  for (const vpiHandle &handle : designHandles) {
    const uhdm::Design *const design =
        (const uhdm::Design *)((const uhdm_handle *)handle)->object;
    RoundTripTracer listener(design);
    listener.listenDesign(design);

    for (auto &entry : listener.contents) {
      std::filesystem::path lhs_filepath = entry.first;
      if (lhs_filepath.is_relative()) {
        lhs_filepath = baseDir / lhs_filepath;
      }
      lhs_filepath = std::filesystem::weakly_canonical(lhs_filepath);

      std::filesystem::path rhs_filepath;
      const std::string stem = lhs_filepath.stem().string();
      const std::string extension = lhs_filepath.extension().string();
      for (int32_t i = 0;; ++i) {
        std::ostringstream strm;
        strm << stem << "_" << std::setfill('0') << std::setw(3) << i
             << extension;
        std::string candidate = strm.str();
        if (filenames.find(candidate) == filenames.end()) {
          filenames.insert(candidate);
          rhs_filepath = outDir / candidate;
          break;
        }
      }
      rhs_filepath = std::filesystem::weakly_canonical(rhs_filepath);

      std::ofstream strm(rhs_filepath.string());
      for (const std::string &line : entry.second) {
        strm << line << std::endl;
      }
      strm.flush();
      strm.close();

      comparison_result_t result = compare(lhs_filepath, entry.second);
      designStatistics.emplace_back(lhs_filepath, rhs_filepath, result.first,
                                    result.second);

      longestLHSFilepath =
          std::max<int32_t>(longestLHSFilepath, lhs_filepath.string().length());
      longestRHSFilepath =
          std::max<int32_t>(longestRHSFilepath, rhs_filepath.string().length());
    }
  }

  std::cout << std::endl;
  constexpr std::string_view separator = " | ";
  for (design_statistics_t::const_reference entry : designStatistics) {
    std::cout << "[roundtrip]: " << std::left << std::setw(longestLHSFilepath)
              << std::get<0>(entry).string() << separator
              << std::setw(longestRHSFilepath) << std::get<1>(entry).string()
              << separator << std::right << std::get<2>(entry) << separator
              << std::right << std::get<3>(entry) << separator << std::endl;
  }
  std::cout << std::endl;

  return 0;
}

static int usage(const char *const progname) {
  fprintf(stderr, "Usage: All options identical to surelog.exe.\n");
  return 1;
}

int main(int argc, const char **argv) {
  if (argc < 2) return usage(argv[0]);

#if defined(_MSC_VER) && defined(_DEBUG)
  // Redirect cout to file
  std::streambuf *cout_rdbuf = nullptr;
  std::streambuf *cerr_rdbuf = nullptr;
  std::ofstream file;
  if (IsDebuggerPresent() != 0) {
    file.open("cout.txt");
    cout_rdbuf = std::cout.rdbuf(file.rdbuf());
    cerr_rdbuf = std::cerr.rdbuf(file.rdbuf());
  }
#endif

  // Read command line, compile a design, use -parse argument
  int32_t code = 0;

  SURELOG::Session session;
  SURELOG::FileSystem *const fileSystem = session.getFileSystem();
  SURELOG::ErrorContainer *const errors = session.getErrorContainer();
  SURELOG::CommandLineParser *const clp = session.getCommandLineParser();
  bool success = session.parseCommandLine(argc, argv, false, false);
  clp->noPython();
  clp->setElaborate(false);
  clp->setElabUhdm(false);  // Force disable elaboration!
  clp->setCoverUhdm(false);
  // clp->setDebugAstModel(false);
  clp->setDebugUhdm(true);
  clp->showVpiIds(true);
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

  if (vpi_design != nullptr) {
    std::filesystem::path logDir = fileSystem->toPath(clp->getOutputDirId());
    if (logDir.is_relative()) {
      logDir = std::filesystem::current_path() / logDir;
    }
    logDir = std::filesystem::weakly_canonical(logDir);

    code = run({vpi_design}, std::filesystem::current_path(), logDir);
  }

  // Do not delete these objects until you are done with UHDM
  SURELOG::shutdown_compiler(compiler);

#if defined(_MSC_VER) && defined(_DEBUG)
  // Redirect cout back to screen
  if (cout_rdbuf != nullptr) {
    std::cout.rdbuf(cout_rdbuf);
  }
  if (cerr_rdbuf != nullptr) {
    std::cerr.rdbuf(cerr_rdbuf);
  }
  if (file.is_open()) {
    file.flush();
    file.close();
  }
#endif

  return code;
}
