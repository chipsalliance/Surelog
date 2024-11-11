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
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <regex>
#include <sstream>
#include <stack>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "Surelog/API/Surelog.h"
#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/PlatformFileSystem.h"
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
using typespec_names_t =
    std::unordered_map<UHDM::UHDM_OBJECT_TYPE, std::string_view>;
using variable_type_names_t =
    std::unordered_map<UHDM::UHDM_OBJECT_TYPE, std::string_view>;
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
  { UHDM::uhdmarray_typespec, "" },
  { UHDM::uhdmbit_typespec, "bit" },
  { UHDM::uhdmbyte_typespec, "byte" },
  { UHDM::uhdmchandle_typespec, "" },
  { UHDM::uhdmclass_typespec, "" },
  { UHDM::uhdmenum_typespec, "" },
  { UHDM::uhdmevent_typespec, "" },
  { UHDM::uhdmimport_typespec, "import" },
  { UHDM::uhdmint_typespec, "int" },
  { UHDM::uhdminteger_typespec, "integer" },
  { UHDM::uhdminterface_typespec, "" },
  { UHDM::uhdmlogic_typespec, "logic" },
  { UHDM::uhdmlong_int_typespec, "longint" },
  { UHDM::uhdmpacked_array_typespec, "" },
  { UHDM::uhdmproperty_typespec, "" },
  { UHDM::uhdmreal_typespec, "real" },
  { UHDM::uhdmsequence_typespec, "" },
  { UHDM::uhdmshort_int_typespec, "shortint" },
  { UHDM::uhdmshort_real_typespec, "shortreal" },
  { UHDM::uhdmstring_typespec, "string" },
  { UHDM::uhdmstruct_typespec, "" },
  { UHDM::uhdmtime_typespec, "time" },
  { UHDM::uhdmtype_parameter, "" },
  { UHDM::uhdmunion_typespec, "" },
  { UHDM::uhdmunsupported_typespec, "" },
  { UHDM::uhdmvoid_typespec, "void" },
};

static const variable_type_names_t kVariableTypeNames = {
 { UHDM::uhdmarray_var, "" },
 { UHDM::uhdmbit_var, "bit" },
 { UHDM::uhdmbyte_var, "byte" },
 { UHDM::uhdmchandle_var, "" },
 { UHDM::uhdmclass_var, "" },
 { UHDM::uhdmenum_var, "" },
 { UHDM::uhdmint_var, "int" },
 { UHDM::uhdminteger_var, "int" },
 { UHDM::uhdmlogic_var, "logic" },
 { UHDM::uhdmlong_int_var, "longint" },
 { UHDM::uhdmpacked_array_var, "" },
 { UHDM::uhdmreal_var, "float" },
 { UHDM::uhdmref_var, "" },
 { UHDM::uhdmshort_int_var, "shortint" },
 { UHDM::uhdmshort_real_var, "shortfloat" },
 { UHDM::uhdmstring_var, "string" },
 { UHDM::uhdmstruct_var, "" },
 { UHDM::uhdmtime_var, "" },
 { UHDM::uhdmunion_var, "" },
 { UHDM::uhdmvar_bit, "" },
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

class RoundTripTracer final : public UHDM::UhdmListener {
 public:
  explicit RoundTripTracer(const UHDM::design *const design) : design(design) {}
  ~RoundTripTracer() final = default;

 public:
  const UHDM::design *const design = nullptr;
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

  inline static bool isModuleDefinition(const UHDM::module_inst *const mdl) {
    return ((mdl->VpiParent() == nullptr) ||
            (mdl->VpiParent()->UhdmType() != UHDM::uhdmmodule_inst)) &&
           mdl->VpiName().empty();
  }

  inline static bool isInterfaceDefinition(
      const UHDM::interface_inst *const mdl) {
    return ((mdl->VpiParent() == nullptr) ||
            (mdl->VpiParent()->UhdmType() != UHDM::uhdminterface_inst)) &&
           mdl->VpiName().empty();
  }

  inline bool isWalkingModuleDefinition() const {
    for (any_stack_t::const_reverse_iterator it = callstack.rbegin(),
                                             rend = callstack.rend();
         it != rend; ++it) {
      const UHDM::any *const any = *it;
      if (any->UhdmType() == UHDM::uhdmmodule_inst) {
        return isModuleDefinition(static_cast<const UHDM::module_inst *>(any));
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

  inline std::string getTypespecName(const UHDM::typespec *const object) {
    constexpr std::string_view keyword = "unsigned";

    if (const UHDM::ref_typespec *const rt = object->Typedef_alias()) {
      if (const UHDM::typespec *const alias = rt->Actual_typespec()) {
        return getTypespecName(alias);
      }
    }

    const std::string_view name = object->VpiName();
    if (!name.empty()) return formatName(name);

    std::string text;
    typespec_names_t::const_iterator it =
        kTypespecNames.find(object->UhdmType());
    if (it != kTypespecNames.end()) {
      text.append(it->second);
      if (object->UhdmType() != UHDM::uhdmlogic_typespec) {
        text.append(1, kOverwriteMarker);
      }
    }

    switch (object->UhdmType()) {
      case UHDM::uhdmbyte_typespec: {
        if (!static_cast<const UHDM::byte_typespec *>(object)->VpiSigned()) {
          text.append(keyword);
        }
      } break;

      case UHDM::uhdmint_typespec: {
        if (!static_cast<const UHDM::int_typespec *>(object)->VpiSigned()) {
          text.append(keyword);
        }
      } break;

      case UHDM::uhdminteger_typespec: {
        if (!static_cast<const UHDM::integer_typespec *>(object)->VpiSigned()) {
          text.append(keyword);
        }
      } break;

      case UHDM::uhdmlong_int_typespec: {
        if (!static_cast<const UHDM::long_int_typespec *>(object)
                 ->VpiSigned()) {
          text.append(keyword);
        }
      } break;

      case UHDM::uhdmshort_int_typespec: {
        if (!static_cast<const UHDM::short_int_typespec *>(object)
                 ->VpiSigned()) {
          text.append(keyword);
        }
      } break;

      case UHDM::uhdmbit_typespec:
      case UHDM::uhdmlogic_typespec: {
        const UHDM::VectorOfrange *const ranges =
            static_cast<const UHDM::logic_typespec *>(object)->Ranges();
        if ((ranges != nullptr) && !ranges->empty()) {
          text.resize(object->VpiEndColumnNo() - object->VpiColumnNo(),
                      kOverwriteMarker);
        }
      } break;

      default:
        break;
    }

    return text;
  }

  void enterVariables_(const UHDM::variables *const object) {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "automatic";
    constexpr std::string_view keyword2 = "unsigned";
    const std::filesystem::path &filepath = object->VpiFile();

    std::string prefix;
    const std::string name = formatName(object->VpiName());

    const UHDM::typespec *ts = nullptr;
    if (const UHDM::ref_typespec *const rt = object->Typespec()) {
      ts = rt->Actual_typespec();
    }

    if (ts != nullptr) {
      prefix.append(getTypespecName(ts));
      if (ts->VpiColumnNo() != 0) {
        insert(filepath, ts->VpiLineNo(), ts->VpiColumnNo(), prefix);
        prefix.clear();
      } else {
        prefix.append(1, kOverwriteMarker);
      }
    } else if (object->UhdmType() == UHDM::uhdmarray_var) {
      const UHDM::VectorOfvariables *const variables =
          static_cast<const UHDM::array_var *>(object)->Variables();
      if ((variables != nullptr) && !variables->empty()) {
        const UHDM::variables *const variable = variables->at(0);
        if (const UHDM::ref_typespec *const rt = variable->Typespec()) {
          ts = rt->Actual_typespec();
        }
        if (ts != nullptr) {
          prefix.append(getTypespecName(ts));
          if (ts->VpiColumnNo() != 0) {
            insert(filepath, ts->VpiLineNo(), ts->VpiColumnNo(), prefix);
            prefix.clear();
          } else {
            prefix.append(1, kOverwriteMarker);
          }
        }
      }
    } else {
      if (object->VpiAutomatic()) {
        prefix.append(keyword1).append(1, kOverwriteMarker);
      }

      variable_type_names_t::const_iterator it =
          kVariableTypeNames.find(object->UhdmType());
      if (it != kVariableTypeNames.end()) {
        prefix.append(it->second);
      }

      if (object->UhdmType() == UHDM::uhdmlogic_var) {
        const UHDM::VectorOfrange *const ranges =
            static_cast<const UHDM::logic_var *>(object)->Ranges();
        if ((ranges != nullptr) && !ranges->empty()) {
          const UHDM::range *const range0 = ranges->front();
          const UHDM::range *const rangeN = ranges->back();
          prefix.append(rangeN->VpiEndColumnNo() - range0->VpiColumnNo(),
                        kOverwriteMarker);
        }
      } else if (!object->VpiSigned()) {
        switch (object->UhdmType()) {
          case UHDM::uhdmbyte_var:
          case UHDM::uhdmint_var:
          case UHDM::uhdminteger_var:
          case UHDM::uhdmlong_int_var:
          case UHDM::uhdmshort_int_var: {
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

    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - prefix.length(), text);

    if (const UHDM::expr *const expr = object->Expr()) {
      insert(filepath, expr->VpiLineNo(), expr->VpiColumnNo() - 1, "=");
    }
  }

  void enterTypespec(const UHDM::typespec *const object) {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "unsigned";

    const std::filesystem::path &filepath = object->VpiFile();

    const UHDM::typespec *typespec = object;
    if (object->UhdmType() == UHDM::uhdmarray_typespec) {
      if (const UHDM::ref_typespec *const element_typespec =
              static_cast<const UHDM::array_typespec *>(object)
                  ->Elem_typespec()) {
        typespec = element_typespec->Actual_typespec();
      }
    } else if (object->UhdmType() == UHDM::uhdmpacked_array_typespec) {
      if (const UHDM::ref_typespec *const element_typespec =
              static_cast<const UHDM::packed_array_typespec *>(object)
                  ->Elem_typespec()) {
        typespec = element_typespec->Actual_typespec();
      }
    }

    std::string text(typespec->VpiName());
    if (text.empty()) {
      typespec_names_t::const_iterator it =
          kTypespecNames.find(typespec->UhdmType());
      if (it != kTypespecNames.end()) {
        text.assign(it->second);
      }
    } else {
      text = formatName(text);
    }

    switch (typespec->UhdmType()) {
      case UHDM::uhdmenum_typespec: {
        const UHDM::enum_typespec *const enum_typespec =
            static_cast<const UHDM::enum_typespec *>(typespec);
        if (const UHDM::ref_typespec *const rt =
                enum_typespec->Typedef_alias()) {
          if (const UHDM::typespec *const alias = rt->Actual_typespec()) {
            text = formatName(alias->VpiName());
          }
        }
      } break;

      case UHDM::uhdmstruct_typespec: {
        const UHDM::struct_typespec *const struct_typespec =
            static_cast<const UHDM::struct_typespec *>(typespec);
        if (const UHDM::ref_typespec *const rt =
                struct_typespec->Typedef_alias()) {
          if (const UHDM::typespec *const alias = rt->Actual_typespec()) {
            text = formatName(alias->VpiName());
          }
        }
      } break;

      case UHDM::uhdmbyte_typespec: {
        if (!static_cast<const UHDM::byte_typespec *>(typespec)->VpiSigned()) {
          if (!text.empty()) text.append(1, kOverwriteMarker);
          text.append(keyword);
        }
      } break;

      case UHDM::uhdmint_typespec: {
        if (!static_cast<const UHDM::int_typespec *>(typespec)->VpiSigned()) {
          if (!text.empty()) text.append(1, kOverwriteMarker);
          text.append(keyword);
        }
      } break;

      case UHDM::uhdminteger_typespec: {
        if (!static_cast<const UHDM::integer_typespec *>(typespec)
                 ->VpiSigned()) {
          if (!text.empty()) text.append(1, kOverwriteMarker);
          text.append(keyword);
        }
      } break;

      case UHDM::uhdmlong_int_typespec: {
        if (!static_cast<const UHDM::long_int_typespec *>(typespec)
                 ->VpiSigned()) {
          if (!text.empty()) text.append(1, kOverwriteMarker);
          text.append(keyword);
        }
      } break;

      case UHDM::uhdmshort_int_typespec: {
        if (!static_cast<const UHDM::short_int_typespec *>(typespec)
                 ->VpiSigned()) {
          if (!text.empty()) text.append(1, kOverwriteMarker);
          text.append(keyword);
        }
      } break;

      default:
        break;
    }

    insert(filepath, typespec->VpiLineNo(), typespec->VpiColumnNo(), text);
  }

 public:
  void enterAny(const UHDM::any *const object) override {
    if ((object->UhdmType() == UHDM::uhdmpackage) &&
        (static_cast<const UHDM::package *>(object)->VpiName() == "builtin")) {
      // Ignore the built-in package
      visited.insert(object);
      return;
    }

    const UHDM::any *parent = object->VpiParent();
    while (parent != nullptr) {
      if ((parent->UhdmType() == UHDM::uhdmpackage) &&
          static_cast<const UHDM::package *>(parent)->VpiTop()) {
        visited.insert(object);
        return;
      }

      if ((parent->UhdmType() == UHDM::uhdmmodule_inst) &&
          static_cast<const UHDM::module_inst *>(parent)->VpiTop()) {
        visited.insert(object);
        return;
      }

      parent = parent->VpiParent();
    }
  }

  void enterAttribute(const UHDM::attribute *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "(* ";
    constexpr std::string_view keyword2 = " *)";

    const std::filesystem::path &filepath = object->VpiFile();

    const std::string name = formatName(object->VpiName());
    if (name.empty()) return;

    std::string text;
    text.append(keyword1).append(name);
    std::string value = formatValue(object->VpiValue());
    if (!value.empty()) {
      text.append("=").append(value);
    }
    text.append(keyword2);
    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - keyword1.length(), text);
  }

  void enterVirtual_interface_var(
      const UHDM::virtual_interface_var *const object) final {
    // Test file not available.
  }

  void enterLet_decl(const UHDM::let_decl *const object) final {
    // Test file not available.
  }

  void enterAlways(const UHDM::always *const object) final {
    if (visited.find(object) != visited.end()) return;

    always_type_names_t::const_iterator it =
        kAlwaysTypeNames.find(object->VpiAlwaysType());

    const std::filesystem::path &filepath = object->VpiFile();
    if (it != kAlwaysTypeNames.end()) {
      insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), it->second);
    }
  }

  void enterFinal_stmt(const UHDM::final_stmt *const object) final {
    // Test file not available.
  }

  void enterInitial(const UHDM::initial *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "initial";

    const std::filesystem::path &filepath = object->VpiFile();
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword);
  }

  void enterDelay_control(const UHDM::delay_control *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           object->VpiDelay());
  }

  void enterDelay_term(const UHDM::delay_term *const object) final {
    // Test file not available.
  }

  void enterEvent_control(const UHDM::event_control *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    if (const UHDM::any *const condition = object->VpiCondition()) {
      insert(filepath, condition->VpiLineNo(), condition->VpiColumnNo() - 2,
             "@(");
      insert(filepath, condition->VpiEndLineNo(), condition->VpiEndColumnNo(),
             ")");
    } else {
      insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), "@(*)");
    }
  }

  void enterRepeat_control(const UHDM::repeat_control *const object) final {}

  void enterBegin(const UHDM::begin *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "begin";
    constexpr std::string_view keyword2 = "end";

    const std::filesystem::path &filepath = object->VpiFile();
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword1);
    insert(filepath, object->VpiEndLineNo(),
           object->VpiEndColumnNo() - keyword2.length(), keyword2);
  }

  void enterNamed_begin(const UHDM::named_begin *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "begin:";
    constexpr std::string_view keyword2 = "end";

    const std::filesystem::path &filepath = object->VpiFile();
    const std::string name = formatName(object->VpiName());

    std::string text;

    text.assign(keyword1).append(name);
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiEndLineNo(),
           object->VpiEndColumnNo() - keyword2.length(), keyword2);
  }

  void enterNamed_fork(const UHDM::named_fork *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "fork";
    constexpr std::string_view keyword2 = "join";

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.append(keyword1).append(":").append(formatName(object->VpiName()));

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiEndLineNo(),
           object->VpiEndColumnNo() - keyword2.length(), keyword2);
  }

  void enterFork_stmt(const UHDM::fork_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "fork";
    constexpr std::string_view keyword2 = "join";

    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword1);
    insert(filepath, object->VpiEndLineNo(),
           object->VpiEndColumnNo() - keyword2.length(), keyword2);
  }

  void enterFor_stmt(const UHDM::for_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "for";
    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword);
    insert(filepath, object->VpiLineNo(), object->VpiEndColumnNo(), "(");

    const UHDM::VectorOfany *const inits = object->VpiForInitStmts();
    if ((inits != nullptr) && !inits->empty()) {
      for (int32_t i = 0, ni = inits->size() - 1; i < ni; ++i) {
        const UHDM::any *const init = inits->at(i);
        insert(filepath, init->VpiLineNo(), init->VpiEndColumnNo(), ",");
      }

      const UHDM::any *const initN = inits->back();
      insert(filepath, initN->VpiLineNo(), initN->VpiEndColumnNo(), ";");
    } else if (const UHDM::any *const init = object->VpiForInitStmt()) {
      insert(filepath, init->VpiLineNo(), init->VpiEndColumnNo(), ";");
    }

    if (const UHDM::any *const condition = object->VpiCondition()) {
      insert(filepath, condition->VpiLineNo(), condition->VpiEndColumnNo(),
             ";");
    }

    const UHDM::VectorOfany *const incs = object->VpiForIncStmts();
    if ((incs != nullptr) && !incs->empty()) {
      for (int32_t i = 0, ni = incs->size() - 1; i < ni; ++i) {
        const UHDM::any *const inc = incs->at(i);
        insert(filepath, inc->VpiLineNo(), inc->VpiEndColumnNo(), ",");
      }

      const UHDM::any *const incN = incs->back();
      insert(filepath, incN->VpiLineNo(), incN->VpiEndColumnNo(), ")");
    } else if (const UHDM::any *const inc = object->VpiForIncStmt()) {
      insert(filepath, inc->VpiLineNo(), inc->VpiEndColumnNo(), ")");
    }
  }

  void enterIf_stmt(const UHDM::if_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "if";

    const std::filesystem::path &filepath = object->VpiFile();
    const UHDM::expr *const condition = object->VpiCondition();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword);
    insert(filepath, condition->VpiLineNo(), condition->VpiColumnNo() - 1, "(");
    insert(filepath, condition->VpiEndLineNo(), condition->VpiEndColumnNo(),
           ")");
  }

  void enterEvent_stmt(const UHDM::event_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "->";
    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.append(keyword)
        .append(1, kOverwriteMarker)
        .append(formatName(object->VpiName()))
        .append(";");
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
  }

  void enterThread_obj(const UHDM::thread_obj *const object) final {
    // Test file not available.
  }

  void enterForever_stmt(const UHDM::forever_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "forever";

    const std::filesystem::path &filepath = object->VpiFile();
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword);
  }

  void enterWait_stmt(const UHDM::wait_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "wait";
    const std::filesystem::path &filepath = object->VpiFile();
    const UHDM::any *const condition = object->VpiCondition();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword1);
    insert(filepath, condition->VpiLineNo(), condition->VpiColumnNo() - 1, "(");
    insert(filepath, condition->VpiEndLineNo(), condition->VpiEndColumnNo(),
           ");");
  }

  void enterWait_fork(const UHDM::wait_fork *const object) final {
    // Test file not available.
  }

  void enterOrdered_wait(const UHDM::ordered_wait *const object) final {
    // Test file not available.
  }

  void enterDisable(const UHDM::disable *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "disable";
    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.append(keyword1).append(1, kOverwriteMarker);

    if (const UHDM::expr *const expr = object->VpiExpr<UHDM::expr>()) {
      text.append(expr->VpiName());
    } else if (const UHDM::scope *const scope =
                   object->VpiExpr<UHDM::scope>()) {
      text.append(scope->VpiName());
    }

    text.append(";");

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
  }

  void enterDisable_fork(const UHDM::disable_fork *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "disable fork;";
    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword1);
  }

  void enterContinue_stmt(const UHDM::continue_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "continue;";
    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword1);
  }

  void enterBreak_stmt(const UHDM::break_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "break;";
    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword1);
  }

  void enterReturn_stmt(const UHDM::return_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), "return");
  }

  void enterWhile_stmt(const UHDM::while_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "while";
    const std::filesystem::path &filepath = object->VpiFile();
    const UHDM::any *const condition = object->VpiCondition();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword1);
    insert(filepath, condition->VpiLineNo(), condition->VpiColumnNo() - 1, "(");
    insert(filepath, condition->VpiEndLineNo(), condition->VpiEndColumnNo(),
           ")");
  }

  void enterRepeat(const UHDM::repeat *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "repeat";
    const std::filesystem::path &filepath = object->VpiFile();
    const UHDM::any *const condition = object->VpiCondition();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword1);
    insert(filepath, condition->VpiLineNo(), condition->VpiColumnNo() - 1, "(");
    insert(filepath, condition->VpiEndLineNo(), condition->VpiEndColumnNo(),
           ")");
  }

  void enterDo_while(const UHDM::do_while *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "do";
    constexpr std::string_view keyword2 = "while";

    const std::filesystem::path &filepath = object->VpiFile();

    const UHDM::expr *const condition = object->VpiCondition();

    std::string text;
    text.append(keyword2).append("(");

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword1);
    insert(filepath, condition->VpiLineNo(),
           condition->VpiColumnNo() - text.length(), text);
    insert(filepath, condition->VpiEndLineNo(), condition->VpiEndColumnNo(),
           ");");
  }

  void enterIf_else(const UHDM::if_else *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "if";
    constexpr std::string_view keyword2 = "else";

    const std::filesystem::path &filepath = object->VpiFile();

    const UHDM::any *const ifStmt = object->VpiStmt();
    const UHDM::any *const elseStmt = object->VpiElseStmt();
    const UHDM::expr *const condition = object->VpiCondition();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword1);
    insert(filepath, condition->VpiLineNo(), condition->VpiColumnNo() - 1, "(");
    insert(filepath, condition->VpiEndLineNo(), condition->VpiEndColumnNo(),
           ")");

    // Check if the "else" keyword is on its own line
    if ((elseStmt->VpiLineNo() - ifStmt->VpiEndLineNo()) >= 2) {
      insert(filepath, ifStmt->VpiEndLineNo() + 1, object->VpiColumnNo(),
             keyword2);
    } else {
      insert(filepath, elseStmt->VpiLineNo(),
             elseStmt->VpiColumnNo() - keyword2.length() - 1, keyword2);
    }
  }

  void enterCase_stmt(const UHDM::case_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "endcase";
    // constexpr std::string_view keyword2 = "inside";

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    case_qualifier_names_t::const_iterator it1 =
        kCaseQualifierNames.find(object->VpiQualifier());
    if (it1 != kCaseQualifierNames.end()) {
      text.append(it1->second).append(1, kOverwriteMarker);
    }

    case_type_names_t::const_iterator it2 =
        kCaseTypeNames.find(object->VpiCaseType());
    if (it2 != kCaseTypeNames.end()) {
      text.append(it2->second);
    }

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiEndLineNo(),
           object->VpiEndColumnNo() - keyword1.length(), keyword1);

    const UHDM::expr *const condition = object->VpiCondition();
    insert(filepath, condition->VpiLineNo(), condition->VpiColumnNo() - 1, "(");
    insert(filepath, condition->VpiEndLineNo(), condition->VpiEndColumnNo(),
           ")");
  }

  void enterForce(const UHDM::force *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "force";

    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword);

    const UHDM::any *const lhs = object->Lhs();
    const UHDM::any *const rhs = object->Rhs();
    if ((lhs != nullptr) && (rhs != nullptr)) {
      insert(filepath, rhs->VpiLineNo(), rhs->VpiColumnNo() - 1, "=");
    }
  }

  void enterAssign_stmt(const UHDM::assign_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    // constexpr std::string_view keyword1 = "assign";

    const std::filesystem::path &filepath = object->VpiFile();

    // TODO(HS): This should basically be a check for implicit vs. explicit
    // but, unfortunately, there is nothing in the model to identify that.
    // if ((object->VpiParent() == nullptr) ||
    //     (object->VpiParent()->UhdmType() != UHDM::uhdmfor_stmt)) {
    //   insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword1);
    // }

    const UHDM::any *const lhs = object->Lhs();
    const UHDM::any *const rhs = object->Rhs();
    if ((lhs != nullptr) && (rhs != nullptr)) {
      insert(filepath, rhs->VpiLineNo(), rhs->VpiColumnNo() - 1, "=");
    }
  }

  void enterDeassign(const UHDM::deassign *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "deassign";

    const std::filesystem::path &filepath = object->VpiFile();

    if (const UHDM::any *const lhs = object->Lhs()) {
      insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword);
    }
  }

  void enterRelease(const UHDM::release *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "release";

    const std::filesystem::path &filepath = object->VpiFile();

    if (const UHDM::any *const lhs = object->Lhs()) {
      insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword);
    }
  }

  void enterNull_stmt(const UHDM::null_stmt *const object) final {
    // Test file not available.
  }

  void enterExpect_stmt(const UHDM::expect_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "expect";
    constexpr std::string_view keyword2 = ");";

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.append(keyword1).append("(");

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiEndLineNo(),
           object->VpiEndColumnNo() - keyword2.length(), keyword2);
  }

  void enterForeach_stmt(const UHDM::foreach_stmt *const object) final {
    // tests\DollarRoot, tests\UnitForeach
    // @todo: variables info is missing while decoding in foreach.
    // Need to revisit later.

    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "foreach";
    constexpr std::string_view keyword2 = ")";

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.append(keyword1).append("(");
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);

    if (const UHDM::any *const stmt = object->VpiStmt()) {
      insert(filepath, stmt->VpiLineNo(),
             stmt->VpiColumnNo() - keyword2.length() - 1, keyword2);
    }
  }

  void enterGen_scope(const UHDM::gen_scope *const object) final {
    // tests\BindStmt, tests\Bindings, tests\ArianeElab
  }

  void enterGen_var(const UHDM::gen_var *const object) final {
    // Test file not available.
  }

  void enterGen_scope_array(const UHDM::gen_scope_array *const object) final {
    // tests\BindStmt, tests\Bindings, tests\ArianeElab, tests\Cell ..
  }

  void enterAssert_stmt(const UHDM::assert_stmt *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "assert";
    constexpr std::string_view keyword2 = "else";

    const std::filesystem::path &filepath = object->VpiFile();
    const std::string name = formatName(object->VpiName());

    std::string prefix;
    if (!name.empty()) {
      prefix.append(name).append(":");
    }

    std::string text = prefix;
    text.append(keyword1);

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiLineNo(), object->VpiEndColumnNo() - 1, ";");

    if (const UHDM::any *const else_stmt = object->Else_stmt()) {
      const UHDM::any *const property = object->VpiProperty();
      insert(filepath, property->VpiEndLineNo(), property->VpiEndColumnNo() + 1,
             keyword2);
    }
  }

  void enterCover(const UHDM::cover *const object) final {
    // Test file not available.
  }

  void enterAssume(const UHDM::assume *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "assume";
    constexpr std::string_view keyword2 = "else";

    const std::filesystem::path &filepath = object->VpiFile();
    const std::string name = formatName(object->VpiName());

    std::string prefix;
    if (!name.empty()) {
      prefix.append(name).append(": ");
    }

    std::string text = prefix;
    text.append(keyword1);

    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - prefix.length(), text);

    if (const UHDM::any *const stmt = object->Stmt()) {
      const UHDM::any *const property = object->VpiProperty();
      insert(filepath, property->VpiEndLineNo(), property->VpiEndColumnNo() + 1,
             keyword2);
    }
  }

  void enterRestrict(const UHDM::restrict *const object) final {
    // Test file not available.
  }

  void enterImmediate_assert(const UHDM::immediate_assert *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "assert";

    const std::filesystem::path &filepath = object->VpiFile();
    const std::string name = formatName(object->VpiName());

    std::string text;
    if (!name.empty()) {
      text.append(name).append(":");
    }
    text.append(keyword).append("(");

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo() - 2,
           ");");
  }

  void enterImmediate_assume(const UHDM::immediate_assume *const object) final {
    // Test file not available.
  }

  void enterImmediate_cover(const UHDM::immediate_cover *const object) final {
    // Test file not available.
  }

  void enterCase_item(const UHDM::case_item *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "default:";

    const std::filesystem::path &filepath = object->VpiFile();

    const UHDM::VectorOfany *const exprs = object->VpiExprs();
    if ((exprs != nullptr) && !exprs->empty()) {
      for (int32_t i = 0, ni = exprs->size() - 1; i < ni; ++i) {
        const UHDM::any *const expr = exprs->at(i);
        insert(filepath, expr->VpiEndLineNo(), expr->VpiEndColumnNo(), ",");
      }

      const UHDM::any *const exprN = exprs->back();
      insert(filepath, exprN->VpiEndLineNo(), exprN->VpiEndColumnNo(), ":");
    } else {
      insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), keyword);
    }
  }

  void enterAssignment(const UHDM::assignment *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "=";
    constexpr std::string_view keyword2 = "<";

    const std::filesystem::path &filepath = object->VpiFile();

    const UHDM::any *const rhs = object->Rhs();
    uint32_t column = rhs->VpiColumnNo();
    // In case of delay, might be need to add one space.
    // Will revisit once get any test file.
    if (const UHDM::any *const delayCtrl = object->Delay_control()) {
      column = delayCtrl->VpiColumnNo();
    }

    std::string text;
    op_type_names_t::const_iterator it = kOpTypeNames.find(object->VpiOpType());
    if ((it != kOpTypeNames.end()) &&
        (object->VpiOpType() != vpiAssignmentOp)) {
      text.assign(it->second);
    }
    if (!object->VpiBlocking()) {
      text.append(keyword2);
    }
    text.append(keyword1);
    insert(filepath, rhs->VpiEndLineNo(), column - text.length(), text);
  }

  void enterAny_pattern(const UHDM::any_pattern *const object) final {
    // Test file not available.
  }

  void enterTagged_pattern(const UHDM::tagged_pattern *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    const UHDM::typespec *typespec = nullptr;
    if (const UHDM::ref_typespec *const rt = object->Typespec()) {
      typespec = rt->Actual_typespec();
    }

    const UHDM::any *const pattern = object->Pattern();
    if ((typespec != nullptr) && (pattern != nullptr)) {
      std::string value;
      switch (typespec->UhdmType()) {
        case UHDM::uhdmint_typespec:
          value = static_cast<const UHDM::int_typespec *>(typespec)->VpiValue();
          break;
        case UHDM::uhdminteger_typespec:
          value = static_cast<const UHDM::int_typespec *>(typespec)->VpiValue();
          break;
        default:
          break;
      };

      if (value.empty()) {
        insert(filepath, typespec->VpiLineNo(), typespec->VpiColumnNo(),
               getTypespecName(typespec));
      } else {
        value = formatValue(value, false);
        insert(filepath, typespec->VpiLineNo(), typespec->VpiColumnNo(), value);
      }

      insert(filepath, typespec->VpiLineNo(), typespec->VpiEndColumnNo(), ":");

      listenAny(pattern);
      visited.insert(object);
    }
  }

  void enterStruct_pattern(const UHDM::struct_pattern *const object) final {
    // Test file not available.
  }

  void enterUnsupported_expr(const UHDM::unsupported_expr *const object) final {
    // Test file not available.
  }

  void enterUnsupported_stmt(const UHDM::unsupported_stmt *const object) final {
    // Test file not available.
  }

  void enterSequence_inst(const UHDM::sequence_inst *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.append(formatName(object->VpiName())).append("(");

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo() - 1, ")");

    const UHDM::VectorOfany *const args =
        object->Named_event_sequence_expr_groups();
    if ((args != nullptr) && !args->empty()) {
      for (int32_t i = 0, n = args->size() - 1; i < n; ++i) {
        UHDM::VectorOfany::const_reference arg = args->at(i);
        insert(filepath, arg->VpiLineNo(), arg->VpiEndColumnNo(), ",");
      }
    }
  }

  void enterSeq_formal_decl(const UHDM::seq_formal_decl *const object) final {
    // Test file not available.
  }

  void enterSequence_decl(const UHDM::sequence_decl *const object) final {
    // Test file not available.
  }

  void enterProp_formal_decl(const UHDM::prop_formal_decl *const object) final {
    // Test file not available.
  }

  void enterProperty_inst(const UHDM::property_inst *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.append(formatName(object->VpiName())).append("(");

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo() - 1, ")");

    const UHDM::VectorOfany *const args = object->VpiArguments();
    if ((args != nullptr) && !args->empty()) {
      for (int32_t i = 0, n = args->size() - 1; i < n; ++i) {
        UHDM::VectorOfany::const_reference arg = args->at(i);
        insert(filepath, arg->VpiLineNo(), arg->VpiEndColumnNo(), ",");
      }
    }
  }

  void enterProperty_spec(const UHDM::property_spec *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "property(";
    constexpr std::string_view keyword2 = "@(";
    constexpr std::string_view keyword3 = ")";
    constexpr std::string_view keyword4 = ")";

    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - keyword1.length(), keyword1);
    insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo(),
           keyword4);

    if (const UHDM::expr *const clockingEvent = object->VpiClockingEvent()) {
      insert(filepath, clockingEvent->VpiLineNo(),
             clockingEvent->VpiColumnNo() - keyword2.length(), keyword2);
      insert(filepath, clockingEvent->VpiEndLineNo(),
             clockingEvent->VpiEndColumnNo(), keyword3);
    }
  }

  void enterProperty_decl(const UHDM::property_decl *const object) final {
    // Test file not available.
  }

  void enterClocked_property(const UHDM::clocked_property *const object) final {
    // Test file not available.
  }

  void enterCase_property_item(
      const UHDM::case_property_item *const object) final {
    // Test file not available.
  }

  void enterCase_property(const UHDM::case_property *const object) final {
    // Test file not available.
  }

  void enterMulticlock_sequence_expr(
      const UHDM::multiclock_sequence_expr *const object) final {
    // Test file not available.
  }

  void enterClocked_seq(const UHDM::clocked_seq *const object) final {
    // Test file not available.
  }

  void enterConstant(const UHDM::constant *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text = formatValue(object->VpiDecompile());
    if (object->VpiConstType() == vpiStringConst) {
      if ((text.size() < 2) || (text.front() != '\"') ||
          (text.back() != '\"')) {
        const std::string tmp_text = text;
        text.assign("\"").append(tmp_text).append("\"");
      }
    }
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);

    if (const UHDM::ref_typespec *const rt = object->Typespec()) {
      if (const UHDM::typespec *const typespec = rt->Actual_typespec()) {
        visited.insert(typespec);
      }
    }
  }

  void enterLet_expr(const UHDM::let_expr *const object) final {
    // Test file not available.
  }

  void enterOperation(const UHDM::operation *const object) final {
    if (visited.find(object) != visited.end()) return;

    op_type_names_t::const_iterator it = kOpTypeNames.find(object->VpiOpType());
    if (it == kOpTypeNames.end()) return;

    const UHDM::VectorOfany *const operands = object->Operands();
    if ((operands == nullptr) || operands->empty()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    switch (object->VpiOpType()) {
      case vpiConditionOp: {
        const UHDM::any *const operand0 = operands->at(0);
        const UHDM::any *const operand1 = operands->at(1);
        insert(filepath, operand0->VpiEndLineNo(), operand0->VpiEndColumnNo(),
               it->second);
        insert(filepath, operand1->VpiEndLineNo(), operand1->VpiEndColumnNo(),
               ":");
      } break;

      case vpiMinTypMaxOp:
      case vpiListOp: {
        for (int32_t i = 0, n = operands->size() - 1; i < n; ++i) {
          UHDM::VectorOfany::const_reference operand = operands->at(i);
          insert(filepath, operand->VpiEndLineNo(), operand->VpiEndColumnNo(),
                 it->second);
        }
      } break;

      case vpiConcatOp: {
        insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), "{");
        UHDM::VectorOfany ordered(operands->begin(), operands->end());
        if (object->VpiReordered()) {
          std::stable_sort(
              ordered.begin(), ordered.end(),
              [](const UHDM::any *const lhs, const UHDM::any *const rhs) {
                int32_t r = lhs->VpiLineNo() - rhs->VpiLineNo();
                if (r != 0) return r < 0;

                r = lhs->VpiColumnNo() - rhs->VpiColumnNo();
                if (r != 0) return r < 0;

                r = lhs->VpiEndLineNo() - rhs->VpiEndLineNo();
                if (r != 0) return r < 0;

                r = lhs->VpiEndColumnNo() - rhs->VpiEndColumnNo();
                return r < 0;
              });
        }

        for (int32_t i = 0, ni = ordered.size() - 1; i < ni; ++i) {
          const UHDM::any *const operand = ordered[i];
          insert(filepath, operand->VpiEndLineNo(), operand->VpiEndColumnNo(),
                 ",");
        }
        insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo() - 1,
               "}");
      } break;

      case vpiMultiConcatOp: {
        insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), "{");
        insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo() - 1,
               "}");
      } break;

      case vpiMultiAssignmentPatternOp: {
        insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), "'{");
        insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo() - 1,
               "};");
      } break;

      case vpiAssignmentPatternOp: {
        insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), "'{");
        for (int32_t i = 0, ni = operands->size() - 1; i < ni; ++i) {
          const UHDM::any *const operand = operands->at(i);
          insert(filepath, operand->VpiEndLineNo(), operand->VpiEndColumnNo(),
                 ",");
        }
        insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo() - 1,
               "};");
      } break;

      case vpiPostIncOp: {
        const UHDM::any *const operand0 = operands->at(0);
        insert(filepath, operand0->VpiEndLineNo(), operand0->VpiEndColumnNo(),
               it->second);
      } break;

      case vpiEqOp: {
        const UHDM::any *const operand1 = operands->at(1);
        insert(filepath, operand1->VpiLineNo(),
               operand1->VpiColumnNo() - it->second.length(), it->second);
      } break;

      case vpiEventOrOp: {
        const UHDM::any *const operand0 = operands->at(0);
        insert(filepath, operand0->VpiEndLineNo(),
               operand0->VpiEndColumnNo() + 1, it->second);
      } break;

      case vpiCycleDelayOp: {
        const UHDM::any *const operand1 = operands->at(1);
        insert(filepath, operand1->VpiLineNo(),
               operand1->VpiColumnNo() - it->second.length(), it->second);
      } break;

      default: {
        if (operands->size() == 1) {
          const UHDM::any *const operand0 = operands->at(0);
          insert(filepath, operand0->VpiLineNo(),
                 operand0->VpiColumnNo() - it->second.length(), it->second);
        } else if (operands->size() == 2) {
          const UHDM::any *const operand1 = operands->at(1);
          insert(filepath, operand1->VpiLineNo(),
                 operand1->VpiColumnNo() - it->second.length(), it->second);
        }
      } break;
    }
  }

  void enterPart_select(const UHDM::part_select *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    if (const UHDM::any *const parent = object->VpiParent()) {
      insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
             formatName(parent->VpiName()));
    }

    const UHDM::expr *const lr = object->Left_range();
    const UHDM::expr *const rr = object->Right_range();

    if ((lr != nullptr) && (rr != nullptr)) {
      insert(filepath, lr->VpiLineNo(), lr->VpiColumnNo() - 1, "[");
      insert(filepath, lr->VpiEndLineNo(), lr->VpiEndColumnNo(), ":");
      insert(filepath, rr->VpiEndLineNo(), rr->VpiEndColumnNo(), "]");
    }
  }

  void enterIndexed_part_select(
      const UHDM::indexed_part_select *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view kPosIndexed = "+:";
    constexpr std::string_view kNegIndexed = "-:";

    const UHDM::any *const parent = object->VpiParent();
    if (parent == nullptr) return;

    const std::filesystem::path &filepath = object->VpiFile();
    const std::string text = formatName(parent->VpiDefName());
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo() + text.length(),
           "[");
    insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo() - 1, "]");

    const UHDM::expr *const width = object->Width_expr();
    switch (object->VpiIndexedPartSelectType()) {
      case vpiPosIndexed: {
        insert(filepath, width->VpiLineNo(),
               width->VpiColumnNo() - kPosIndexed.length(), kPosIndexed);
      } break;

      case vpiNegIndexed: {
        insert(filepath, width->VpiLineNo(),
               width->VpiColumnNo() - kNegIndexed.length(), kNegIndexed);
      } break;
    };
  }

  void enterRef_obj(const UHDM::ref_obj *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    const UHDM::any *resolved = object->Actual_group();
    if (resolved == nullptr) {
      resolved = object;
    }

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(resolved->VpiName()));
  }

  void enterHier_path(const UHDM::hier_path *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    const UHDM::VectorOfany *const elements = object->Path_elems();
    if ((elements != nullptr) && !elements->empty()) {
      for (size_t i = 1, n = elements->size(); i < n; ++i) {
        const UHDM::any *const element = elements->at(i);
        insert(filepath, element->VpiLineNo(), element->VpiColumnNo() - 1, ".");
      }
    }
  }

  void enterVar_select(const UHDM::var_select *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();
    const std::string text = formatName(object->VpiName());

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
  }

  void enterBit_select(const UHDM::bit_select *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();
    std::string text = formatName(object->VpiName());

    if (const UHDM::expr *const index = object->VpiIndex()) {
      text.resize(index->VpiEndColumnNo() - object->VpiColumnNo() + 1,
                  kOverwriteMarker);
      text[index->VpiColumnNo() - object->VpiColumnNo() - 1] = '[';
      text[index->VpiEndColumnNo() - object->VpiColumnNo()] = ']';
    }

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
  }

  void enterRef_var(const UHDM::ref_var *const object) final {
    enterVariables_(object);
  }

  void enterShort_real_var(const UHDM::short_real_var *const object) final {
    enterVariables_(object);
  }

  void enterReal_var(const UHDM::real_var *const object) final {
    enterVariables_(object);
  }

  void enterByte_var(const UHDM::byte_var *const object) final {
    enterVariables_(object);
  }

  void enterShort_int_var(const UHDM::short_int_var *const object) final {
    enterVariables_(object);
  }

  void enterInt_var(const UHDM::int_var *const object) final {
    enterVariables_(object);
  }

  void enterLong_int_var(const UHDM::long_int_var *const object) final {
    enterVariables_(object);
  }

  void enterInteger_var(const UHDM::integer_var *const object) final {
    enterVariables_(object);
  }

  void enterTime_var(const UHDM::time_var *const object) final {
    enterVariables_(object);
  }

  void enterArray_var(const UHDM::array_var *const object) final {
    if (visited.find(object) != visited.end()) return;

    enterVariables_(object);

    const std::filesystem::path &filepath = object->VpiFile();

    if (const UHDM::ref_typespec *const rt = object->Typespec()) {
      if (const UHDM::typespec *const typespec = rt->Actual_typespec()) {
        insert(filepath, typespec->VpiLineNo(), typespec->VpiColumnNo() - 1,
               "[");
        insert(filepath, typespec->VpiEndLineNo(), typespec->VpiEndColumnNo(),
               "]");
      }
    }

    if (const UHDM::VectorOfvariables *const variables = object->Variables()) {
      std::copy(variables->begin(), variables->end(),
                std::inserter(visited, visited.end()));
    }
  }

  void enterReg_array(const UHDM::reg_array *const object) final {
    // Test file not available.
  }

  void enterReg(const UHDM::reg *const object) final {
    // Test file not available.
  }

  void enterPacked_array_var(const UHDM::packed_array_var *const object) final {
    enterVariables_(object);
  }

  void enterBit_var(const UHDM::bit_var *const object) final {
    enterVariables_(object);
  }

  void enterLogic_var(const UHDM::logic_var *const object) final {
    enterVariables_(object);
  }

  void enterStruct_var(const UHDM::struct_var *const object) final {
    enterVariables_(object);
  }

  void enterUnion_var(const UHDM::union_var *const object) final {
    enterVariables_(object);
  }

  void enterEnum_var(const UHDM::enum_var *const object) final {
    enterVariables_(object);
  }

  void enterString_var(const UHDM::string_var *const object) final {
    enterVariables_(object);
  }

  void enterChandle_var(const UHDM::chandle_var *const object) final {
    enterVariables_(object);
  }

  void enterVar_bit(const UHDM::var_bit *const object) final {
    enterVariables_(object);
  }

  void enterTask(const UHDM::task *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "task";
    constexpr std::string_view keyword2 = "endtask";
    constexpr std::string_view keyword3 = "virtual";
    constexpr std::string_view keyword4 = "pure";

    const std::filesystem::path &filepath = object->VpiFile();
    const bool isPureVirtual = object->VpiDPIPure();

    std::string text;
    if (isPureVirtual) {
      text.append(keyword4).append(1, kOverwriteMarker);
    }
    if (object->VpiVirtual()) {
      text.append(keyword3).append(1, kOverwriteMarker);
    }
    text.append(keyword1)
        .append(1, kOverwriteMarker)
        .append(formatName(object->VpiName()))
        .append("(");

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);

    if (!isPureVirtual) {
      insert(filepath, object->VpiEndLineNo(),
             object->VpiEndColumnNo() - keyword2.length(), keyword2);
    }

    int32_t end_line = object->VpiLineNo();
    int32_t end_column = object->VpiColumnNo() + text.length();
    const UHDM::VectorOfio_decl *const io_decls = object->Io_decls();
    if ((io_decls != nullptr) && !io_decls->empty()) {
      for (int32_t i = 0, ni = io_decls->size() - 1; i < ni; ++i) {
        const UHDM::io_decl *const io_decl = io_decls->at(i);
        if (const UHDM::any *const expr = io_decl->Expr()) {
          insert(filepath, expr->VpiLineNo(), expr->VpiColumnNo() - 1, "=");
          insert(filepath, expr->VpiEndLineNo(), expr->VpiEndColumnNo(), ",");
        } else {
          insert(filepath, io_decl->VpiEndLineNo(), io_decl->VpiEndColumnNo(),
                 ",");
        }
      }

      const UHDM::io_decl *const io_declN = io_decls->back();
      if (const UHDM::any *const exprN = io_declN->Expr()) {
        insert(filepath, exprN->VpiLineNo(), exprN->VpiColumnNo() - 1, "=");
        end_line = exprN->VpiEndLineNo();
        end_column = exprN->VpiEndColumnNo();
      } else {
        end_line = io_declN->VpiEndLineNo();
        end_column = io_declN->VpiEndColumnNo();
      }
    }

    insert(filepath, end_line, end_column, ");");
  }

  void enterFunction(const UHDM::function *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "function";
    constexpr std::string_view keyword2 = "automatic";
    constexpr std::string_view keyword3 = "endfunction";
    constexpr std::string_view keyword4 = "void";
    const std::filesystem::path &filepath = object->VpiFile();

    std::string text(keyword1);
    if (object->VpiAutomatic()) {
      text.append(1, kOverwriteMarker).append(keyword2);
    }

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);

    int32_t end_column = object->VpiColumnNo() + text.length();

    // NOTE(HS): For implicit return, the location data is never set
    if (const UHDM::variables *const returnValue = object->Return()) {
      if (returnValue->VpiEndColumnNo() > 0) {
        end_column = returnValue->VpiEndColumnNo();
      }
    } else {
      insert(filepath, object->VpiLineNo(), end_column + 1, keyword4);
      end_column += keyword4.length() + 1;
    }

    const std::string name = formatName(object->VpiName());
    insert(filepath, object->VpiLineNo(), end_column + 1, name);
    end_column += name.length() + 1;

    insert(filepath, object->VpiLineNo(), end_column, "(");

    const UHDM::VectorOfio_decl *const io_decls = object->Io_decls();
    if ((io_decls != nullptr) && !io_decls->empty()) {
      for (int32_t i = 0, ni = io_decls->size() - 1; i < ni; ++i) {
        UHDM::VectorOfio_decl::const_reference io_decl = io_decls->at(i);
        if (const UHDM::any *const expr = io_decl->Expr()) {
          insert(filepath, expr->VpiLineNo(), expr->VpiColumnNo() - 1, "=");
          insert(filepath, expr->VpiEndLineNo(), expr->VpiEndColumnNo(), ",");
        } else {
          insert(filepath, io_decl->VpiEndLineNo(), io_decl->VpiEndColumnNo(),
                 ",");
        }
      }

      UHDM::VectorOfio_decl::const_reference io_declN = io_decls->back();
      if (const UHDM::any *const exprN = io_declN->Expr()) {
        insert(filepath, exprN->VpiLineNo(), exprN->VpiColumnNo() - 1, "=");
        insert(filepath, exprN->VpiEndLineNo(), exprN->VpiEndColumnNo(), ");");
      } else {
        const UHDM::VectorOfrange *const ranges = io_declN->Ranges();
        if ((ranges != nullptr) && !ranges->empty()) {
          const UHDM::range *const rangeN = ranges->back();
          insert(filepath, io_declN->VpiEndLineNo(), rangeN->VpiEndColumnNo(),
                 ");");
        } else {
          insert(filepath, io_declN->VpiEndLineNo(), io_declN->VpiEndColumnNo(),
                 ");");
        }
      }
    } else {
      insert(filepath, object->VpiLineNo(), end_column + 1, ");");
    }

    insert(filepath, object->VpiEndLineNo(), object->VpiColumnNo(), keyword3);
  }

  void enterModport(const UHDM::modport *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "modport";

    const std::filesystem::path &filepath = object->VpiFile();

    std::string prefix(keyword);
    prefix.append(1, kOverwriteMarker);

    std::string text = prefix;
    text.append(formatName(object->VpiName()));

    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - prefix.length(), text);

    const UHDM::VectorOfio_decl *const io_decls = object->Io_decls();
    if ((io_decls != nullptr) && !io_decls->empty()) {
      insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo(), "(");

      for (int32_t i = 0, ni = io_decls->size() - 1; i < ni; ++i) {
        UHDM::VectorOfio_decl::const_reference io_decl = io_decls->at(i);
        insert(filepath, io_decl->VpiEndLineNo(), io_decl->VpiEndColumnNo(),
               ",");
      }

      UHDM::VectorOfio_decl::const_reference io_declN = io_decls->back();
      insert(filepath, io_declN->VpiEndLineNo(), io_declN->VpiEndColumnNo(),
             ")");
    } else {
      insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo(), "()");
    }
  }

  void enterInterface_tf_decl(
      const UHDM::interface_tf_decl *const object) final {
    // Test file not available.
  }

  void enterCont_assign(const UHDM::cont_assign *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "assign";

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text(keyword);

    if (const UHDM::any *const lhs = object->Lhs()) {
      text.resize(keyword.length() + 1 + lhs->VpiEndColumnNo() -
                      object->VpiColumnNo() + 1,
                  kOverwriteMarker);
      text[keyword.length() + 1 + lhs->VpiEndColumnNo() -
           object->VpiColumnNo()] = '=';
    }
    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - keyword.length() - 1, text);
  }

  void enterCont_assign_bit(const UHDM::cont_assign_bit *const object) final {
    // Test file not available.
  }

  void enterPort(const UHDM::port *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));
  }

  void enterPort_bit(const UHDM::port_bit *const object) final {
    // Test file not available.
  }

  void enterChecker_port(const UHDM::checker_port *const object) final {
    // Test file not available. Need to try with tests\CheckerInst
  }

  void enterChecker_inst_port(
      const UHDM::checker_inst_port *const object) final {
    // Test file not available.
  }

  void enterGate(const UHDM::gate *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.assign(formatName(object->VpiName()));

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);

    uint32_t column = object->VpiColumnNo();
    text.assign(formatName(object->VpiDefName()));

    if (const UHDM::expr *expr = object->Delay()) {
      if (expr->UhdmType() == UHDM::uhdmoperation) {
        const UHDM::VectorOfany *const operands =
            static_cast<const UHDM::operation *>(expr)->Operands();
        if ((operands != nullptr) && !operands->empty()) {
          UHDM::VectorOfany::const_reference operand0 = operands->front();
          UHDM::VectorOfany::const_reference operandN = operands->back();

          insert(filepath, operand0->VpiLineNo(), operand0->VpiColumnNo() - 2,
                 "#(");
          insert(filepath, operandN->VpiEndLineNo(), operandN->VpiEndColumnNo(),
                 ")");
        }
      }
      column = expr->VpiColumnNo();
    }
    insert(filepath, object->VpiLineNo(), column - text.length() - 1, text);

    column = object->VpiEndColumnNo();
    uint32_t endColumn = object->VpiEndColumnNo() + 1;
    const UHDM::VectorOfprim_term *const prims = object->Prim_terms();
    if ((prims != nullptr) && !prims->empty()) {
      for (int32_t i = 0, ni = prims->size() - 1; i < ni; ++i) {
        UHDM::VectorOfprim_term::const_reference prim = prims->at(i);
        insert(filepath, prim->VpiEndLineNo(), prim->VpiEndColumnNo(), ",");
      }

      UHDM::VectorOfprim_term::const_reference prim0 = prims->front();
      UHDM::VectorOfprim_term::const_reference primN = prims->back();
      column = prim0->VpiColumnNo() - 1;
      endColumn = primN->VpiEndColumnNo();
    }

    insert(filepath, object->VpiLineNo(), column, "(");
    insert(filepath, object->VpiEndLineNo(), endColumn, ");");
  }

  void enterSwitch_tran(const UHDM::switch_tran *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.assign(formatName(object->VpiName())).append("(");
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);

    text.assign(formatName(object->VpiDefName())).append(1, kOverwriteMarker);
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo() - text.length(),
           text);

    uint32_t column = object->VpiEndColumnNo();
    const UHDM::VectorOfprim_term *const prims = object->Prim_terms();
    if ((prims != nullptr) && !prims->empty()) {
      for (int32_t i = 0, ni = prims->size() - 1; i < ni; ++i) {
        UHDM::VectorOfprim_term::const_reference prim = prims->at(i);
        insert(filepath, prim->VpiEndLineNo(), prim->VpiEndColumnNo(), ",");
      }

      UHDM::VectorOfprim_term::const_reference primN = prims->back();
      column = primN->VpiEndColumnNo();
    }
    insert(filepath, object->VpiEndLineNo(), column, ");");
  }

  void enterUdp(const UHDM::udp *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "primitive";
    constexpr std::string_view keyword2 = "endprimitive";

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.append(keyword1)
        .append(1, kOverwriteMarker)
        .append(formatName(object->VpiDefName()));

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiEndLineNo(),
           object->VpiEndColumnNo() - keyword2.length(), keyword2);
  }

  void enterMod_path(const UHDM::mod_path *const object) final {
    // Test file not available.
  }

  void enterTchk(const UHDM::tchk *const object) final {
    // Test file not available.
  }

  void enterRange(const UHDM::range *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "unsized";

    const std::filesystem::path &filepath = object->VpiFile();

    uint32_t column = object->VpiColumnNo();
    uint32_t endColumn = object->VpiEndColumnNo();

    const UHDM::expr *const rexpr = object->Right_expr();
    if (rexpr->UhdmType() == UHDM::uhdmoperation) {  // single-range
      const UHDM::VectorOfany *const operands =
          static_cast<const UHDM::operation *>(rexpr)->Operands();
      if ((operands != nullptr) &&
          (operands->at(0)->UhdmType() == UHDM::uhdmconstant)) {
        std::string_view loperand =
            static_cast<const UHDM::constant *>(operands->at(0))
                ->VpiDecompile();
        insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), loperand);
        visited.insert(rexpr);
        visited.insert(object->Left_expr());

        column -= 1;  // It's a single range so set the start "[" to column - 1.
        endColumn += 1;
      }
    } else if (rexpr->VpiDecompile() == keyword) {  // unsized-range
      visited.insert(rexpr);
      visited.insert(object->Left_expr());
    } else {  // double-range
      insert(filepath, rexpr->VpiLineNo(), rexpr->VpiColumnNo() - 1, ":");
    }
    insert(filepath, object->VpiLineNo(), column, "[");
    insert(filepath, object->VpiEndLineNo(), endColumn - 1, "]");
  }

  void enterUdp_defn(const UHDM::udp_defn *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "primitive";
    constexpr std::string_view keyword2 = "endprimitive";

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.append(keyword1)
        .append(1, kOverwriteMarker)
        .append(formatName(object->VpiDefName()))
        .append("(");

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiEndLineNo(),
           object->VpiEndColumnNo() - keyword2.length(), keyword2);

    const UHDM::VectorOfio_decl *const io_decls = object->Io_decls();
    if ((io_decls != nullptr) && !io_decls->empty()) {
      for (int32_t i = 0, ni = io_decls->size() - 1; i < ni; ++i) {
        UHDM::VectorOfio_decl::const_reference io_decl = io_decls->at(i);
        insert(filepath, io_decl->VpiEndLineNo(), io_decl->VpiEndColumnNo(),
               ",");
      }
      UHDM::VectorOfio_decl::const_reference io_declN = io_decls->back();
      insert(filepath, io_declN->VpiEndLineNo(), io_declN->VpiEndColumnNo(),
             ")");
    } else {
      insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo() + 1,
             ")");
    }
  }

  void enterTable_entry(const UHDM::table_entry *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    const std::string text = formatValue(object->VpiValue(), false);
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
  }

  void enterIo_decl(const UHDM::io_decl *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    if (const UHDM::ref_typespec *const rt = object->Typespec()) {
      if (const UHDM::typespec *const typespec = rt->Actual_typespec()) {
        const std::string name = getTypespecName(typespec);
        switch (typespec->UhdmType()) {
          case UHDM::uhdmclass_typespec:
          case UHDM::uhdmenum_typespec:
          case UHDM::uhdmstruct_typespec: {
            insert(filepath, object->VpiLineNo(),
                   object->VpiColumnNo() - name.length() - 1, name);
          } break;

          default: {
            insert(filepath, typespec->VpiLineNo(), typespec->VpiColumnNo(),
                   name);
          } break;
        }
      }
    }

    std::string prefix;
    if (object->VpiDirection() != vpiInput) {
      direction_names_t::const_iterator it =
          kDirectionNames.find(object->VpiDirection());
      if (it != kDirectionNames.end()) {
        prefix.append(it->second).append(1, kOverwriteMarker);
      }
    }

    std::string text = prefix;
    text.append(formatName(object->VpiName()));

    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - prefix.length(), text);
  }

  void enterAlias_stmt(const UHDM::alias_stmt *const object) final {
    // Test file not available.
  }

  void enterClocking_block(const UHDM::clocking_block *const object) final {
    if (visited.find(object) != visited.end()) return;

    const UHDM::any *const parent = object->VpiParent();
    if ((parent == nullptr) || (parent->UhdmType() != UHDM::uhdmmodule_inst))
      return;

    constexpr std::string_view keyword1 = "unnamed_clocking_block";
    constexpr std::string_view keyword2 = "default";
    constexpr std::string_view keyword3 = "global";
    constexpr std::string_view keyword4 = "clocking";
    constexpr std::string_view keyword5 = "endclocking";
    constexpr std::string_view keyword6 = "input";
    constexpr std::string_view keyword7 = "output";

    const std::filesystem::path &filepath = object->VpiFile();
    const std::string name = formatName(object->VpiName());

    const UHDM::module_inst *const mdl =
        static_cast<const UHDM::module_inst *>(parent);
    std::string text;
    if (mdl->Global_clocking() == object) {
      text.append(keyword3).append(1, kOverwriteMarker);
    } else if (mdl->Default_clocking() == object) {
      text.append(keyword2).append(1, kOverwriteMarker);
    }
    text.append(keyword4);

    if (name != keyword1) {
      text.append(1, kOverwriteMarker).append(name);
    }

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiEndLineNo(),
           object->VpiEndColumnNo() - keyword5.length(), keyword5);

    const UHDM::delay_control *const inputSkew = object->Input_skew();
    const UHDM::delay_control *const outputSkew = object->Output_skew();
    if (inputSkew != nullptr) {
      insert(filepath, inputSkew->VpiLineNo(),
             inputSkew->VpiColumnNo() - keyword2.length() - 1 -
                 keyword6.length() - 1,
             keyword2);
      insert(filepath, inputSkew->VpiLineNo(),
             inputSkew->VpiColumnNo() - keyword6.length() - 1, keyword6);

      edge_names_t::const_iterator it =
          kEdgeNames.find(object->VpiOutputEdge());
      if (it != kEdgeNames.end()) {
        text.assign(keyword7).append(1, kOverwriteMarker).append(it->second);
        insert(filepath, inputSkew->VpiEndLineNo(),
               inputSkew->VpiEndColumnNo() + 1, text);
      }
    }

    if (outputSkew != nullptr) {
      if ((inputSkew == nullptr) ||
          (inputSkew->VpiLineNo() != outputSkew->VpiLineNo())) {
        insert(filepath, outputSkew->VpiLineNo(),
               outputSkew->VpiColumnNo() - keyword2.length() - 1 -
                   keyword6.length() - 1,
               keyword2);
      }

      insert(filepath, outputSkew->VpiLineNo(),
             outputSkew->VpiColumnNo() - keyword7.length() - 1, keyword7);
    }
  }

  void enterClocking_io_decl(const UHDM::clocking_io_decl *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));

    std::string text;
    direction_names_t::const_iterator it1 =
        kDirectionNames.find(object->VpiDirection());
    if (it1 != kDirectionNames.end()) {
      text.append(it1->second).append(1, kOverwriteMarker);
    }
    if ((object->VpiDirection() == vpiInput) &&
        (object->VpiInputEdge() != vpiNoEdge)) {
      edge_names_t::const_iterator it2 =
          kEdgeNames.find(object->VpiInputEdge());
      if (it2 != kEdgeNames.end()) {
        text.append(it2->second).append(1, kOverwriteMarker);
      }
    } else if ((object->VpiDirection() == vpiOutput) &&
               (object->VpiOutputEdge() != vpiNoEdge)) {
      edge_names_t::const_iterator it2 =
          kEdgeNames.find(object->VpiOutputEdge());
      if (it2 != kEdgeNames.end()) {
        text.append(it2->second).append(1, kOverwriteMarker);
      }
    }

    const UHDM::delay_control *const inputSkew = object->Input_skew();
    const UHDM::delay_control *const outputSkew = object->Output_skew();
    if (inputSkew != nullptr) {
      insert(filepath, inputSkew->VpiLineNo(),
             inputSkew->VpiColumnNo() - text.length(), text);
    } else if (outputSkew != nullptr) {
      insert(filepath, outputSkew->VpiLineNo(),
             outputSkew->VpiColumnNo() - text.length(), text);
    } else {
      insert(filepath, object->VpiLineNo(),
             object->VpiColumnNo() - text.length(), text);
    }

    const UHDM::any *const expr = object->Expr();
    if (expr != nullptr) {
      insert(filepath, expr->VpiLineNo(), expr->VpiColumnNo() - 1, "=");
    }
  }

  void enterParam_assign(const UHDM::param_assign *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    const UHDM::any *const lhs = object->Lhs();
    const UHDM::any *const rhs = object->Rhs();
    if ((lhs != nullptr) && (rhs != nullptr)) {
      insert(filepath, rhs->VpiLineNo(), rhs->VpiColumnNo() - 1, "=");
    }
  }

  void enterInterface_array(const UHDM::interface_array *const object) final {
    //@todo: Ideally it should have information related to type of interface.
    // Ex. MyInterface.MyModPort my_port2. It only has "my_port2" info not
    // MyInterface.MyModPort File: test\ModPortRange\dut.sv
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));
  }

  void enterProgram_array(const UHDM::program_array *const object) final {
    // Test file not available.
  }

  void enterModule_array(const UHDM::module_array *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));

    const UHDM::VectorOfrange *const ranges = object->Ranges();
    if ((ranges != nullptr) && !ranges->empty()) {
      const UHDM::range *const rangeN = ranges->back();
      insert(filepath, rangeN->VpiLineNo(), rangeN->VpiEndColumnNo(), "();");
    }
  }

  void enterModule_typespec(const UHDM::module_typespec *const object) final {
    enterTypespec(object);
  }

  void enterSwitch_array(const UHDM::switch_array *const object) final {
    // Test file not available.
  }

  void enterUdp_array(const UHDM::udp_array *const object) final {
    // Test file not available.
  }

  void enterPrim_term(const UHDM::prim_term *const object) final {
    // third_party\tests\SimpleParserTest\jkff_udp.v
    // No data available. Also taken care by entergate() and enterRef_obj().
  }

  void enterPath_term(const UHDM::path_term *const object) final {
    // Test file not available.
  }

  void enterTchk_term(const UHDM::tchk_term *const object) final {
    // Test file not available.
  }

  void enterNet_bit(const UHDM::net_bit *const object) final {
    // Test file not available.
  }

  void enterStruct_net(const UHDM::struct_net *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    std::string prefix;

    net_type_names_t::const_iterator it =
        kNetTypeNames.find(object->VpiNetType());
    if (it != kNetTypeNames.end()) {
      prefix.append(it->second).append(1, kOverwriteMarker);
    }

    if (const UHDM::ref_typespec *const rt = object->Typespec()) {
      if (const UHDM::typespec *const typespec = rt->Actual_typespec()) {
        prefix.append(getTypespecName(typespec)).append(1, kOverwriteMarker);
      }
    }

    std::string text = prefix;
    text.append(formatName(object->VpiName()));

    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - prefix.length(), text);
  }

  void enterEnum_net(const UHDM::enum_net *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();
    std::string prefix;

    net_type_names_t::const_iterator it =
        kNetTypeNames.find(object->VpiNetType());
    if (it != kNetTypeNames.end()) {
      prefix.append(it->second).append(1, kOverwriteMarker);
    }

    if (const UHDM::ref_typespec *const rt = object->Typespec()) {
      if (const UHDM::typespec *const typespec = rt->Actual_typespec()) {
        prefix.append(getTypespecName(typespec)).append(1, kOverwriteMarker);
      }
    }

    std::string text = prefix;
    text.append(formatName(object->VpiName()));

    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - prefix.length(), text);
  }

  void enterInteger_net(const UHDM::integer_net *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();
    std::string prefix;

    net_type_names_t::const_iterator it =
        kNetTypeNames.find(object->VpiNetType());
    if (it != kNetTypeNames.end()) {
      prefix.append(it->second).append(1, kOverwriteMarker);
    }

    if (const UHDM::ref_typespec *const rt = object->Typespec()) {
      if (const UHDM::typespec *const typespec = rt->Actual_typespec()) {
        prefix.append(getTypespecName(typespec)).append(1, kOverwriteMarker);
      }
    }

    std::string text = prefix;
    text.append(formatName(object->VpiName()));

    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - prefix.length(), text);
  }

  void enterTime_net(const UHDM::time_net *const object) final {
    // Test file not available.
  }

  void enterLogic_net(const UHDM::logic_net *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));

    const UHDM::VectorOfrange *const ranges = object->Ranges();
    if ((ranges != nullptr) && !ranges->empty()) {
      net_type_names_t::const_iterator it =
          kNetTypeNames.find(object->VpiNetType());
      if (it != kNetTypeNames.end()) {
        const UHDM::range *const range0 = ranges->at(0);
        insert(filepath, range0->VpiLineNo(),
               range0->VpiColumnNo() - it->second.length() - 2, it->second);
      }
    }
  }

  void enterArray_net(const UHDM::array_net *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));
  }

  void enterPacked_array_net(const UHDM::packed_array_net *const object) final {
  }

  void enterEvent_typespec(const UHDM::event_typespec *const object) final {
    enterTypespec(object);
  }

  void enterNamed_event(const UHDM::named_event *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "event";
    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.append(keyword)
        .append(1, kOverwriteMarker)
        .append(formatName(object->VpiName()))
        .append(";");
    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - keyword.length() - 1, text);
  }

  void enterNamed_event_array(
      const UHDM::named_event_array *const object) final {
    // Test file not available.
  }

  void enterParameter(const UHDM::parameter *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "localparam";
    constexpr std::string_view keyword2 = "parameter";

    const std::filesystem::path &filepath = object->VpiFile();

    int32_t line = object->VpiLineNo();
    int32_t column = object->VpiColumnNo();
    if (const UHDM::ref_typespec *const rt = object->Typespec()) {
      if (const UHDM::typespec *const typespec = rt->Actual_typespec()) {
        if ((typespec->UhdmType() == UHDM::uhdmenum_typespec) ||
            (typespec->UhdmType() == UHDM::uhdmstruct_typespec)) {
          const std::string name = getTypespecName(typespec);
          column = object->VpiColumnNo() - name.length() - 1;
          insert(filepath, line, column, name);
        } else if (typespec->VpiColumnNo() != 0) {
          // TODO(HS): This check needs to go!
          column = typespec->VpiColumnNo();
        }
      }
    }

    if (object->VpiLocalParam()) {
      insert(filepath, line, column - keyword1.length() - 1, keyword1);
    } else {
      insert(filepath, line, column - keyword2.length() - 1, keyword2);
    }

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));
  }

  void enterDef_param(const UHDM::def_param *const object) final {
    // Test file not available.
  }

  void enterSpec_param(const UHDM::spec_param *const object) final {
    // Test file not available.
  }

  void enterClass_typespec(const UHDM::class_typespec *const object) final {
    enterTypespec(object);
  }

  void enterExtends(const UHDM::extends *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "extends";
    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - keyword1.length() - 1, keyword1);

    if (const UHDM::ref_typespec *const rt = object->Class_typespec()) {
      if (const UHDM::class_typespec *const typespec =
              rt->Actual_typespec<UHDM::class_typespec>()) {
        enterTypespec(typespec);
      }
    }
  }

  void enterClass_defn(const UHDM::class_defn *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "class";
    constexpr std::string_view keyword2 = "endclass";

    const std::filesystem::path &filepath = object->VpiFile();
    const std::string name = formatName(object->VpiName());

    std::string text;
    text.append(keyword1)
        .append(1, kOverwriteMarker)
        .append(formatName(object->VpiName()));

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiEndLineNo(),
           object->VpiEndColumnNo() - keyword2.length(), keyword2);

    if (const UHDM::extends *const extends = object->Extends()) {
      enterExtends(extends);
    }
  }

  void enterClass_obj(const UHDM::class_obj *const object) final {
    // Test file not available.
  }

  void enterClass_var(const UHDM::class_var *const object) final {
    enterVariables_(object);
  }

  void enterInterface_inst(const UHDM::interface_inst *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    if (isInterfaceDefinition(object)) {
      constexpr std::string_view keyword1 = "interface";
      constexpr std::string_view keyword2 = "endinterface";

      std::string text;
      text.append(keyword1)
          .append(1, kOverwriteMarker)
          .append(formatName(object->VpiDefName()));

      insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
      insert(filepath, object->VpiEndLineNo(),
             object->VpiEndColumnNo() - keyword2.length(), keyword2);
    } else {
      insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
             formatName(object->VpiName()));
    }
  }

  void enterProgram(const UHDM::program *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "program";
    constexpr std::string_view keyword2 = "endprogram";

    const std::filesystem::path &filepath = object->VpiFile();
    const std::string name = formatName(object->VpiName());

    std::string text;
    if (name.empty()) {
      text.append(keyword1)
          .append(1, kOverwriteMarker)
          .append(formatName(object->VpiDefName()));

      insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
      insert(filepath, object->VpiEndLineNo(),
             object->VpiEndColumnNo() - keyword2.length(), keyword2);
    } else {
      text.append(formatName(object->VpiDefName()))
          .append(" #() ")
          .append(name)
          .append("(");

      insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
      insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo() - 1,
             ")");
    }
  }

  void enterPackage(const UHDM::package *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "package";
    constexpr std::string_view keyword2 = "endpackage";
    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.append(keyword1)
        .append(1, kOverwriteMarker)
        .append(formatName(object->VpiName()));

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiEndLineNo(),
           object->VpiEndColumnNo() - keyword2.length(), keyword2);
  }

  void enterModule_inst(const UHDM::module_inst *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    uint32_t end_column = 0;
    if (isModuleDefinition(object)) {
      constexpr std::string_view keyword1("module");
      constexpr std::string_view keyword2("endmodule");

      std::string text;
      text.append(keyword1)
          .append(1, kOverwriteMarker)
          .append(formatName(object->VpiDefName()));

      insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
      insert(filepath, object->VpiEndLineNo(),
             object->VpiEndColumnNo() - keyword2.length(), keyword2);
      end_column = object->VpiColumnNo() + text.length();

      insert(filepath, object->VpiLineNo(), end_column, "(");

      uint32_t end_line = object->VpiLineNo();
      const UHDM::VectorOfport *const ports = object->Ports();
      if ((ports != nullptr) && !ports->empty()) {
        for (int32_t i = 0, ni = ports->size(); i < ni; ++i) {
          const UHDM::port *const port = ports->at(i);

          const UHDM::VectorOfrange *ranges = nullptr;
          if (const UHDM::ref_typespec *const rt = port->Typespec()) {
            if (const UHDM::typespec *const typespec = rt->Actual_typespec()) {
              if (typespec->UhdmType() == UHDM::uhdmarray_typespec) {
                ranges = static_cast<const UHDM::array_typespec *>(typespec)
                             ->Ranges();
              } else if (typespec->UhdmType() ==
                         UHDM::uhdmpacked_array_typespec) {
                ranges =
                    static_cast<const UHDM::packed_array_typespec *>(typespec)
                        ->Ranges();
              }
            }
          }

          if ((ranges == nullptr) || ranges->empty()) {
            end_line = port->VpiEndLineNo();
            end_column = port->VpiEndColumnNo();
          } else {
            const UHDM::range *const rangeN = ranges->back();

            end_line = rangeN->VpiEndLineNo();
            end_column = rangeN->VpiEndColumnNo();
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
      text.append(formatName(object->VpiDefName()))
          .append(1, kOverwriteMarker)
          .append(formatName(object->VpiName()));

      insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
      end_column = object->VpiColumnNo() + text.length();

      insert(filepath, object->VpiLineNo(), end_column, "(");

      const UHDM::VectorOfport *const ports = object->Ports();
      if ((ports != nullptr) && !ports->empty()) {
        for (int32_t i = 0, ni = ports->size() - 1; i < ni; ++i) {
          const UHDM::port *const port = ports->at(i);
          if (const UHDM::any *const high_conn = port->High_conn()) {
            insert(filepath, high_conn->VpiEndLineNo(),
                   high_conn->VpiEndColumnNo() + 1, ",");
          }
        }
        const UHDM::port *const portN = ports->back();
        if (const UHDM::any *const high_connN = portN->High_conn()) {
          end_column = high_connN->VpiEndColumnNo() + 1;
        }
      }
      insert(filepath, object->VpiEndLineNo(), end_column + 1, ");");
    }

    const UHDM::VectorOfparam_assign *const param_assigns =
        object->Param_assigns();
    if ((param_assigns != nullptr) && !param_assigns->empty()) {
      UHDM::VectorOfparam_assign ordered(*param_assigns);
      std::stable_sort(ordered.begin(), ordered.end(),
                       [](UHDM::VectorOfparam_assign::const_reference lhs,
                          UHDM::VectorOfparam_assign::const_reference rhs) {
                         int32_t r = lhs->VpiLineNo() - rhs->VpiLineNo();
                         if (r != 0) return r < 0;

                         r = lhs->VpiColumnNo() - rhs->VpiColumnNo();
                         if (r != 0) return r < 0;

                         r = lhs->VpiEndLineNo() - rhs->VpiEndLineNo();
                         if (r != 0) return r < 0;

                         r = lhs->VpiEndColumnNo() - rhs->VpiEndColumnNo();
                         return r < 0;
                       });
      for (int32_t i = 0, j = 1, nj = ordered.size(); j < nj; ++i, ++j) {
        const UHDM::any *const ilhs = ordered[i]->Lhs();
        const UHDM::any *const jlhs = ordered[j]->Lhs();
        if ((ilhs->UhdmType() == UHDM::uhdmparameter) &&
            (jlhs->UhdmType() == UHDM::uhdmparameter)) {
          const UHDM::typespec *itypespec = nullptr;
          if (const UHDM::ref_typespec *const rt =
                  static_cast<const UHDM::parameter *>(ilhs)->Typespec()) {
            itypespec = rt->Actual_typespec();
          }

          const UHDM::typespec *jtypespec = nullptr;
          if (const UHDM::ref_typespec *const rt =
                  static_cast<const UHDM::parameter *>(jlhs)->Typespec()) {
            jtypespec = rt->Actual_typespec();
          }

          if ((itypespec != nullptr) && (jtypespec != nullptr) &&
              (itypespec->VpiLineNo() != 0) &&
              (itypespec->VpiColumnNo() != 0) &&
              (itypespec->VpiEndLineNo() != 0) &&
              (itypespec->VpiEndColumnNo() != 0) &&
              (itypespec->UhdmType() == jtypespec->UhdmType()) &&
              (itypespec->VpiLineNo() == jtypespec->VpiLineNo()) &&
              (itypespec->VpiColumnNo() == jtypespec->VpiColumnNo()) &&
              (itypespec->VpiEndLineNo() == jtypespec->VpiEndLineNo()) &&
              (itypespec->VpiEndColumnNo() == jtypespec->VpiEndColumnNo())) {
            UHDM::VectorOfparam_assign::const_reference iparam_assign =
                ordered[i];
            insert(filepath, iparam_assign->VpiEndLineNo(),
                   iparam_assign->VpiEndColumnNo(), ",");
          }
        }
      }
    }
  }

  void enterChecker_decl(const UHDM::checker_decl *const object) final {
    // Test file not available.
  }

  void enterChecker_inst(const UHDM::checker_inst *const object) final {
    // TODO(KS): In case of checker intance, other data is not available. Only
    // checker instance and instance name with start and end line and col is
    // available. tests\CheckerInst\dut.sv

    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.append(formatName(object->VpiDefName()))
        .append(1, kOverwriteMarker)
        .append(formatName(object->VpiName()))
        .append("(");

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);
    insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo(), ")");
  }

  void enterShort_real_typespec(
      const UHDM::short_real_typespec *const object) final {
    enterTypespec(object);
  }

  void enterReal_typespec(const UHDM::real_typespec *const object) final {
    enterTypespec(object);
  }

  void enterByte_typespec(const UHDM::byte_typespec *const object) final {
    enterTypespec(object);
  }

  void enterShort_int_typespec(
      const UHDM::short_int_typespec *const object) final {
    enterTypespec(object);
  }

  void enterInt_typespec(const UHDM::int_typespec *const object) final {
    enterTypespec(object);
  }

  void enterLong_int_typespec(
      const UHDM::long_int_typespec *const object) final {
    enterTypespec(object);
  }

  void enterInteger_typespec(const UHDM::integer_typespec *const object) final {
    enterTypespec(object);
  }

  void enterTime_typespec(const UHDM::time_typespec *const object) final {
    enterTypespec(object);
  }

  void enterString_typespec(const UHDM::string_typespec *const object) final {
    enterTypespec(object);
  }

  void enterChandle_typespec(const UHDM::chandle_typespec *const object) final {
    enterTypespec(object);
  }

  void enterLogic_typespec(const UHDM::logic_typespec *const object) final {
    if (visited.find(object) != visited.end()) return;

    const UHDM::any *const parent = object->VpiParent();
    if ((parent != nullptr) && (parent->UhdmType() != UHDM::uhdmparameter) &&
        (parent->UhdmType() != UHDM::uhdmparam_assign) &&
        (parent->UhdmType() != UHDM::uhdmtypespec_member)) {
      constexpr std::string_view keyword = "typedef";
      const std::filesystem::path &filepath = object->VpiFile();

      std::string prefix(keyword);
      prefix.append(1, kOverwriteMarker);

      std::string text(prefix);
      text.append("logic");
      insert(filepath, object->VpiLineNo(),
             object->VpiColumnNo() - prefix.length(), text);

      insert(filepath, object->VpiEndLineNo(), object->VpiEndColumnNo() + 1,
             formatName(object->VpiName()));
    } else if (object->VpiName().empty()) {
      enterTypespec(object);
    }
  }

  void enterPacked_array_typespec(
      const UHDM::packed_array_typespec *const object) final {
    enterTypespec(object);
  }

  void enterArray_typespec(const UHDM::array_typespec *const object) final {
    enterTypespec(object);
  }

  void enterVoid_typespec(const UHDM::void_typespec *const object) final {
    enterTypespec(object);
  }

  void enterSequence_typespec(
      const UHDM::sequence_typespec *const object) final {
    enterTypespec(object);
  }

  void enterProperty_typespec(
      const UHDM::property_typespec *const object) final {
    enterTypespec(object);
  }

  void enterInterface_typespec(
      const UHDM::interface_typespec *const object) final {
    enterTypespec(object);
  }

  void enterEnum_typespec(const UHDM::enum_typespec *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text("typedef enum ");

    if (const UHDM::ref_typespec *const rt = object->Base_typespec()) {
      if (const UHDM::typespec *const base_typespec = rt->Actual_typespec()) {
        text.append(getTypespecName(base_typespec)).append(1, kOverwriteMarker);
      }
    }

    text.append("{");
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);

    text.assign("} ").append(getTypespecName(object)).append(";");
    insert(filepath, object->VpiEndLineNo(),
           object->VpiEndColumnNo() - text.length(), text);

    const UHDM::VectorOfenum_const *const enum_consts = object->Enum_consts();
    if ((enum_consts != nullptr) && !enum_consts->empty()) {
      for (int32_t i = 0, ni = enum_consts->size() - 1; i < ni; ++i) {
        insert(filepath, enum_consts->at(i)->VpiEndLineNo(),
               enum_consts->at(i)->VpiEndColumnNo(), ",");
      }
    }
  }

  void enterStruct_typespec(const UHDM::struct_typespec *const object) final {
    if (visited.find(object) != visited.end()) return;

    // TODO: struct_typespec/endline is wrong!
    const UHDM::VectorOftypespec_member *const members = object->Members();
    if ((members != nullptr) && !members->empty()) {
      const UHDM::typespec_member *const last = members->back();

      constexpr std::string_view keyword1 = "typedef";
      constexpr std::string_view keyword2 = "struct";
      const std::filesystem::path &filepath = object->VpiFile();

      std::string prefix;
      //      if (callstack.empty() ||
      //          (callstack.back()->UhdmType() != UHDM::uhdmtypespec_member)) {
      prefix.append(keyword1).append(1, kOverwriteMarker);
      //      }

      std::string text = prefix;
      text.append(keyword2);
      if (object->VpiPacked()) {
        text.append(" packed");
      }
      text.append(" {");
      insert(filepath, object->VpiLineNo(),
             object->VpiColumnNo() - prefix.length(), text);

      text.assign("} ").append(formatName(object->VpiName()));
      insert(filepath, last->VpiLineNo() + 1, 1, text);
    }
  }

  void enterUnion_typespec(const UHDM::union_typespec *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    // TODO: union_typespec/endline is wrong!
    const UHDM::VectorOftypespec_member *const members = object->Members();
    if ((members != nullptr) && !members->empty()) {
      const UHDM::typespec_member *const last = members->back();

      constexpr std::string_view keyword = "typedef";

      std::string text;
      text.append(keyword).append(1, kOverwriteMarker).append("union");
      if (object->VpiPacked()) {
        text.append(" packed");
      }
      text.append(" {");
      insert(filepath, object->VpiLineNo(),
             object->VpiColumnNo() - keyword.length() - 1, text);

      text.assign("} ").append(formatName(object->VpiName()));
      insert(filepath, last->VpiLineNo() + 1, 1, text);
    }
  }

  void enterUnsupported_typespec(
      const UHDM::unsupported_typespec *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));
  }

  void enterType_parameter(const UHDM::type_parameter *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "parameter type";
    constexpr std::string_view keyword2 = "=logic";

    const std::filesystem::path &filepath = object->VpiFile();
    if (const UHDM::ref_typespec *const rt = object->Typespec()) {
      if (const UHDM::typespec *const typespec = rt->Actual_typespec()) {
        switch (typespec->UhdmType()) {
          case UHDM::uhdmlogic_typespec: {
            insert(filepath, typespec->VpiLineNo(), typespec->VpiColumnNo() - 1,
                   keyword2);
          } break;

          default:
            break;
        }
      }
    }
    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - keyword1.length() - 1, keyword1);
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));
  }

  void enterTypespec_member(const UHDM::typespec_member *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    if (const UHDM::ref_typespec *const rt = object->Typespec()) {
      if (const UHDM::typespec *typespec = rt->Actual_typespec()) {
        insert(filepath, object->VpiRefLineNo(), object->VpiRefColumnNo(),
               getTypespecName(typespec));
      }
    }
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));
  }

  void enterEnum_const(const UHDM::enum_const *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();
    const std::string name = formatName(object->VpiName());
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), name);

    if (static_cast<uint16_t>(object->VpiColumnNo() + name.length()) <
        object->VpiEndColumnNo()) {
      std::string text;
      text.append("=").append(object->VpiDecompile());
      insert(filepath, object->VpiLineNo(),
             object->VpiEndColumnNo() - text.length(), text);
    }
    visited.insert(object);
  }

  void enterBit_typespec(const UHDM::bit_typespec *const object) final {
    enterTypespec(object);
  }

  void enterUser_systf(const UHDM::user_systf *const object) final {
    // Test file not available.
  }

  void enterSys_func_call(const UHDM::sys_func_call *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    const std::string text = formatName(object->VpiName());

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(), text);

    const UHDM::VectorOfany *const call_args = object->Tf_call_args();
    if ((call_args != nullptr) && !call_args->empty()) {
      UHDM::VectorOfany::const_reference call_arg0 = call_args->front();
      UHDM::VectorOfany::const_reference call_argN = call_args->back();

      insert(filepath, call_arg0->VpiLineNo(), call_arg0->VpiColumnNo() - 1,
             "(");
      insert(filepath, call_argN->VpiEndLineNo(), call_argN->VpiEndColumnNo(),
             ")");

      for (int32_t i = 0, n = call_args->size() - 1; i < n; ++i) {
        UHDM::VectorOfany::const_reference call_arg = call_args->at(i);
        insert(filepath, call_arg->VpiEndLineNo(), call_arg->VpiEndColumnNo(),
               ",");
      }
    }
  }

  void enterSys_task_call(const UHDM::sys_task_call *const object) final {
    // Test file not available.
  }

  void enterMethod_func_call(const UHDM::method_func_call *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    if (object->Prefix() != nullptr) {
      insert(filepath, object->VpiLineNo(), object->VpiColumnNo() - 1, ".");
    }
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));
    insert(filepath, object->VpiLineNo(), object->VpiEndColumnNo(), "(");

    uint32_t closing_bracket_line = object->VpiLineNo();
    uint32_t closing_bracket_column = object->VpiEndColumnNo() + 1;
    const UHDM::VectorOfany *const call_args = object->Tf_call_args();
    if ((call_args != nullptr) && !call_args->empty()) {
      for (size_t i = 0, n = call_args->size() - 1; i < n; ++i) {
        const UHDM::any *const arg = call_args->at(i);
        if ((arg->VpiLineNo() > 0) && (arg->VpiColumnNo() > 0) &&
            (arg->VpiEndLineNo() > 0) && (arg->VpiEndColumnNo() > 0)) {
          insert(filepath, arg->VpiEndLineNo(), arg->VpiEndColumnNo(), ",");
        }
      }
      closing_bracket_line = call_args->back()->VpiLineNo();
      closing_bracket_column = call_args->back()->VpiEndColumnNo();
    }
    insert(filepath, closing_bracket_line, closing_bracket_column, ")");
  }

  void enterMethod_task_call(const UHDM::method_task_call *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();

    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));

    const UHDM::VectorOfany *const args = object->Tf_call_args();
    if ((args != nullptr) && !args->empty()) {
      const UHDM::any *const arg0 = args->front();
      insert(filepath, arg0->VpiLineNo(), arg0->VpiColumnNo() - 1, "(");
      for (int32_t i = 0, ni = args->size() - 1; i < ni; ++i) {
        const UHDM::any *const arg = args->at(i);
        insert(filepath, arg->VpiEndLineNo(), arg->VpiEndColumnNo(), ",");
      }
      const UHDM::any *const argN = args->back();
      insert(filepath, argN->VpiEndLineNo(), argN->VpiEndColumnNo(), ")");
    } else {
      insert(filepath, object->VpiLineNo(), object->VpiEndColumnNo(), "()");
    }
  }

  void enterFunc_call(const UHDM::func_call *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));

    const UHDM::VectorOfany *const args = object->Tf_call_args();
    if ((args != nullptr) && !args->empty()) {
      const UHDM::any *const arg0 = args->front();
      insert(filepath, arg0->VpiLineNo(), arg0->VpiColumnNo() - 1, "(");
      for (int32_t i = 0, ni = args->size() - 1; i < ni; ++i) {
        const UHDM::any *const arg = args->at(i);
        insert(filepath, arg->VpiEndLineNo(), arg->VpiEndColumnNo(), ",");
      }
      const UHDM::any *const argN = args->back();
      insert(filepath, argN->VpiEndLineNo(), argN->VpiEndColumnNo(), ")");
    } else {
      insert(filepath, object->VpiLineNo(), object->VpiEndColumnNo(), "()");
    }
  }

  void enterTask_call(const UHDM::task_call *const object) final {
    if (visited.find(object) != visited.end()) return;

    const std::filesystem::path &filepath = object->VpiFile();
    insert(filepath, object->VpiLineNo(), object->VpiColumnNo(),
           formatName(object->VpiName()));

    const UHDM::VectorOfany *const args = object->Tf_call_args();
    if ((args != nullptr) && !args->empty()) {
      const UHDM::any *const arg0 = args->front();
      insert(filepath, arg0->VpiLineNo(), arg0->VpiColumnNo() - 1, "(");
      for (int32_t i = 0, ni = args->size() - 1; i < ni; ++i) {
        const UHDM::any *const arg = args->at(i);
        insert(filepath, arg->VpiEndLineNo(), arg->VpiEndColumnNo(), ",");
      }
      const UHDM::any *const argN = args->back();
      insert(filepath, argN->VpiEndLineNo(), argN->VpiEndColumnNo(), ")");
    } else {
      insert(filepath, object->VpiLineNo(), object->VpiEndColumnNo(), "()");
    }
  }

  void enterConstraint_ordering(
      const UHDM::constraint_ordering *const object) final {
    // Test file not available.
  }

  void enterConstraint(const UHDM::constraint *const object) final {
    // tests\SimpleClass
  }

  void enterImport_typespec(const UHDM::import_typespec *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword1 = "import";
    constexpr std::string_view keyword2 = "STRING:";

    const std::filesystem::path &filepath = object->VpiFile();
    const UHDM::constant *const constant = object->Item();

    std::string value(constant->VpiValue());
    size_t pos = value.find(keyword2);
    if (pos == 0) {
      value = value.substr(keyword2.length());
    }

    std::string text;
    text.append(keyword1)
        .append(1, kOverwriteMarker)
        .append(object->VpiName())
        .append("::")
        .append(value)
        .append(";");

    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - keyword1.length() - 1, text);
  }

  void enterDist_item(const UHDM::dist_item *const object) final {
    // Test file not available.
  }

  void enterDistribution(const UHDM::distribution *const object) final {
    // Test file not available.
  }

  void enterImplication(const UHDM::implication *const object) final {
    // Test file not available.
  }

  void enterConstr_if(const UHDM::constr_if *const object) final {
    // Test file not available.
  }

  void enterConstr_if_else(const UHDM::constr_if_else *const object) final {
    // Test file not available.
  }

  void enterConstr_foreach(const UHDM::constr_foreach *const object) final {
    // Test file not available.
  }

  void enterSoft_disable(const UHDM::soft_disable *const object) final {
    // Test file not available.
  }

  void enterInclude_file_info(
      const UHDM::include_file_info *const object) final {
    if (visited.find(object) != visited.end()) return;

    constexpr std::string_view keyword = "`include";

    const std::filesystem::path &filepath = object->VpiFile();

    std::string text;
    text.assign(keyword).append(" \"");
    text.append(object->VpiIncludedFile()).append("\"");

    insert(filepath, object->VpiLineNo(),
           object->VpiColumnNo() - keyword.length() - 1, text);
  }

  void enterDesign(const UHDM::design *const object) final {}

  void enterAllPackages(const UHDM::any *const object,
                        const UHDM::VectorOfpackage &objects) final {
    for (UHDM::VectorOfpackage::const_reference package : objects) {
      package->VpiTop(false);
    }
  }

  void enterTopPackages(const UHDM::any *const object,
                        const UHDM::VectorOfpackage &objects) final {
    for (UHDM::VectorOfpackage::const_reference package : objects) {
      package->VpiTop(true);
      visited.insert(package);
    }
  }

  void enterAllClasses(const UHDM::any *const object,
                       const UHDM::VectorOfclass_defn &objects) final {}

  void enterAllInterfaces(const UHDM::any *const object,
                          const UHDM::VectorOfinterface_inst &objects) final {}

  void enterAllUdps(const UHDM::any *const object,
                    const UHDM::VectorOfudp_defn &objects) final {}

  void enterAllPrograms(const UHDM::any *const object,
                        const UHDM::VectorOfprogram &objects) final {}

  void enterAllModules(const UHDM::any *const object,
                       const UHDM::VectorOfmodule_inst &objects) final {
    for (UHDM::VectorOfmodule_inst::const_reference module : objects) {
      module->VpiTop(false);
    }
  }

  void enterTypespecs(const UHDM::any *const object,
                      const UHDM::VectorOftypespec &objects) final {}

  void enterLet_decls(const UHDM::any *const object,
                      const UHDM::VectorOflet_decl &objects) final {}

  void enterTask_funcs(const UHDM::any *const object,
                       const UHDM::VectorOftask_func &objects) final {}

  void enterParameters(const UHDM::any *const object,
                       const UHDM::VectorOfany &objects) final {}

  void enterParam_assigns(const UHDM::any *const object,
                          const UHDM::VectorOfparam_assign &objects) final {}

  void enterTopModules(const UHDM::any *const object,
                       const UHDM::VectorOfmodule_inst &objects) final {
    for (UHDM::VectorOfmodule_inst::const_reference module : objects) {
      module->VpiTop(true);
      visited.insert(module);
    }
  }

  void enterTable_entrys(const UHDM::any *const object,
                         const UHDM::VectorOftable_entry &objects) final {
    const std::filesystem::path &filepath = object->VpiFile();

    const UHDM::table_entry *const entry0 = objects.front();
    insert(filepath, entry0->VpiLineNo() - 1, entry0->VpiColumnNo(), "table");

    const UHDM::table_entry *const entryN = objects.back();
    insert(filepath, entryN->VpiEndLineNo() + 1, entry0->VpiColumnNo(),
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
    const UHDM::design *const design =
        (const UHDM::design *)((const uhdm_handle *)handle)->object;
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

  SURELOG::FileSystem::setInstance(
      new SURELOG::PlatformFileSystem(std::filesystem::current_path()));

  // Read command line, compile a design, use -parse argument
  uint32_t code = 0;
  SURELOG::FileSystem *const fileSystem = SURELOG::FileSystem::getInstance();
  SURELOG::SymbolTable *const symbolTable = new SURELOG::SymbolTable();
  SURELOG::ErrorContainer *const errors =
      new SURELOG::ErrorContainer(symbolTable);
  SURELOG::CommandLineParser *const clp =
      new SURELOG::CommandLineParser(errors, symbolTable, false, false);
  bool success = clp->parseCommandLine(argc, argv);
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
    compiler = SURELOG::start_compiler(clp);
    vpi_design = SURELOG::get_uhdm_design(compiler);
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
  delete clp;
  delete symbolTable;
  delete errors;

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
