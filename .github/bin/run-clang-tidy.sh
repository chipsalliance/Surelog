#!/usr/bin/env bash
# Copyright 2021 The Surelog Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

LOCAL_TMP=${TMPDIR:-/tmp}

TIDY_OUT=${LOCAL_TMP}/clang-tidy-surelog.out

if [ "$1" == "limited" ]; then
    export CLANG_TIDY_CONFIG="${LOCAL_TMP}/clang-tidy"
    # For now, since there are a lot things to fix, don't enable everything
    # that is mentioned in .clang-tidy, but add rules as we fix them.
    # The more strict .clang-tidy rules will still show up as reminders in the
    # IDE, so are hopefully fixed on the way.
    cat > "${CLANG_TIDY_CONFIG}" <<EOF
Checks: >
    -*,
    bugprone-copy-constructor-init,
    bugprone-macro-parentheses,
    bugprone-redundant-branch-condition,
    bugprone-string-integer-assignment,
    bugprone-suspicious-include,
    bugprone-suspicious-missing-comma,
    bugprone-suspicious-string-compare,
    bugprone-too-small-loop-variable,
    clang-analyzer-security.insecureAPI.strcpy,
    clang-diagnostic-ignored-qualifiers,
    clang-diagnostic-inconsistent-missing-override,
    clang-diagnostic-overloaded-virtual
    clang-diagnostic-unused-private-field,
    google-build-using-namespace,
    google-explicit-constructor,
    modernize-concat-nested-namespaces,
    modernize-loop-convert,
    modernize-make-unique,
    modernize-raw-string-literal,
    modernize-redundant-void-arg,
    modernize-use-bool-literals,
    modernize-use-equals-default,
    modernize-use-equals-delete,
    modernize-use-nullptr,
    modernize-use-override,
    modernize-use-using,
    performance-faster-string-find,
    performance-for-range-copy,
    performance-inefficient-string-concatenation,
    performance-inefficient-vector-operation,
    performance-unnecessary-copy-initialization,
    performance-unnecessary-value-param,
    readability-avoid-const-params-in-decls,
    readability-const-return-type,
    readability-container-size-empty,
    readability-delete-null-pointer,
    readability-non-const-parameter,
    readability-redundant-casting,
    readability-redundant-member-init,
    readability-redundant-smartptr-get,
    readability-redundant-string-cstr,
    readability-redundant-string-init,
    readability-static-accessed-through-instance,
    readability-static-definition-in-anonymous-namespace,
    readability-string-compare,
    readability-use-anyofallof,

CheckOptions:
    - key: performance-unnecessary-value-param.AllowedTypes
      value: ::SURELOG::SymbolId;SURELOG::SymbolId;SymbolId;::SURELOG::NodeId;SURELOG::NodeId;NodeId;::SURELOG::PathId;SURELOG::PathId;PathId
    - key: performance-for-range-copy.AllowedTypes
      value: ::SURELOG::SymbolId;SURELOG::SymbolId;SymbolId;::SURELOG::NodeId;SURELOG::NodeId;NodeId;::SURELOG::PathId;SURELOG::PathId;PathId
    - key: performance-unnecessary-copy-initialization.AllowedTypes
      value: ::SURELOG::SymbolId;SURELOG::SymbolId;SymbolId;::SURELOG::NodeId;SURELOG::NodeId;NodeId;::SURELOG::PathId;SURELOG::PathId;PathId
EOF
fi

if [ ! -r compile_commands.json ]; then
    echo "To get compile_commands.json, run in root of project and "
    echo "  make run-cmake-release"
    exit 1
fi

# Invoke run-clang-tidy-cached, possibly with the 'limited' clang-tidy config.
sh $(dirname $0)/run-clang-tidy-cached.cc
