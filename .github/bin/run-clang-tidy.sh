#!/bin/bash
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

CLANG_TIDY=clang-tidy-12

hash ${CLANG_TIDY} || exit 2  # make sure it is installed.

if [ "$1" == "limited" ]; then
    # For now, since there are a lot things to fix, don't enable everything
    # that is mentioned in .clang-tidy, but add rules as we fix them.
    cat > ${LOCAL_TMP}/clang-tidy <<EOF
Checks: >
    -*,
    bugprone-copy-constructor-init,
    bugprone-macro-parentheses,
    bugprone-redundant-branch-condition,
    bugprone-string-integer-assignment,
    bugprone-suspicious-missing-comma,
    bugprone-suspicious-string-compare,
    bugprone-too-small-loop-variable,
    clang-analyzer-security.insecureAPI.strcpy,
    clang-diagnostic-ignored-qualifiers,
    clang-diagnostic-inconsistent-missing-override,
    clang-diagnostic-overloaded-virtual
    clang-diagnostic-unused-private-field,
    google-default-arguments,
    google-explicit-constructor,
    modernize-loop-convert,
    modernize-use-override,
    performance-faster-string-find,
    performance-for-range-copy,
    performance-inefficient-vector-operation,
    performance-unnecessary-copy-initialization,
    performance-unnecessary-value-param,
    readability-const-return-type,
    readability-container-size-empty,
    readability-delete-null-pointer,
    readability-non-const-parameter,
    readability-redundant-member-init,
    readability-redundant-string-cstr,
    readability-redundant-string-init,
    readability-static-accessed-through-instance,
    readability-static-definition-in-anonymous-namespace,
    readability-string-compare,
    readability-use-anyofallof,
EOF
    CLANG_TIDY_OPTS="--config-file=${LOCAL_TMP}/clang-tidy"
fi

CLANG_TIDY_OPTS="${CLANG_TIDY_OPTS} --quiet"

if [ ! -r compile_commands.json ]; then
    echo "To get compile_commands.json, run in root of project and "
    echo "  make run-cmake-release"
    exit 1
fi

find src/ -name "*.cpp" -or -name "*.h" \
    | grep -v Python | grep -v Constraint.h \
    | xargs -P$(nproc) -n 5 -- ${CLANG_TIDY} ${CLANG_TIDY_OPTS} 2>/dev/null \
            > ${TIDY_OUT}

cat ${TIDY_OUT}

sed 's|\(.*\)\(\[[a-zA-Z.-]*\]$\)|\2|p;d' < ${TIDY_OUT} | sort | uniq -c | sort -n

if [ -s ${TIDY_OUT} ]; then
    echo "There were clang-tidy warnings. Please fix."
    exit 1
fi

echo "No clang-tidy complaints.😎"
exit 0
