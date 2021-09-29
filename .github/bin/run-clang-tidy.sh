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

TIDY_OUT=${TMPDIR:-/tmp}/clang-tidy-surelog.out

CLANG_TIDY=clang-tidy-12

hash ${CLANG_TIDY} || exit 2  # make sure it is installed.

if [ ! -r compile_commands.json ]; then
    echo "To get compile_commands.json, run in root of project and "
    echo "  make run-cmake-release"
    exit 1
fi

find src/ -name "*.cpp" -or -name "*.h" \
  | xargs -P$(nproc) -n 5 -- \
          ${CLANG_TIDY} --quiet 2>/dev/null \
  > ${TIDY_OUT}


cat ${TIDY_OUT}

sed 's|\(.*\)\(\[[a-z-]*\]$\)|\2|p;d' < ${TIDY_OUT} | sort | uniq -c | sort -n

if [ -s ${TIDY_OUT} ]; then
    echo "There were clang-tidy warnings. Please fix"
    echo "For now, this is not an error yet"
    # For now, we don't fail-exit as there is a lot of fixing needed, so
    # we just have the messages above as FYI.
    exit 0
    #exit 1
fi

echo "No clang-tidy complaints.😎"
exit 0
