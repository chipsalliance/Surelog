#!/bin/bash
# Copyright 2021 Alain Dargelas
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

FORMAT_OUT=${TMPDIR:-/tmp}/clang-format-diff.out

# Run on all files except the ones that are generated.
# TODO: have generator scripts run clang-format on their
#   output as well as last step, then we can exclude less
#   files here.
find src -name "*.h" -o -name "*.cpp"  \
    | grep -v "src/parser/" \
    | grep -v "src/API/slapi_scripts.h" \
    | grep -v "src/API/SV3_1aPythonListener.h" \
    | grep -v "src/SourceCompile/VObjectTypes\." \
    | grep -v "src/API/vobjecttypes_py.h" \
    | grep -v "src/SourceCompile/SV3_1aTreeShapeListener.h" \
    | grep -v "src/SourceCompile/SV3_1aPpTreeShapeListener.h" \
    | grep -v "src/API/vpi_user.h" \
    | xargs clang-format --style=Google -i

# Check if we got any diff, then print it out in in the CI.
# TODO: make these suggested diffs in the pull request.
git diff > ${FORMAT_OUT}

if [ -s ${FORMAT_OUT} ]; then
    echo "== There were changes running the formatter =="
    cat ${FORMAT_OUT}
    echo "To locally fix, run .github/bin/run-clang-format.sh then commit and push."
   exit 1
fi

exit 0
