#!/bin/bash
# Surelog Bash invocation script
SCRIPTPATH="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
export LD_LIBRARY_PATH=${SCRIPTPATH}/lib:$LD_LIBRARY_PATH
${SCRIPTPATH}/bin/surelog.exe "$@"

