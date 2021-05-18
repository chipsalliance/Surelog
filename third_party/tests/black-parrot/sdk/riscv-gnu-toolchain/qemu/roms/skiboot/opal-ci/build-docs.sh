#!/bin/bash

set -uo pipefail
set -e
set -vx

cd doc;
make html latexpdf text
