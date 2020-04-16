#!/bin/bash

set -e

# Check the SCRIPT_XXX values are set.
if [ -z "${SCRIPT_SRC}" ]; then
	echo 'Parent script must do SCRIPT_SRC="$(realpath ${BASH_SOURCE[0]})"'
	exit 1
fi
if [ -z "${SCRIPT_DIR}" ]; then
	echo 'Parent script must do SCRIPT_DIR="$(dirname "${SCRIPT_SRC}")"'
	exit 1
fi

# Check the KOKORO environment variables are correct
if [ -z "$KOKORO_DIR" ]; then
	echo "$$KOKORO_DIR environment variable is missing ('$KOKORO_DIR')!"
	exit 1
fi

# Close STDERR FD
exec 2<&-
# Redirect STDERR to STDOUT
exec 2>&1

# Get us into the github checkout source directory.
cd github/$KOKORO_DIR/

# Run the common setup steps
source ./.github/kokoro/steps/hostsetup.sh
source ./.github/kokoro/steps/hostinfo.sh
source ./.github/kokoro/steps/git.sh
