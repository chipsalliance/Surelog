#!/bin/bash

set -e

cd github/$KOKORO_DIR/

source ./.github/kokoro/steps/hostsetup.sh
source ./.github/kokoro/steps/hostinfo.sh
source ./.github/kokoro/steps/git.sh

echo
echo "==========================================="
echo "Building Surelog"
echo "-------------------------------------------"
(
	make -j10 release
)
echo "-------------------------------------------"

echo
echo "==========================================="
echo "Installing Surelog"
echo "-------------------------------------------"
(
	sudo make install
)
echo "-------------------------------------------"

echo
echo "==========================================="
echo "Executing Surelog tests"
echo "-------------------------------------------"
(
	make test_install
	make test-parallel
)
echo "-------------------------------------------"
