#!/bin/bash

# Takes /dev/stdin as dtb, saves to file, does dtdiff
# Also runs parameter through a dts->dtb->dts conversion
# in order to work around dtc bugs.

T=$(mktemp)
cp /dev/stdin $T.dtb
dtc -I dts -O dtb $1 > $T.orig.dtb
dtdiff $T.orig.dtb $T.dtb
R=$?
if [ $R == 0 ]; then rm -f $T.dtb; fi
exit $R
