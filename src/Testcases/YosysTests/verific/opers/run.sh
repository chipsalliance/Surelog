#!/bin/bash

set -x
trap "echo FAIL > $1.status" ERR

yosys -p "
	verific -sv $1.sv
	verific -import -v top
	synth -flatten -top top
	design -stash A

	verific -sv $1.sv
	verific -import -gates -flatten top
	synth -flatten -top top
	design -stash B

	design -copy-from A -as A top
	design -copy-from B -as B top
	miter -equiv -flatten A B miter
	sat -verify -prove trigger 0 miter
"
if [ $? != 0 ] ; then
    echo FAIL > ${1}_${2}.status
    touch .stamp
    exit 0
fi

echo PASS > $1.status

