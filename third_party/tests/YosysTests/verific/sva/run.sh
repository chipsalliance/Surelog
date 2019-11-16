#!/bin/bash

set -x
test -f $1.sv
trap "echo FAIL > $1.status" ERR

while read t; do
	{
		echo "[options]"
		echo "mode bmc"
		echo "depth 32"
		echo "expect $(echo $t | cut -f1 -d_)"
		echo ""
		echo "[engines]"
		echo "smtbmc yices"
		echo ""
		echo "[script]"
		echo "verific -sv $1.sv"
		echo "verific -import $t"
		echo "prep -nordff -top $t"
		echo ""
		echo "[files]"
		echo "$1.sv"
	} > $1.$t.sby
	sby -f $1.$t.sby
	if [ $? != 0 ] ; then
    	echo FAIL > ${1}_${2}.status
    	touch .stamp
    	exit 0
	fi
done < <( egrep '^module (pass|fail)_[0-9][0-9]' $1.sv | gawk '{ print $2; }'; )

echo PASS > $1.status
