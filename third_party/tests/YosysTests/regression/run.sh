#!/bin/bash

set -x
test -d $1
test -f scripts/$2.ys

rm -rf $1/work_$2
mkdir $1/work_$2
cd $1/work_$2

touch .start

# cases where 'syntax error' or other errors are expected
if [ "$1" = "issue_00089" ] ||\
   [ "$1" = "issue_00093" ] ||\
   [ "$1" = "issue_00095" ] ||\
   [ "$1" = "issue_00096" ] ||\
   [ "$1" = "issue_00196" ] ||\
   [ "$1" = "issue_00362" ] ||\
   [ "$1" = "issue_00582" ] ||\
   [ "$1" = "issue_00594" ] ||\
   [ "$1" = "issue_00603" ] ||\
   [ "$1" = "issue_00635" ] ||\
   [ "$1" = "issue_00639" ] ||\
   [ "$1" = "issue_00763" ] ||\
   [ "$1" = "issue_00814" ] ||\
   [ "$1" = "issue_01063" ] ||\
   [ "$1" = "issue_01093" ] ||\
   [ "$1" = "issue_01131" ] ||\
   [ "$1" = "issue_01144" ]; then

	expected_string="syntax error"
    #Change checked string for check other errors
	if [ "$1" = "issue_00196" ]; then
		expected_string="Found posedge/negedge event"
	elif [ "$1" = "issue_00362" ]; then
		expected_string="is connected to constants:"
	elif [ "$1" = "issue_00582" ]; then
		expected_string="Failed to detect width for identifier"
	elif [ "$1" = "issue_00594" ]; then
		expected_string="Single range expected"
	elif [ "$1" = "issue_00639" ]; then
		expected_string="ERROR: Found 3 unproven \$equiv cells in 'equiv_status -assert'."
	elif [ "$1" = "issue_00763" ]; then
		expected_string="Invalid nesting"
	elif [ "$1" = "issue_00814" ]; then
		expected_string="is implicitly declared"
	elif [ "$1" = "issue_01063" ]; then
		expected_string="Gate cell u_mid8 not found in module top."
	elif [ "$1" = "issue_01093" ]; then
		expected_string="ERROR: Design has no top module, use the 'hierarchy' command to specify one."
	elif [ "$1" = "issue_01131" ]; then
		expected_string="ERROR: Value conversion failed"
	fi

	if yosys -ql yosys.log ../../scripts/$2.ys; then
		echo FAIL > ${1}_${2}.status
	else
		if grep "$expected_string" yosys.log; then
			echo PASS > ${1}_${2}.status
		else
			echo FAIL > ${1}_${2}.status
		fi
	fi

# cases without any additional checks (only checks in .ys script)
elif [ "$1" = "issue_00502" ] ||\
     [ "$1" = "issue_00524" ] ||\
     [ "$1" = "issue_00527" ] ||\
     [ "$1" = "issue_00642" ] ||\
     [ "$1" = "issue_00644" ] ||\
     [ "$1" = "issue_00655" ] ||\
     [ "$1" = "issue_00675" ] ||\
     [ "$1" = "issue_00685" ] ||\
	 [ "$1" = "issue_00689" ] ||\
	 [ "$1" = "issue_00699" ] ||\
	 [ "$1" = "issue_00708" ] ||\
	 [ "$1" = "issue_00774" ] ||\
	 [ "$1" = "issue_00781" ] ||\
	 [ "$1" = "issue_00785" ] ||\
	 [ "$1" = "issue_00810" ] ||\
	 [ "$1" = "issue_00823" ] ||\
	 [ "$1" = "issue_00826" ] ||\
	 [ "$1" = "issue_00831" ] ||\
	 [ "$1" = "issue_00835" ] ||\
	 [ "$1" = "issue_00857" ] ||\
	 [ "$1" = "issue_00862" ] ||\
	 [ "$1" = "issue_00865" ] ||\
	 [ "$1" = "issue_00867" ] ||\
	 [ "$1" = "issue_00870" ] ||\
	 [ "$1" = "issue_00873" ] ||\
	 [ "$1" = "issue_00888" ] ||\
	 [ "$1" = "issue_00922" ] ||\
	 [ "$1" = "issue_00931" ] ||\
	 [ "$1" = "issue_00935" ] ||\
	 [ "$1" = "issue_00938" ] ||\
	 [ "$1" = "issue_00940" ] ||\
	 [ "$1" = "issue_00948" ] ||\
	 [ "$1" = "issue_00961" ] ||\
	 [ "$1" = "issue_00981" ] ||\
	 [ "$1" = "issue_00987" ] ||\
	 [ "$1" = "issue_00993" ] ||\
	 [ "$1" = "issue_01016" ] ||\
	 [ "$1" = "issue_01033" ] ||\
	 [ "$1" = "issue_01034" ] ||\
	 [ "$1" = "issue_01047" ] ||\
	 [ "$1" = "issue_01070" ] ||\
	 [ "$1" = "issue_01091" ] ||\
	 [ "$1" = "issue_01128" ] ||\
	 [ "$1" = "issue_01132" ] ||\
	 [ "$1" = "issue_01135" ] ||\
	 [ "$1" = "issue_01145" ] ||\
	 [ "$1" = "issue_01220" ] ||\
	 [ "$1" = "issue_01223" ] ||\
	 [ "$1" = "issue_01231" ] ||\
	 [ "$1" = "issue_01273" ] ||\
	 [ "$1" = "issue_01329" ] ||\
     [ "$1" = "issue_01364" ] ||\
	 [ "$1" = "issue_01372" ] ||\
	 [ "$1" = "issue_00623" ] ||\
	 [ "$1" = "issue_00656" ] ||\
	 [ "$1" = "issue_01014" ] ||\
	 [ "$1" = "issue_01023" ] ||\
	 [ "$1" = "issue_01084" ] ||\
	 [ "$1" = "issue_01193" ] ||\
	 [ "$1" = "issue_01206" ] ||\
	 [ "$1" = "issue_01216" ] ||\
	 [ "$1" = "issue_01225" ] ||\
	 [ "$1" = "issue_01259" ] ||\
	 [ "$1" = "issue_01360" ]; then

	yosys -ql yosys.log ../../scripts/$2.ys;

	if [ $? != 0 ] ; then
    	echo FAIL > ${1}_${2}.status
    	touch .stamp
    	exit 0
	else
		echo PASS > ${1}_${2}.status
	fi

# cases where some object names are/aren't expected in output file (tee -o result.log in the test script)
elif [ "$1" = "issue_00737" ] ||\
	 [ "$1" = "issue_00954" ] ||\
	 [ "$1" = "issue_00955" ] ||\
	 [ "$1" = "issue_00956" ] ||\
	 [ "$1" = "issue_00968" ] ||\
	 [ "$1" = "issue_00982" ] ||\
	 [ "$1" = "issue_00997" ] ||\
	 [ "$1" = "issue_01002" ] ||\
	 [ "$1" = "issue_01022" ] ||\
	 [ "$1" = "issue_01040" ] ||\
	 [ "$1" = "issue_01065" ] ||\
	 [ "$1" = "issue_01115" ] ||\
	 [ "$1" = "issue_01118" ] ||\
	 [ "$1" = "issue_01243" ] ||\
	 [ "$1" = "issue_00329" ] ||\
	 [ "$1" = "issue_01126" ] ||\
	 [ "$1" = "issue_01161" ] ||\
	 [ "$1" = "issue_01217" ] ||\
	 [ "$1" = "issue_01291" ]; then

	expected_string=""
	expected="1"
	if [ "$1" = "issue_00737" ]; then
		expected_string="ATTR \\\A:"
	elif [ "$1" = "issue_00954" ]; then
		expected_string="out = 4'1000"
	elif [ "$1" = "issue_00955" ]; then
		expected_string="out = 8'00001000"
	elif [ "$1" = "issue_00956" ]; then
		expected_string="Wire inivalue.r_val has an unprocessed 'init' attribute"
		expected="0"
	elif [ "$1" = "issue_00968" ]; then
		expected_string="assign o_value = { 4'hx, i_value }"
	elif [ "$1" = "issue_00982" ]; then
		expected_string="INIT 1'0"
	elif [ "$1" = "issue_00997" ]; then
		expected_string="h0"
	elif [ "$1" = "issue_01002" ]; then
		expected_string="Estimated number of LCs:         87"
	elif [ "$1" = "issue_01022" ]; then
		expected_string="connect \\\b 32'11111111111111111111111111111111"
	elif [ "$1" = "issue_01040" ]; then
		expected_string=".subckt dut_sub a\[2\]=a\[2\] a\[3\]=a\[3\] a\[4\]=a\[4\] a\[5\]=a\[5\] a\[6\]=a\[6\]"
	elif [ "$1" = "issue_01065" ]; then
		expected_string="Driver-driver conflict for"
		expected="0"
	elif [ "$1" = "issue_01115" ]; then
		expected_string="connect \\\o 33'xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
	elif [ "$1" = "issue_01118" ]; then
		expected_string="connect \\\o \[0\] 1'0"
	elif [ "$1" = "issue_01126" ]; then
		expected_string="assign d = c\\[5:0\\]"
	elif [ "$1" = "issue_01243" ]; then
		expected_string="assign y = reg_assign;"
	elif [ "$1" = "issue_00329" ]; then
		expected_string="wire \\[-1"
		expected="0"
	elif [ "$1" = "issue_01161" ]; then
		expected_string="assign z0 = b"
	elif [ "$1" = "issue_01217" ]; then
		expected_string="is implicitly declared."
		expected="0"
	elif [ "$1" = "issue_01291" ]; then
		expected_string="connect \\\out 1'x"
		expected="0"
	fi

	if [ "$1" = "issue_01118" ]; then
		# This issue manifests as an infinite loop.
		timeout 5s yosys -ql yosys.log ../../scripts/$2.ys;
	else
		yosys -ql yosys.log ../../scripts/$2.ys;
	fi

	if [ $? != 0 ] ; then
    	echo FAIL > ${1}_${2}.status
    	touch .stamp
    	exit 0
	fi
	if grep "$expected_string" result.log; then
		if [ $expected = "1" ]; then
			echo PASS > ${1}_${2}.status
		else
			echo FAIL > ${1}_${2}.status
		fi
	else
		if [ $expected = "1" ]; then
			echo FAIL > ${1}_${2}.status
		else
			echo PASS > ${1}_${2}.status
		fi
	fi


# cases with simulation checks
else
	if [ -f "../../../../../techlibs/common/simcells.v" ]; then
		COMMON_PREFIX=../../../../../techlibs/common
		TECHLIBS_PREFIX=../../../../../techlibs
	else
		COMMON_PREFIX=/usr/local/share/yosys
		TECHLIBS_PREFIX=/usr/local/share/yosys
	fi

	iverilog_adds=""
	#Additional sources for iverilog simulation
	if [ "$1" = "issue_00160" ] ||\
		 [ "$1" = "issue_00182" ] ||\
		 [ "$1" = "issue_00183" ] ||\
		 [ "$1" = "issue_00481" ] ||\
		 [ "$1" = "issue_00567" ] ||\
		 [ "$1" = "issue_00589" ] ||\
		 [ "$1" = "issue_00628" ]; then
		iverilog_adds="$TECHLIBS_PREFIX/ice40/cells_sim.v"
	elif [ "$1" = "issue_00896" ]; then
		iverilog_adds="$TECHLIBS_PREFIX/ecp5/cells_sim.v"
	fi

	yosys -ql yosys.log ../../scripts/$2.ys
	if [ $? != 0 ] ; then
    	echo FAIL > ${1}_${2}.status
    	touch .stamp
    	exit 0
	fi
	# cases where we do not run iverilog
	if [ "$1" = "issue_00449" ] ||\
	   [ "$1" = "issue_00084" ]; then
		echo PASS > ${1}_${2}.status
    	touch .stamp
    	exit 0
	fi


	iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $COMMON_PREFIX/simlib.v $iverilog_adds
	if [ $? != 0 ] ; then
    	echo FAIL > ${1}_${2}.status
    	touch .stamp
    	exit 0
	fi

	if ! vvp -N testbench > testbench.log 2>&1; then
		grep 'ERROR' testbench.log
		echo FAIL > ${1}_${2}.status
	elif grep 'ERROR' testbench.log || ! grep 'OKAY' testbench.log; then
		echo FAIL > ${1}_${2}.status
	else
		echo PASS > ${1}_${2}.status
	fi

fi


touch .stamp
