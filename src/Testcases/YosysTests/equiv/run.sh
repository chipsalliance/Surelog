#!/bin/bash

set -x
test -d $1
test -f scripts/$2.ys

rm -rf $1/work_$2
mkdir $1/work_$2
cd $1/work_$2

touch .start

# cases where 'syntax error' or other errors are expected
if echo "$1" | grep ".*_error"; then

	expected_string=""
    #Change checked string for check other errors
	if [ "$2" = "equiv_add_module_context" ]; then
		expected_string="ERROR: This command must be executed in module context!"
	elif [ "$2" = "equiv_add_cant_find_gold_cell" ]; then
		expected_string="ERROR: Can't find gold cell"
	elif [ "$2" = "equiv_add_cant_find_gate_cell" ]; then
		expected_string="ERROR: Can't find gate cell"
	elif [ "$2" = "equiv_add_invalid_number_of_args" ]; then
		expected_string="ERROR: Invalid number of arguments."
	elif [ "$2" = "equiv_make_synth_error" ]; then
		expected_string="ERROR: Syntax error in encfile '../encfile_synth_error.fsm'!"
	elif [ "$2" = "equiv_make_redefenition_of_signal" ]; then
		expected_string="ERROR: Re-definition of signal"
	elif [ "$2" = "equiv_make_cant_open_encfile" ]; then
		expected_string="ERROR: Can't open encfile 'encfile111.fsm'!"
	elif [ "$2" = "equiv_make_cant_open_blacklist" ]; then
		expected_string="ERROR: Can't open blacklist file '../black.txt'!"
	elif [ "$2" = "equiv_make_cant_find_gate_mod" ]; then
		expected_string="ERROR: Can't find gate module"
	elif [ "$2" = "equiv_make_cant_find_gold_mod" ]; then
		expected_string="ERROR: Can't find gold module"
	elif [ "$2" = "equiv_make_invalid_num_of_args" ]; then
		expected_string="ERROR: Invalid number of arguments"
	elif [ "$2" = "equiv_make_cant_match" ]; then
		expected_string="ERROR: Can't match gate port \`rst_gate' to a gold port"
	elif [ "$2" = "equiv_make_cant_match_gold_to_gate" ]; then
		expected_string="ERROR: Can't match gold port \`set_gold' to a gate port"
	elif [ "$2" = "equiv_make_equiv_mod_already_exists" ]; then
		expected_string="ERROR: Equiv module equiv already exists."
	elif [ "$2" = "equiv_make_gold_mod_contains_proc" ]; then
		expected_string="ERROR: Gold module contains memories or processes. Run 'memory' or 'proc' respectively."
	elif [ "$2" = "equiv_make_gate_mod_contains_proc" ]; then
		expected_string="ERROR: Gate module contains memories or processes. Run 'memory' or 'proc' respectively."
	elif [ "$2" = "equiv_miter_invalid_num_of_args" ]; then
		expected_string="ERROR: Invalid number of arguments."
	elif [ "$2" = "equiv_miter_miter_module_already_exists" ]; then
		expected_string="ERROR: Miter module equiv already exists"
	elif [ "$2" = "equiv_miter_one_module_must_be_selected" ]; then
		expected_string="ERROR: Exactly one module must be selected for 'equiv_miter'!"
	elif [ "$2" = "equiv_opt_unknown_option" ]; then
		expected_string="ERROR: Command syntax error: Unknown option."
	elif [ "$2" = "equiv_opt_no_opt" ]; then
		expected_string="ERROR: No optimization pass specified!"
	elif [ "$2" = "equiv_opt_fully_selected_des" ]; then
		expected_string="ERROR: This command only operates on fully selected designs!"
	elif [ "$2" = "equiv_remove_gold_gate" ]; then
		expected_string="ERROR: Options -gold and -gate are exclusive."
	elif [ "$2" = "equiv_status_assert" ]; then
		expected_string="ERROR: Found 1 unproven \$equiv cells in 'equiv_status -assert'."


	fi


	if yosys -ql yosys.log ../../scripts/$2.ys; then
		echo FAIL > ${1}_${2}.status
	else
		if  grep "$expected_string" yosys.log && [ "$expected_string" != "" ]; then
			echo PASS > ${1}_${2}.status
		else
			echo FAIL > ${1}_${2}.status
		fi
	fi
else


	yosys -ql yosys.log ../../scripts/$2.ys
	if [ $? != 0 ] ; then
		echo FAIL > ${1}_${2}.status
		touch .stamp
		exit 0
	fi
	sed -i 's/reg =/dummy =/' ./synth.v

	if [ -f "../../../../../techlibs/common/simcells.v" ]; then
		COMMON_PREFIX=../../../../../techlibs/common
	else
		COMMON_PREFIX=/usr/local/share/yosys
	fi

	iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $COMMON_PREFIX/simlib.v
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
