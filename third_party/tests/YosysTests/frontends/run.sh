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
	if [ "$2" = "read_aiger_cant_interpret_first_char" ]; then
		expected_string="ERROR: Line 80: cannot interpret first character"
	elif [ "$2" = "read_aiger_unsup_aiger_file" ]; then
		expected_string="ERROR: Unsupported AIGER file!"
	elif [ "$2" = "read_aiger_invalid_aiger_header" ]; then
		expected_string="ERROR: Invalid AIGER header"
	elif [ "$2" = "read_aiger_cant_interpret_as_input" ]; then
		expected_string="ERROR: Line 2 cannot be interpreted as an input!"
	elif [ "$2" = "read_aiger_cant_interpret_as_and" ]; then
		expected_string="ERROR: Line 6 cannot be interpreted as an AND!"
	elif [ "$2" = "read_aiger_bad_state_property" ]; then
		expected_string="ERROR: Line 4 cannot be interpreted as a bad state property!"
	elif [ "$2" = "read_aiger_invalid_reset_literal" ]; then
		expected_string="ERROR: Line 1 has invalid reset literal for latch!"
	elif [ "$2" = "read_aiger_duplicate_definition" ]; then
		expected_string="ERROR: Duplicate definition of module top!"
	elif [ "$2" = "read_blif_syntax_error" ]; then
		expected_string="ERROR: Syntax error in line"
	elif [ "$2" = "read_blif_duplicate_defenition" ]; then
		expected_string="ERROR: Duplicate definition of module "
	elif [ "$2" = "read_ilang_parse_error" ]; then
		expected_string="ERROR: Parser error in line "
	elif [ "$2" = "read_json_nonstring_key" ]; then
		expected_string="ERROR: Unexpected non-string key in JSON dict."
	elif [ "$2" = "read_json_nonarray_bits_attr" ]; then
		expected_string=" has non-array bits attribute."
	elif [ "$2" = "read_json_unexpected_eof" ]; then
		expected_string="ERROR: Unexpected EOF in JSON file."
	elif [ "$2" = "read_json_invalid_direction" ]; then
		expected_string="ERROR: JSON port node 'x' has invalid 'insdfasdfput' direction attribute."
	elif [ "$2" = "read_json_no_bits" ]; then
		expected_string=" has no bits attribute."
	elif [ "$2" = "read_json_no_direction" ]; then
		expected_string=" has no direction attribute."
	elif [ "$2" = "read_json_unexpected_char" ]; then
		expected_string="ERROR: Unexpected character in JSON file: "
	elif [ "$2" = "verilog_defaults_missing_arg" ]; then
		expected_string="ERROR: Command syntax error: Missing argument."
	elif [ "$2" = "verilog_defaults_extra_arg" ]; then
		expected_string="ERROR: Command syntax error: Extra argument."
	elif [ "$2" = "verilog_defines_extra_arg" ]; then
		expected_string="ERROR: Command syntax error: Extra argument."
	elif [ "$2" = "read_liberty_invalid_bus_type" ]; then
		expected_string="ERROR: Missing or invalid direction for bus B on cell bused_cell."
	elif [ "$2" = "read_liberty_unsupp_type_for_bus" ]; then
		expected_string="ERROR: Unknown or unsupported type for bus interface D on cell top."
	elif [ "$2" = "read_liberty_bus_interface_only_in_lib_mode" ]; then
		expected_string="ERROR: Error in cell top: bus interfaces are only supported in -lib mode."
	elif [ "$2" = "read_liberty_latch_has_no_data_in" ]; then
		expected_string="ERROR: Latch cell top has no data_in and/or enable attribute."
	elif [ "$2" = "read_liberty_miss_func_on_output" ]; then
		expected_string="ERROR: Missing function on output Y of cell top."
	elif [ "$2" = "read_liberty_ff_has_no_next_stage_attr" ]; then
		expected_string="ERROR: FF cell top has no next_state and/or clocked_on attribute."
	elif [ "$2" = "read_liberty_parse_error_in_function" ]; then
		expected_string="ERROR: Parser error in function expr "
	elif [ "$2" = "read_liberty_cant_resolve_wire_name" ]; then
		expected_string="ERROR: Can't resolve wire name s."
	elif [ "$2" = "read_liberty_missing_direction" ]; then
		expected_string="ERROR: Missing or invalid direction for pin A on cell top."
	elif [ "$2" = "read_liberty_cant_open_input_file" ]; then
		expected_string="ERROR: Can't open input file \`../libbbb.lib' for reading: No such file or directory"
	elif [ "$2" = "read_liberty_redefenition_of_module" ]; then
		expected_string="ERROR: Re-definition of cell/module top!"
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
