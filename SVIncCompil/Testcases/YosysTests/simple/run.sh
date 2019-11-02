#!/bin/bash

set -x
test -d $1

if [ "$2" != "verify" -a "$2" != "falsify" ]; then
	test -f scripts/$2.ys
fi

rm -rf $1/work_$2
mkdir $1/work_$2
cd $1/work_$2

touch .start

# cases where 'syntax error' or other errors are expected
if echo "$1" | grep ".*_error"; then

	expected_string=""
    #Change checked string for check other errors
	if [ "$2" = "dff2dffe_error" ]; then
		expected_string="ERROR: No cell types matched pattern "
	elif [ "$2" = "extract_mine_and_map" ]; then
		expected_string="ERROR: You cannot mix -map and -mine."
	elif [ "$2" = "extract_map_and_mine" ]; then
		expected_string="ERROR: You cannot mix -map and -mine."
	elif [ "$2" = "extract_args_to_perm" ]; then
		expected_string="ERROR: Arguments to -perm are not a valid permutation!"
	elif [ "$2" = "extract_missing_opt" ]; then
		expected_string="ERROR: Missing option -map <verilog_or_ilang_file> or -mine <output_ilang_file>."
	elif [ "$2" = "extract_cant_open_map_file" ]; then
		expected_string="ERROR: Can't open map file"
	elif [ "$2" = "extract_cant_open_output" ]; then
		expected_string="ERROR: Can't open output file"
	elif [ "$2" = "extract_counter_pout_without_args" ]; then
		expected_string="ERROR: extract_counter -pout requires an argument"
	elif [ "$2" = "fsm_export_couldnt_open_file" ]; then
		expected_string="ERROR: Could not open file \"tt/fsm.kiss2\" with write access."
	elif [ "$2" = "fsm_recode_encoding_isnt_supported" ]; then
		expected_string="ERROR: FSM encoding \`binari' is not supported!"
	elif [ "$2" = "fsm_recode_cant_open_fm_set_fsm_file" ]; then
		expected_string="ERROR: Can't open fm_set_fsm_file"
	elif [ "$2" = "fsm_recode_cant_open_encfile" ]; then
		expected_string="ERROR: Can't open encfile "
	elif [ "$2" = "hierarchy_no_top_module" ]; then
		expected_string="ERROR: Design has no top module."
	elif [ "$2" = "hierarchy_top_requires_args" ]; then
		expected_string="ERROR: Option -top requires an additional argument!"
	elif [ "$2" = "hierarchy_module_not_found" ]; then
		expected_string="ERROR: Module \`uu' not found!"
	elif [ "$2" = "memory_bram_syntax_error_in_rules" ]; then
		expected_string="ERROR: Syntax error in rules file line"
	elif [ "$2" = "memory_bram_cant_open_rules_file" ]; then
		expected_string="ERROR: Can't open rules file "
	elif [ "$2" = "nlutmap_error" ]; then
		expected_string="ERROR: Insufficient number of LUTs to map all logic cells!"
	elif [ "$2" = "prep_error" ]; then
		expected_string="ERROR: This command only operates on fully selected designs!"
	elif [ "$2" = "shregmap_zinit_init" ]; then
		expected_string="ERROR: Options -zinit and -init are exclusive!"
	elif [ "$2" = "shregmap_match_clkpol" ]; then
		expected_string="ERROR: Options -clkpol and -match are exclusive!"
	elif [ "$2" = "shregmap_match_enpol" ]; then
		expected_string="ERROR: Options -enpol and -match are exclusive!"
	elif [ "$2" = "shregmap_match_params" ]; then
		expected_string="ERROR: Options -params and -match are exclusive!"
	elif [ "$2" = "submod_error" ]; then
		expected_string="ERROR: More than one module selected:"
	elif [ "$2" = "synth_error" ]; then
		expected_string="ERROR: This command only operates on fully selected designs!"
	elif [ "$2" = "synth_abc9_no_lut" ]; then
		expected_string="ERROR: ABC9 flow only supported for FPGA synthesis (using '-lut' option)"
	elif [ "$2" = "zinit_failed_to_handle" ]; then
		expected_string="ERROR: Failed to handle init bit"
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

	if [ "$2" = "verify" ]; then
		iverilog -o testbench ../testbench.v ../../common.v ../top.v
		if [ $? != 0 ] ; then
			echo FAIL > ${1}_${2}.status
			touch .stamp
			exit 0
		fi
	elif [ "$2" = "falsify" ]; then
		iverilog -DBUG -o testbench ../testbench.v ../../common.v ../top.v
		if [ $? != 0 ] ; then
			echo FAIL > ${1}_${2}.status
			touch .stamp
			exit 0
		fi
	else
		yosys -ql yosys.log ../../scripts/$2.ys
		if [ $? != 0 ] ; then
			echo FAIL > ${1}_${2}.status
			touch .stamp
			exit 0
		fi

		if [ -f "../../../../../techlibs/common/simcells.v" ]; then
			COMMON_PREFIX=../../../../../techlibs/common
		else
			COMMON_PREFIX=/usr/local/share/yosys
		fi
		iverilog -o testbench ../testbench.v ../../common.v synth.v $COMMON_PREFIX/simcells.v
		if [ $? != 0 ] ; then
			echo FAIL > ${1}_${2}.status
			touch .stamp
			exit 0
		fi
	fi

	if [ "$2" = "falsify" ]; then
		if vvp -N testbench > testbench.log 2>&1; then
			echo FAIL > ${1}_${2}.status
		elif ! grep 'ERROR' testbench.log || grep 'OKAY' testbench.log; then
			echo FAIL > ${1}_${2}.status
		else
			echo PASS > ${1}_${2}.status
		fi
	else
		#cases where some object names are/aren't expected in output file (tee -o result.log in the test script)
		cell_failed="0"
		if test -f "result.log"; then
			expected_string=""
			expected="1"

			if [ "$1" = "aigmap" ]; then
				expected_string="\$mux"
				expected="0"
			elif [ "$1" = "async2sync" ] ||\
				[ "$1" = "clk2fflogic" ] ||\
				[ "$1" = "clk2fflogic_latch" ] ||\
				[ "$1" = "clk2fflogic_mem" ]; then
				expected_string="\$adff"
				expected="0"
			elif [ "$1" = "dff2dffe_unmap" ]; then
				expected_string="\$dffe"
				expected="0"
			elif [ "$1" = "flowmap" ] ||\
				[ "$1" = "flowmap_latch" ] ||\
				[ "$1" = "flowmap_mem" ]; then
				expected_string="cell \$lut \$auto\$flowmap"
			elif [ "$1" = "fsm" ] ||\
				[ "$1" = "fsm_expand" ] ||\
				[ "$1" = "fsm_export" ] ||\
				[ "$1" = "fsm_opt" ] ||\
				[ "$1" = "fsm_recode" ] ||\
				[ "$1" = "fsm_unreach" ]; then
				expected_string="cell \$fsm"
			elif [ "$1" = "full_adder" ]; then
				expected_string="\$fa"
			elif [ "$1" = "ice40_dsp_mult" ] ||\
				[ "$1" = "ice40_dsp_mult_acc" ]; then
				expected_string="SB_MAC16"
			elif [ "$1" = "ice40_dsp_mult_a_larger" ] ||\
				[ "$1" = "ice40_dsp_mult_b_larger" ] ||\
				[ "$1" = "ice40_dsp_mult_out_larger" ] ||\
				[ "$1" = "ice40_dsp_mult_signed" ]; then
				expected_string="\$mul"
			elif [ "$1" = "inout_port_demote" ]; then
				expected_string="inout"
				expected="0"
			elif [ "$1" = "iopadmap" ]; then
				expected_string="IBUF \$auto\$iopadmap"
			elif [ "$1" = "macc" ]; then
				expected_string="cell \$macc"
				expected="0"
			elif [ "$1" = "memory" ] ||
				[ "$1" = "memory_single_port" ]; then
				expected_string="cell \$mem "
				expected="0"
			elif [ "$1" = "muxcover" ] ||\
				[ "$1" = "muxcover_mux8" ]; then
				expected_string="\$_MUX_"
				expected="0"
			elif [ "$1" = "nlutmap" ]; then
				expected_string="\$lut"
				expected="0"
			elif [ "$1" = "nlutmap_opt" ]; then
				expected_string="\$lut"
			elif [ "$1" = "opt_demorgan_reduce" ]; then
				expected_string="cell \$not \$auto\$opt_demorgan"
			elif [ "$1" = "reduce" ]; then
				expected_string="cell \$reduce_"
			elif [ "$1" = "tribuf" ]; then
				expected_string="cell \$tribuf"
			elif [ "$1" = "tribuf_logic" ]; then
				expected_string="cell \$tribuf"
				expected="0"
			fi
			if test -f "result.log"; then
				if grep "$expected_string" result.log; then
					if [ $expected = "1" ]; then
						cell_failed="0"
					else
						cell_failed="1"
					fi
				else
					if [ $expected = "1" ]; then
						cell_failed="1"
					else
						cell_failed="0"
					fi
				fi
			fi
		fi

		if ! vvp -N testbench > testbench.log 2>&1; then
			grep 'ERROR' testbench.log
			echo FAIL > ${1}_${2}.status
		elif grep 'ERROR' testbench.log || ! grep 'OKAY' testbench.log; then
			echo FAIL > ${1}_${2}.status
		elif [ $cell_failed = '1' ]; then
			echo FAIL > ${1}_${2}.status
		else
			echo PASS > ${1}_${2}.status
		fi
	fi

fi
touch .stamp
