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
	if [ "$2" = "write_aiger_cant_find_top_module" ]; then
		expected_string="ERROR: Can't find top module in current design!"
	elif [ "$2" = "write_aiger_cant_open_file" ]; then
		expected_string="ERROR: Can't open file "
	elif [ "$2" = "write_aiger_miter_and_asserts" ]; then
		expected_string="ERROR: Running AIGER back-end in -miter mode, but design contains \$assert, \$assume, \$live and/or \$fair cells!"
	elif [ "$2" = "write_aiger_unsupported_cell_type" ]; then
		expected_string="ERROR: Unsupported cell type: "
	elif [ "$2" = "write_xaiger_cant_find_top_module" ]; then
		expected_string="ERROR: Can't find top module in current design!"
	elif [ "$2" = "write_xaiger_cant_open_file" ]; then
		expected_string="ERROR: Can't open file "
	elif [ "$2" = "write_blif_unmapped_mem" ]; then
		expected_string="ERROR: Found unmapped memories in module "
	elif [ "$2" = "write_blif_cant_find_top_module" ]; then
		expected_string="ERROR: Can't find top module "
	elif [ "$2" = "write_blif_unmapped_proc" ]; then
		expected_string="ERROR: Found unmapped processes in module "
	elif [ "$2" = "write_btor_no_top_module" ]; then
		expected_string="ERROR: No top module found."
	elif [ "$2" = "write_btor_unsupported_cell_type" ]; then
		expected_string="ERROR: Unsupported cell type: "
	elif [ "$2" = "write_btor_no_driver" ]; then
		expected_string="ERROR: No driver for signal bit "
	elif [ "$2" = "write_edif_cyclic_dependency" ]; then
		expected_string="ERROR: Cyclic dependency between modules found! Cycle includes module "
	elif [ "$2" = "write_edif_constant_nodes" ]; then
		expected_string="ERROR: Design contains constant nodes (map with \"hilomap\" first)."
	elif [ "$2" = "write_edif_unmapped_mem" ]; then
		expected_string="ERROR: Found unmapped memories in module "
	elif [ "$2" = "write_edif_unmapped_proc" ]; then
		expected_string="ERROR: Found unmapped processes in module "
	elif [ "$2" = "write_edif_no_module_found" ]; then
		expected_string="ERROR: No module found in design!"
	elif [ "$2" = "write_firrtl_fully_selected" ]; then
		expected_string="ERROR: This command only operates on fully selected designs!"
	elif [ "$2" = "write_firrtl_negative_edge_ff" ]; then
		expected_string="ERROR: Negative edge clock on FF "
	elif [ "$2" = "write_firrtl_inout_port" ]; then
		expected_string="ERROR: Module port top.q_a is inout!"
	elif [ "$2" = "write_firrtl_unclocked_write_port" ]; then
		expected_string="ERROR: Unclocked write port "
	elif [ "$2" = "write_firrtl_complex_write_enable" ]; then
		expected_string="ERROR: Complex write enable on port "
	elif [ "$2" = "write_ilang_error" ]; then
		expected_string="ERROR: Can't open file \`tt/file1.il' for writing: No such file or directory"
	elif [ "$2" = "write_intersynth_cant_export" ]; then
		expected_string="ERROR: Can't export composite or non-word-wide signal "
	elif [ "$2" = "write_intersynth_unprocessed_proc" ]; then
		expected_string="ERROR: Can't generate a netlist for a module with unprocessed memories or processes!"
	elif [ "$2" = "write_intersynth_cant_open_lib_file" ]; then
		expected_string="ERROR: Can't open lib file "
	elif [ "$2" = "write_json_error" ]; then
		expected_string="ERROR: Can't open file "
	elif [ "$2" = "write_simplec_no_c_model" ]; then
		expected_string="ERROR: No C model for \$lut available at the moment (FIXME)."
	elif [ "$2" = "write_simplec_not_top_module" ]; then
		expected_string="ERROR: Current design has no top module."
	elif [ "$2" = "write_smt2_cyclic_dependency" ]; then
		expected_string="ERROR: Cyclic dependency between modules found! Cycle includes module "
	elif [ "$2" = "write_smt2_cant_open_tpl" ]; then
		expected_string="ERROR: Can't open template file "
	elif [ "$2" = "write_smt2_multiple_drivers" ]; then
		expected_string="ERROR: Found multiple drivers for "
	elif [ "$2" = "write_smt2_logic_loop" ]; then
		expected_string="ERROR: Found logic loop in module "
	elif [ "$2" = "write_smv_cant_open_template" ]; then
		expected_string="ERROR: Can't open template file "
	elif [ "$2" = "write_smv_unsupported_cell" ]; then
		expected_string="ERROR: Found currently unsupported cell type "
	elif [ "$2" = "write_spice_cant_find_top_module" ]; then
		expected_string="ERROR: Can't find top module "
	elif [ "$2" = "write_spice_unmapped_mem" ]; then
		expected_string="ERROR: Found unmapped memories in module "
	elif [ "$2" = "write_spice_unmapped_proc" ]; then
		expected_string="ERROR: Found unmapped processes in module"
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
