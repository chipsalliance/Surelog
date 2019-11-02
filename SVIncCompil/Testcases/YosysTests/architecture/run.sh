#!/bin/bash

set -x
test -d $1

rm -rf $1/work_$2
mkdir $1/work_$2
cd $1/work_$2

touch .start

# cases where 'syntax error' or other errors are expected
if echo "$1" | grep ".*_error"; then

	expected_string=""
	# Change checked string for check other errors
	if echo "$2" | grep ".*_fully_selected"; then
		expected_string="ERROR: This command only operates on fully selected designs!"
	elif [ "$2" = "synth_greenpak4_invalid_part" ]; then
		expected_string="ERROR: Invalid part name: "
	elif [ "$2" = "synth_intel_invalid_family" ]; then
		expected_string="ERROR: Invalid or no family specified:"
	elif [ "$2" = "synth_xilinx_invalid_arch" ]; then
		expected_string="ERROR: Invalid Xilinx -family setting: "
	elif [ "$2" = "synth_xilinx_widemux_1" ]; then
		expected_string="ERROR: -widemux value must be 0 or >= 2."
	elif [ "$2" = "synth_xilinx_abc9_retime" ]; then
		expected_string="ERROR: -retime option not currently compatible with -abc9!"
	elif [ "$2" = "synth_ice40_abc9_retime" ]; then
		expected_string="ERROR: -retime option not currently compatible with -abc9!"
	elif [ "$2" = "synth_ice40_device_unknown" ]; then
		expected_string="ERROR: Invalid or no device specified: "
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

	if [ -f ../run-test.sh ]; then
		../run-test.sh
		if [ $? != 0 ] ; then
			echo FAIL > ${1}_${2}.status
		else
			echo PASS > ${1}_${2}.status
		fi
		touch .stamp
		exit
	else
		test -f scripts/$2.ys
		yosys -ql yosys.log ../../scripts/$2.ys
		if [ $? != 0 ] ; then
			echo FAIL > ${1}_${2}.status
			touch .stamp
			exit 0
		fi
	fi
	if [ -f "../../../../../techlibs/common/simcells.v" ]; then
		COMMON_PREFIX=../../../../../techlibs/common
		TECHLIBS_PREFIX=../../../../../techlibs
	else
		COMMON_PREFIX=/usr/local/share/yosys
		TECHLIBS_PREFIX=/usr/local/share/yosys
	fi

	if [ "$1" = "synth_ecp5" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/ecp5/cells_sim.v
	elif [ "$1" = "synth_ecp5_wide_ffs" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/ecp5/cells_sim.v
	elif [ "$1" = "synth_achronix" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/achronix/speedster22i/cells_sim.v
	elif [ "$1" = "synth_anlogic" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/anlogic/cells_sim.v
	elif [ "$1" = "synth_anlogic_fulladder" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/anlogic/cells_sim.v
	elif [ "$1" = "synth_anlogic_fsm" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/anlogic/cells_sim.v
	elif [ "$1" = "synth_anlogic_mem" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/anlogic/cells_sim.v  $TECHLIBS_PREFIX/anlogic/eagle_bb.v
	elif [ "$1" = "synth_coolrunner2" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/coolrunner2/cells_sim.v
	elif [ "$1" = "synth_coolrunner2_fulladder" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/coolrunner2/cells_sim.v
	elif [ "$1" = "synth_gowin" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/gowin/cells_sim.v
	elif [ "$1" = "synth_gowin_mem" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/gowin/cells_sim.v
	elif [ "$1" = "synth_ice40" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/ice40/cells_sim.v
	elif [ "$1" = "synth_ice40_mem" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/ice40/cells_sim.v
	elif [ "$1" = "synth_ice40_wide_ffs" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/ice40/cells_sim.v
	elif [ "$1" = "synth_ice40_fulladder" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/ice40/cells_sim.v
	elif [ "$1" = "ice40_wrapcarry" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/ice40/cells_sim.v
	elif [ "$1" = "ice40_wrapcarry_adders" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/ice40/cells_sim.v
	elif [ "$1" = "synth_intel" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/intel/max10/cells_sim.v
	elif [ "$1" = "synth_intel_a10gx" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/intel/a10gx/cells_sim.v
	elif [ "$1" = "synth_intel_cycloneiv" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/intel/cycloneiv/cells_sim.v
	elif [ "$1" = "synth_intel_cycloneive" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/intel/cycloneive/cells_sim.v
	elif [ "$1" = "synth_intel_cyclone10" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/intel/cyclone10/cells_sim.v
	elif [ "$1" = "synth_intel_cyclonev" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/intel/cyclonev/cells_sim.v
	elif [ "$1" = "synth_sf2" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/sf2/cells_sim.v
	elif [ "$1" = "synth_xilinx" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/xilinx/cells_sim.v
	elif [ "$1" = "xilinx_srl" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/xilinx/cells_sim.v
	elif [ "$1" = "synth_greenpak4" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/greenpak4/cells_sim_digital.v
	elif [ "$1" = "synth_greenpak4_wide_ffs" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/greenpak4/cells_sim_digital.v
	elif [ "$1" = "synth_greenpak4_dffs_r" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/greenpak4/cells_sim_digital.v
	elif [ "$1" = "synth_efinix" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/efinix/cells_sim.v
	elif [ "$1" = "synth_efinix_fulladder" ]; then
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/efinix/cells_sim.v
	elif [ "$1" = "xilinx_ug901_synthesis_examples" ]; then
		:
	else
		iverilog -o testbench  ../testbench.v synth.v ../../common.v $COMMON_PREFIX/simcells.v
	fi
	if [ $? != 0 ] ; then
		echo FAIL > ${1}_${2}.status
		touch .stamp
		exit 0
	fi
	if [ "$1" = "xilinx_ug901_synthesis_examples" ]; then
		echo PASS > ${1}_${2}.status
	else
		if ! vvp -N testbench > testbench.log 2>&1; then
			grep 'ERROR' testbench.log
			echo FAIL > ${1}_${2}.status
		elif grep 'ERROR' testbench.log || ! grep 'OKAY' testbench.log; then
			echo FAIL > ${1}_${2}.status
		else
			echo PASS > ${1}_${2}.status
		fi
	fi

fi

touch .stamp
