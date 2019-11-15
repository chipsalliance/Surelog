#!/bin/bash

set -x
source $1/config
mkdir -p $1/work_$2
cd $1/work_$2

touch .start

iverilog_cmd="iverilog -o sim -s testbench -I../rtl -I../sim $SIMARGS"

rtl_files=""
for fn in $RTL; do
	rtl_files="$rtl_files ../rtl/$fn"
done

if [ -f "../../../../../techlibs/common/simcells.v" ]; then
    TECHLIBS_PREFIX=../../../../../techlibs
else
    TECHLIBS_PREFIX=/usr/local/share/yosys
fi

case "$2" in
	sim)
		touch ../../.start
		iverilog_cmd="$iverilog_cmd $rtl_files"
		;;
	falsify)
		iverilog_cmd="$iverilog_cmd -D${BUGMACRO:-BUG} $rtl_files"
		;;
	cmos)
		yosys -ql synthlog.txt -p "$PRESYN; synth -top $TOP; abc -g cmos4; write_verilog synth.v" $rtl_files
		iverilog_cmd="$iverilog_cmd synth.v"
		;;
	ice40)
		yosys -ql synthlog.txt -p "$PRESYN; synth_ice40 -top $TOP; write_verilog synth.v" $rtl_files
		iverilog_cmd="$iverilog_cmd synth.v $TECHLIBS_PREFIX/ice40/cells_sim.v"
		;;
	ice40_abc9)
		yosys -ql synthlog.txt -p "$PRESYN; synth_ice40 -abc9 -top $TOP; write_verilog synth.v" $rtl_files
		iverilog_cmd="$iverilog_cmd synth.v $TECHLIBS_PREFIX/ice40/cells_sim.v"
		;;
	ecp5)
		yosys -ql synthlog.txt -p "$PRESYN; synth_ecp5 -top $TOP; write_verilog synth.v" $rtl_files
		iverilog_cmd="$iverilog_cmd synth.v $TECHLIBS_PREFIX/ecp5/cells_sim.v -I$TECHLIBS_PREFIX/ecp5"
		;;
	ecp5_abc9)
		yosys -ql synthlog.txt -p "$PRESYN; synth_ecp5 -abc9 -top $TOP; write_verilog synth.v" $rtl_files
		iverilog_cmd="$iverilog_cmd synth.v $TECHLIBS_PREFIX/ecp5/cells_sim.v -I$TECHLIBS_PREFIX/ecp5"
		;;
	xilinx)
		yosys -ql synthlog.txt -p "$PRESYN; synth_xilinx -top $TOP; write_verilog synth.v" $rtl_files
		iverilog_cmd="$iverilog_cmd synth.v $TECHLIBS_PREFIX/xilinx/cells_sim.v"
		;;
	xilinx_abc9)
		yosys -ql synthlog.txt -p "$PRESYN; synth_xilinx -abc9 -top $TOP; write_verilog synth.v" $rtl_files
		iverilog_cmd="$iverilog_cmd synth.v $TECHLIBS_PREFIX/xilinx/cells_sim.v"
		;;
	*)
		exit 1
		;;
esac

for fn in $SIM; do
	iverilog_cmd="$iverilog_cmd ../sim/$fn"
done
$iverilog_cmd
if [ $? != 0 ] ; then
	echo FAIL > ${1}_${2}.status
	touch .stamp
	exit 0
fi

vvp -N sim $PLUSARGS | pv -l > output.txt
if [ $? != 0 ] ; then
    echo FAIL > ${1}_${2}.status
    touch .stamp
fi

if [ "$2" = "falsify" ]; then
	if cmp output.txt ../work_sim/output.txt; then
		echo FAIL > ../../${1}_${2}.status
	else
		echo PASS > ../../${1}_${2}.status
	fi
elif [ "$2" != "sim" ]; then
	if cmp output.txt ../work_sim/output.txt; then
		echo PASS > ../../${1}_${2}.status
	else
		echo FAIL > ../../${1}_${2}.status
	fi
elif [ "$2" == "sim" ]; then
	echo PASS > ../../${1}_${2}.status
fi
