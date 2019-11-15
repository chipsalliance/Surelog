#!/bin/bash

source scripts/settings.sh

mkdir -p $design/gen
rm -f $design/gen/synth.ys
rm -f $design/gen/synth.v
rm -f $design/gen/sim_synth
rm -f $design/gen/sim_synth.out

{
	for file in $rtl_files; do
		echo "read_verilog -I$design/rtl/ -I$design/sim/ $file"
	done
	if test -n "$TOP"; then
		echo "hierarchy -check -top $TOP"
	else
		echo "hierarchy -check"
	fi
	if $YOSYS_GLOBRST; then
		# insertation of global reset (e.g. for FPGA cores)
		echo "add -global_input globrst 1"
		echo "proc -global_arst globrst"
	fi
	echo "synth -run coarse; opt -fine"
	echo "tee -o $design/gen/brams.log memory_bram -rules scripts/brams.txt;;"
	if ! $YOSYS_COARSE; then
		echo "memory_map; techmap; opt; abc -dff; clean"
	fi
	if $YOSYS_SPLITNETS; then
		# icarus verilog has a performance problems when there are
		# dependencies between the bits of a long vector
		echo "splitnets; clean"
	fi
	if $YOSYS_COARSE; then
		echo "write_verilog -noexpr -noattr $design/gen/synth.v"
	else
		echo "select -assert-none t:\$[!_]"
		echo "write_verilog -noattr $design/gen/synth.v"
	fi
} > $design/gen/synth.ys
yosys -v2 -l $design/gen/synth.log $design/gen/synth.ys

if $YOSYS_COARSE; then
	sim_files="$sim_files $( yosys-config --datdir/simlib.v )"
fi

if [ $design = bch_verilog ]; then
	# https://github.com/steveicarus/iverilog/issues/28
	sed -i 's,OPTION="SERIAL",OPTION=SERIAL,g' $design/gen/synth.v
fi

ulimit -v 1048576
iverilog -s testbench -o $design/gen/sim_synth -I$design/rtl/ -I$design/sim/ $design/gen/synth.v $sim_files scripts/brams.v
vvp -n -l $design/gen/sim_synth.out $design/gen/sim_synth

