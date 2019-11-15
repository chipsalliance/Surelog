#!/bin/bash

source scripts/settings.sh

mkdir -p $design/gen
rm -f $design/gen/sim_modelsim
rm -f $design/gen/sim_modelsim.out

# rtl_files=$design/gen/synth1.v

MODELSIM_DIR=/opt/altera/13.1/modelsim_ase/bin
$MODELSIM_DIR/vlib work
for f in $rtl_files $sim_files; do
	$MODELSIM_DIR/vlog +incdir+$design/rtl +incdir+$design/sim $f
done
$MODELSIM_DIR/vsim -c -do "run -all; exit" work.testbench | tee $design/gen/sim_modelsim.out
rm -rf transcript work

