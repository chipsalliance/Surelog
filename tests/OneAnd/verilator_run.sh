#!/bin/sh
# Synthesize
rm -rf synth_dut.v
yosys synth.ys
sed -i 's/dut/synth_dut/g' synth_dut.v
# Generate C code
verilator -Wall --cc --assert --trace syn_tb.v dut.v synth_dut.v --exe sim_main.cpp
# Compile C code
make -j -C obj_dir/ -f Vsyn_tb.mk Vsyn_tb
# Run Simulation
obj_dir/Vsyn_tb 
# Diff VCD file
vcddiff syn_tb.vcd syn_tb.vcd.rtl
# Inspect Waveform (Optional)
# gtkwave syn_tb.vcd  
