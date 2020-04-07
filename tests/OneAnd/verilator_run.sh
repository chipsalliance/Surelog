#!/bin/sh

verilator  --cc  --trace syn_tb.v dut.v --exe sim_main.cpp
make -j -C obj_dir/ -f Vsyn_tb.mk Vsyn_tb
obj_dir/Vsyn_tb 
vcddiff syn_tb.vcd syn_tb.vcd.rtl
#gtkwave syn_tb.vcd  
