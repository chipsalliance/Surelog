#!/bin/bash

source scripts/settings.sh

mkdir -p $design/gen
rm -f $design/gen/sim_rtl
rm -f $design/gen/sim_rtl.out

ulimit -v 1048576
iverilog -s testbench -o $design/gen/sim_rtl -I$design/rtl/ -I$design/sim/ $rtl_files $sim_files
vvp -n -l $design/gen/sim_rtl.out $design/gen/sim_rtl

