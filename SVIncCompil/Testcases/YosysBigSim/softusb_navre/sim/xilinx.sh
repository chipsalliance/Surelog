#!/bin/bash
#
# Usage example:
#   bash softusb_navre/sim/xilinx.sh
#   bash scripts/sim_rtl.sh softusb_navre
#   cmp softusb_navre/gen/sim_rtl.out softusb_navre/gen/xilinx.out

set -ex
mkdir -p softusb_navre/gen/

yosys -l softusb_navre/gen/xilinx.log -v2 <<EOT
read_verilog softusb_navre/rtl/softusb_navre.v
synth_xilinx -top softusb_navre
tee -o /dev/stdout stat
write_verilog -noexpr -noattr softusb_navre/gen/xilinx.v
EOT

unisims=/opt/Xilinx/Vivado/2014.4/data/verilog/src/unisims
iverilog -o softusb_navre/gen/xilinx_tb -Isoftusb_navre/sim softusb_navre/gen/xilinx.v softusb_navre/sim/bench.v \
		$(yosys-config --datdir/xilinx/cells_sim.v) $unisims/../glbl.v -y$unisims

vvp -n -l softusb_navre/gen/xilinx.out softusb_navre/gen/xilinx_tb

