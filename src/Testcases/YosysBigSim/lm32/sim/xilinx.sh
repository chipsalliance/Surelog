#!/bin/bash
#
# Usage example:
#   bash lm32/sim/xilinx.sh
#   bash scripts/sim_rtl.sh lm32
#   cmp lm32/gen/sim_rtl.out lm32/gen/xilinx.out

set -ex
mkdir -p lm32/gen/

yosys -l lm32/gen/xilinx.log -v2 <<EOT
read_verilog lm32/rtl/lm32_adder.v
read_verilog lm32/rtl/lm32_addsub.v
read_verilog lm32/rtl/lm32_cpu.v
read_verilog lm32/rtl/lm32_dcache.v
read_verilog lm32/rtl/lm32_debug.v
read_verilog lm32/rtl/lm32_decoder.v
read_verilog lm32/rtl/lm32_dp_ram.v
read_verilog lm32/rtl/lm32_dtlb.v
read_verilog lm32/rtl/lm32_icache.v
read_verilog lm32/rtl/lm32_instruction_unit.v
read_verilog lm32/rtl/lm32_interrupt.v
read_verilog lm32/rtl/lm32_itlb.v
read_verilog lm32/rtl/lm32_jtag.v
read_verilog lm32/rtl/lm32_load_store_unit.v
read_verilog lm32/rtl/lm32_logic_op.v
read_verilog lm32/rtl/lm32_mc_arithmetic.v
read_verilog lm32/rtl/lm32_multiplier.v
read_verilog lm32/rtl/lm32_ram.v
read_verilog lm32/rtl/lm32_shifter.v
read_verilog lm32/rtl/lm32_top.v
synth_xilinx -top lm32_top
tee -o /dev/stdout stat
write_verilog -noexpr -noattr lm32/gen/xilinx.v
EOT

unisims=/opt/Xilinx/Vivado/2014.4/data/verilog/src/unisims
iverilog -o lm32/gen/xilinx_tb -Ilm32/rtl lm32/gen/xilinx.v lm32/sim/tb_lm32_system.v \
		$(yosys-config --datdir/xilinx/cells_sim.v) $unisims/../glbl.v -y$unisims

vvp -n -l lm32/gen/xilinx.out lm32/gen/xilinx_tb

