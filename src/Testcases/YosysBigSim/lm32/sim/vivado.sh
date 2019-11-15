#!/bin/bash
# Run 'bash lm32/sim/xilinx.sh' first.

cat > lm32/gen/vivado_rtl.tcl << EOT
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
synth_design -part xc7k70t -top lm32_top -verilog_define USE_MY_CLOG2
opt_design
place_design
route_design
report_utilization
report_timing
close_project
EOT

cat > lm32/gen/vivado_yosys.tcl << EOT
read_verilog lm32/gen/xilinx.v
synth_design -part xc7k70t -top lm32_top
opt_design
place_design
route_design
report_utilization
report_timing
close_project
EOT

/opt/Xilinx/Vivado/2014.4/bin/vivado -mode batch -nojournal -log lm32/gen/vivado_rtl.log -source lm32/gen/vivado_rtl.tcl
/opt/Xilinx/Vivado/2014.4/bin/vivado -mode batch -nojournal -log lm32/gen/vivado_yosys.log -source lm32/gen/vivado_yosys.tcl

