#!/bin/bash
# Run 'bash softusb_navre/sim/xilinx.sh' first.

cat > softusb_navre/gen/vivado_rtl.tcl << EOT
read_verilog softusb_navre/rtl/softusb_navre.v
synth_design -part xc7k70t -top softusb_navre
opt_design
place_design
route_design
report_utilization
report_timing
close_project
EOT

cat > softusb_navre/gen/vivado_yosys.tcl << EOT
read_verilog softusb_navre/gen/xilinx.v
synth_design -part xc7k70t -top softusb_navre
opt_design
place_design
route_design
report_utilization
report_timing
close_project
EOT

/opt/Xilinx/Vivado/2014.4/bin/vivado -mode batch -nojournal -log softusb_navre/gen/vivado_rtl.log -source softusb_navre/gen/vivado_rtl.tcl
/opt/Xilinx/Vivado/2014.4/bin/vivado -mode batch -nojournal -log softusb_navre/gen/vivado_yosys.log -source softusb_navre/gen/vivado_yosys.tcl

