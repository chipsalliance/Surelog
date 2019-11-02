
set hdlin_ignore_full_case false
set hdlin_warn_on_mismatch_message "FMR_ELAB-115 FMR_ELAB-146 FMR_ELAB-147"

read_verilog -container r -libname WORK -01 { rtl/i2c_master_bit_ctrl.v rtl/i2c_master_byte_ctrl.v rtl/i2c_master_top.v }
set_top r:/WORK/i2c_master_top

read_verilog -container i -libname WORK -01 output/synth.v
set_top i:/WORK/i2c_master_top

verify
exit

