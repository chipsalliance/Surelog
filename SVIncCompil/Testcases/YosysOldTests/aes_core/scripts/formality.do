
set hdlin_ignore_full_case false
set hdlin_warn_on_mismatch_message "FMR_ELAB-115 FMR_ELAB-146 FMR_ELAB-147"

read_verilog -container r -libname WORK -01 { rtl/aes_cipher_top.v rtl/aes_inv_cipher_top.v rtl/aes_inv_sbox.v rtl/aes_key_expand_128.v rtl/aes_rcon.v rtl/aes_sbox.v }
set_top r:/WORK/aes_cipher_top

read_verilog -container i -libname WORK -01 output/synth.v
set_top i:/WORK/aes_cipher_top

verify
exit

