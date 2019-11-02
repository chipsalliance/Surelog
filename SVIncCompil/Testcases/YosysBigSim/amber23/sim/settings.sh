YOSYS_COARSE=true
YOSYS_GLOBRST=true
TOP="a23_core"
RTL="a23_alu.v a23_barrel_shift_fpga.v a23_barrel_shift.v a23_cache.v
	a23_coprocessor.v a23_core.v a23_decode.v a23_execute.v a23_fetch.v
	a23_multiply.v a23_ram_register_bank.v a23_register_bank.v
	a23_wishbone.v generic_sram_byte_en.v generic_sram_line_en.v"
SIM="bench.v"
