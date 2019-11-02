YOSYS_COARSE=true
TOP="lm32_top"
RTL="lm32_adder.v lm32_addsub.v lm32_cpu.v lm32_dcache.v lm32_debug.v
	lm32_decoder.v lm32_dp_ram.v lm32_dtlb.v lm32_icache.v
	lm32_instruction_unit.v lm32_interrupt.v lm32_itlb.v lm32_jtag.v
	lm32_load_store_unit.v lm32_logic_op.v lm32_mc_arithmetic.v
	lm32_multiplier.v lm32_ram.v lm32_shifter.v lm32_top.v"
SIM="tb_lm32_system.v"
