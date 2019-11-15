CROSS_COMPILE ?= lm32-elf-

# extra plusargs for simulation
# eg. EXTRA_PLUSARGS = "+dump=dump.vcd"
EXTRA_PLUSARGS ?=

# enable additional debug output
# eg. EXTRA_DEFINES = "-DTB_ENABLE_WB_TRACES"
EXTRA_DEFINES ?=

CC      = $(CROSS_COMPILE)gcc
OBJCOPY = $(CROSS_COMPILE)objcopy

# in case make does not have this already defined
RM ?= rm -f

LDFLAGS = -Tlinker.ld -fno-builtin -nostdlib -lgcc

RTL ?= ../rtl
SOURCES  = tb_lm32_system.v lm32_config.v
SOURCES += $(RTL)/lm32_adder.v $(RTL)/lm32_addsub.v $(RTL)/lm32_cpu.v
SOURCES += $(RTL)/lm32_dcache.v $(RTL)/lm32_debug.v $(RTL)/lm32_decoder.v
SOURCES += $(RTL)/lm32_dp_ram.v $(RTL)/lm32_icache.v
SOURCES += $(RTL)/lm32_instruction_unit.v $(RTL)/lm32_interrupt.v
SOURCES += $(RTL)/lm32_jtag.v $(RTL)/lm32_load_store_unit.v
SOURCES += $(RTL)/lm32_logic_op.v $(RTL)/lm32_mc_arithmetic.v
SOURCES += $(RTL)/lm32_multiplier.v $(RTL)/lm32_ram.v $(RTL)/lm32_shifter.v
SOURCES += $(RTL)/lm32_itlb.v $(RTL)/lm32_dtlb.v
SOURCES += $(RTL)/lm32_top.v

all: tb_lm32_system

sim_%: %.vh tb_lm32_system
	@vvp tb_lm32_system +prog=$< $(EXTRA_PLUSARGS)

trace_%: %.vh tb_lm32_system
	@vvp tb_lm32_system +trace=trace_$*.txt +prog=$< $(EXTRA_PLUSARGS)

%.elf:
	$(CC) $(LDFLAGS) -o $@ $^

%.vh: %.elf
	$(OBJCOPY) -O verilog $< $@

clean:
	$(RM) tb_lm32_system *.vcd *.elf *.vh trace*.txt

tb_lm32_system: $(SOURCES)
	iverilog -I. -I$(RTL) -o $@ $(SOURCES) $(EXTRA_DEFINES)

unittest:
	$(MAKE) -C unittests check

.PHONY: clean unittest

hello_world.elf: crt.S hello_world.c
pipe1.elf: pipe1.S
