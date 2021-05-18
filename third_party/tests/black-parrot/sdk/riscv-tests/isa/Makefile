#=======================================================================
# Makefile for riscv-tests/isa
#-----------------------------------------------------------------------

XLEN ?= 64

src_dir := .

ifeq ($(XLEN),64)
include $(src_dir)/rv64ui/Makefrag
include $(src_dir)/rv64uc/Makefrag
include $(src_dir)/rv64um/Makefrag
include $(src_dir)/rv64ua/Makefrag
include $(src_dir)/rv64uf/Makefrag
include $(src_dir)/rv64ud/Makefrag
include $(src_dir)/rv64si/Makefrag
include $(src_dir)/rv64mi/Makefrag
endif
include $(src_dir)/rv32ui/Makefrag
include $(src_dir)/rv32uc/Makefrag
include $(src_dir)/rv32um/Makefrag
include $(src_dir)/rv32ua/Makefrag
include $(src_dir)/rv32uf/Makefrag
include $(src_dir)/rv32ud/Makefrag
include $(src_dir)/rv32si/Makefrag
include $(src_dir)/rv32mi/Makefrag

default: all

#--------------------------------------------------------------------
# Build rules
#--------------------------------------------------------------------

RISCV_PREFIX ?= riscv$(XLEN)-unknown-elf-
RISCV_GCC ?= $(RISCV_PREFIX)gcc
RISCV_GCC_OPTS ?= -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles
RISCV_OBJDUMP ?= $(RISCV_PREFIX)objdump --disassemble-all --disassemble-zeroes --section=.text --section=.text.startup --section=.text.init --section=.data
RISCV_SIM ?= spike

vpath %.S $(src_dir)

#------------------------------------------------------------
# Build assembly tests

%.dump: %
	$(RISCV_OBJDUMP) $< > $@

%.out: %
	$(RISCV_SIM) --isa=rv64gc $< 2> $@

%.out32: %
	$(RISCV_SIM) --isa=rv32gc $< 2> $@

define compile_template

$$($(1)_p_tests): $(1)-p-%: $(1)/%.S
	$$(RISCV_GCC) $(2) $$(RISCV_GCC_OPTS) -I$(src_dir)/../env/p -I$(src_dir)/macros/scalar -T$(src_dir)/../env/p/link.ld $(BP_SDK_DIR)/perch/atomics.S $(BP_SDK_DIR)/perch/muldiv.S  $(BP_SDK_DIR)/perch/exception.S $(BP_SDK_DIR)/perch/emulation.c  $$< -o $$@.riscv
$(1)_tests += $$($(1)_p_tests)

$$($(1)_pt_tests): $(1)-pt-%: $(1)/%.S
	$$(RISCV_GCC) $(2) $$(RISCV_GCC_OPTS) -I$(src_dir)/../env/pt -I$(src_dir)/macros/scalar -T$(src_dir)/../env/pt/link.ld $(BP_SDK_DIR)/perch/atomics.S $(BP_SDK_DIR)/perch/muldiv.S $(BP_SDK_DIR)/perch/exception.S $(BP_SDK_DIR)/perch/emulation.c  $$< -o $$@.riscv
$(1)_tests += $$($(1)_pt_tests)

$$($(1)_v_tests): $(1)-v-%: $(1)/%.S
	$$(RISCV_GCC) $(2) $$(RISCV_GCC_OPTS) -DENTROPY=0x$$(shell echo \$$@ | md5sum | cut -c 1-7) -std=gnu99 -O2 -I$(src_dir)/../env/v -I$(src_dir)/macros/scalar -T$(src_dir)/../env/v/link.ld $(src_dir)/../env/v/entry.S $(src_dir)/../env/v/*.c $$< -o $$@.riscv
$(1)_tests += $$($(1)_v_tests)

$$($(1)_vt_tests): $(1)-vt-%: $(1)/%.S
	$$(RISCV_GCC) $(2) $$(RISCV_GCC_OPTS) -DENTROPY=0x$$(shell echo \$$@ | md5sum | cut -c 1-7) -std=gnu99 -O2 -I$(src_dir)/../env/v -I$(src_dir)/macros/scalar -T$(src_dir)/../env/v/link.ld $(src_dir)/../env/vt/entry.S $(src_dir)/../env/v/*.c $$< -o $$@.riscv
$(1)_tests += $$($(1)_vt_tests)

.PHONY: $(1)

tests += $$($(1)_tests)

endef

#$(eval $(call compile_template,rv32ui,-march=rv32g -mabi=ilp32))
#$(eval $(call compile_template,rv32uc,-march=rv32g -mabi=ilp32))
#$(eval $(call compile_template,rv32um,-march=rv32g -mabi=ilp32))
#$(eval $(call compile_template,rv32ua,-march=rv32g -mabi=ilp32))
#$(eval $(call compile_template,rv32uf,-march=rv32g -mabi=ilp32))
#$(eval $(call compile_template,rv32ud,-march=rv32g -mabi=ilp32))
#$(eval $(call compile_template,rv32si,-march=rv32g -mabi=ilp32))
#$(eval $(call compile_template,rv32mi,-march=rv32g -mabi=ilp32))
ifeq ($(XLEN),64)
$(eval $(call compile_template,rv64ui,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64uc,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64um,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64ua,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64uf,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64ud,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64si,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64mi,-march=rv64g -mabi=lp64))
endif

#------------------------------------------------------------
# Default

all: $(tests)

#------------------------------------------------------------
# Clean up

clean:
	rm -rf $(junk)
