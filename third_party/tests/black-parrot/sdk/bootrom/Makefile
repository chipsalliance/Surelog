
RISCV_GCC ?= $(CROSS_COMPILE)gcc
RISCV_OBJCOPY ?= $(CROSS_COMPILE)objcopy

.PHONY: clean

RISCV_CFLAGS ?= -march=rv64im -mabi=lp64 -mcmodel=medany -static -nostdlib -nostartfiles
bootrom.riscv: cce_ucode.o
	$(RISCV_GCC) $(RISCV_CFLAGS) bootrom.S $^ -I$(@D) -o $@ -Tlink.ld -static -Wl,--no-gc-sections

# Currently only one bootrom is generated at a time
COH_PROTO ?= mesi
cce_ucode.o:
	$(RISCV_OBJCOPY) -I binary -O elf64-littleriscv -B riscv $(BP_UCODE_DIR)/$(COH_PROTO).bin $@ --strip-all --add-symbol cce_ucode_bin=.data:0

clean:
	@rm -f bootrom.riscv

