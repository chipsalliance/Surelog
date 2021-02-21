#Coremark makefile for BP

RISCV_GCC = $(CROSS_COMPILE)gcc -mabi=lp64 -march=rv64ima -mcmodel=medany -fno-builtin-printf

RISCV_GCC += -funswitch-loops -flto
RISCV_GCC += -mtune=bsg_blackparrot
RISCV_GCC += -O2 -fno-common -funroll-loops -finline-functions --param max-inline-insns-auto=20 -falign-functions=4 -falign-jumps=4 -falign-loops=4
RISCV_LINK = -static -nostdlib -nostartfiles -lm -lgcc -T test.ld -L../

RISCV_TESTS_DIR = ../../riscv-tests/benchmarks

COMMON_FILES = -I$(RISCV_TESTS_DIR)/../env -I$(RISCV_TESTS_DIR)/common -I../ -I./
COMMON_FILES += $(RISCV_TESTS_DIR)/common/crt.S $(RISCV_TESTS_DIR)/common/syscalls.c

#Number of iterations coremark runs for
ITER_NUM = 5
#indicates whether or not BP has float support
BP_HAS_FLOAT = 0

.PHONY: riscv

riscv:
	$(RISCV_GCC) $(COMMON_FILES) -o coremark.riscv $(wildcard *.c) $(wildcard ../*.c) -DITERATIONS=$(ITER_NUM) \
	-DHAS_FLOAT=$(BP_HAS_FLOAT) $(RISCV_LINK)

coremark.s:
	$(RISCV_GCC) $(COMMON_FILES) -dp -S $(wildcard *.c) $(wildcard ../*.c) -DITERATIONS=$(ITER_NUM) \
	-DHAS_FLOAT=$(BP_HAS_FLOAT) $(RISCV_LINK)

clean:
	rm -f *.riscv
