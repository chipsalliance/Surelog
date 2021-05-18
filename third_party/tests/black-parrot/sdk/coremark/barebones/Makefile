
RISCV_GCC       = $(CROSS_COMPILE)gcc
RISCV_GCC_OPTS  = -mabi=lp64 -march=rv64imafd -mcmodel=medany -I../ -I./ -I$(BP_INCLUDE_DIR)
RISCV_GCC_OPTS += -funswitch-loops -flto
RISCV_GCC_OPTS += -mtune=bsg_blackparrot
RISCV_GCC_OPTS += -O2 -fno-common -funroll-loops -finline-functions --param max-inline-insns-auto=20 -falign-functions=4 -falign-jumps=4 -falign-loops=4
RISCV_LINK_OPTS = -T $(BP_LINKER_DIR)/riscv.ld -L$(BP_LIB_DIR) -static -nostartfiles -lperch

#Number of iterations coremark runs for
ITER_NUM = 5
#indicates whether or not BP has float support
BP_HAS_FLOAT = 1

.PHONY: all

all: coremark.riscv

coremark.riscv:
	$(RISCV_GCC) -o $@ $(wildcard *.c) $(wildcard ../*.c) -DITERATIONS=$(ITER_NUM) \
	-DHAS_FLOAT=$(BP_HAS_FLOAT) $(RISCV_GCC_OPTS) $(RISCV_LINK_OPTS)

clean:
	rm -f *.riscv
