
include Makefile.frag

MKLFS               = dramfs_mklfs 128 64
RISCV_GCC           = $(CROSS_COMPILE)gcc
RISCV_GCC_OPTS      = -march=rv64imafd -mabi=lp64 -mcmodel=medany -I $(BP_INCLUDE_DIR)
RISCV_LINK_OPTS     = -T $(BP_LINKER_DIR)/riscv.ld -L$(BP_LIB_DIR) -static -nostartfiles -lperch
RISCV_CPP_LINK_OPTS = -T $(BP_LINKER_DIR)/riscv.ld --sysroot=$(BP_SDK_DIR) -static -lstdc++ -lperch

.PHONY: all

vpath %.c   ./src
vpath %.cpp ./src
vpath %.S   ./src

all: $(foreach x,$(subst -,_,$(BP_TESTS)),$(x).riscv)

%.riscv: %.c
	$(RISCV_GCC) -o $@ $^ $(RISCV_GCC_OPTS) $(RISCV_LINK_OPTS)

%.riscv: %.S
	$(RISCV_GCC) -o $@ $^ $(RISCV_GCC_OPTS) $(RISCV_LINK_OPTS)

%.riscv: %.cpp lfs.cpp
	$(RISCV_GCC) -o $@ $^ $(RISCV_GCC_OPTS) $(RISCV_CPP_LINK_OPTS)

paging.riscv: vm_start.S paging.c
	$(RISCV_GCC) -o $@ $^ $(RISCV_GCC_OPTS) $(RISCV_LINK_OPTS)

mapping.riscv: vm_start.S mapping.c
	$(RISCV_GCC) -o $@ $^ $(RISCV_GCC_OPTS) $(RISCV_LINK_OPTS)

mc_sanity_%.riscv: mc_sanity.c
	$(RISCV_GCC) -DNUM_CORES=$(notdir $*) -o $@ $^ $(RISCV_GCC_OPTS) $(RISCV_LINK_OPTS)

mc_template_%.riscv: mc_template.c
	$(RISCV_GCC) -DNUM_CORES=$(notdir $*) -o $@ $^ $(RISCV_GCC_OPTS) $(RISCV_LINK_OPTS)

mc_rand_walk_%.riscv: mc_rand_walk.c
	$(RISCV_GCC) -DNUM_CORES=$(notdir $*) -o $@ $^ $(RISCV_GCC_OPTS) $(RISCV_LINK_OPTS)

mc_work_share_sort_%.riscv: mc_work_share_sort.c
	$(RISCV_GCC) -DNUM_CORES=$(notdir $*) -o $@ $^ $(RISCV_GCC_OPTS) $(RISCV_LINK_OPTS)

lfs.cpp:
	$(MKLFS) > $@

clean:
	rm -f *.riscv
