export BP_SDK_DIR ?= $(shell git rev-parse --show-toplevel)

.PHONY: sdk prog bsg_cadenv bleach_all
.DEFAULT: sdk

include $(BP_SDK_DIR)/Makefile.common
include $(BP_SDK_DIR)/Makefile.tools
include $(BP_SDK_DIR)/Makefile.prog

## This is the list of target directories that tools and libraries will be installed into
override TARGET_DIRS := $(BP_SDK_BIN_DIR) $(BP_SDK_LIB_DIR) $(BP_SDK_INCLUDE_DIR) $(BP_SDK_TOUCH_DIR)
$(TARGET_DIRS):
	mkdir -p $@

# Makes clones much faster. Comment out if you see "fatal: reference is not a tree"
SHALLOW_SUB ?= --depth=1

sdk_lite: | $(TARGET_DIRS)
	cd $(BP_SDK_DIR); git submodule update --init --checkout $(SHALLOW_SUB)
	$(MAKE) dromajo

## This target makes the sdk tools
sdk: sdk_lite
	$(MAKE) gnu
	$(MAKE) -j1 bedrock
	$(MAKE) -j1 perch
	$(MAKE) -j1 bootrom
	$(MAKE) -j1 bp-demos
	$(MAKE) -j1 bp-tests

prog: sdk
	$(MAKE) riscv-tests
	$(MAKE) coremark
	$(MAKE) beebs
	# Requires access to spec2000
	#$(MAKE) spec2000
	# Requires access to Synopsys VCS
	#$(MAKE) riscv-dv
	# Requires patience
	#$(MAKE) linux

tidy:
	git submodule deinit -f dromajo riscv-gnu-toolchain
	git submodule deinit -f riscv-tests coremark beebs spec2000 riscv-dv linux

bsg_cadenv:
	-cd $(BP_SDK_DIR); git clone git@github.com:bespoke-silicon-group/bsg_cadenv.git bsg_cadenv

## This target just wipes the whole repo clean.
#  Use with caution.
bleach_all:
	cd $(BP_SDK_DIR); git clean -fdx; git submodule deinit -f .

