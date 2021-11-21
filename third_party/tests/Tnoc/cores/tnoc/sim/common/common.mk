FILE_LISTS		=
SOURCE_FILES	=
DEFINES				=
TEST_LIST			=

DUMP						?= off
GUI							?= off
TR_DEBUG				?= off
RANDOM_SEED			?= auto
UVM_VERSION			?= 1.2
VERBOSITY				?= UVM_LOW
TIMEOUT					?= 1_000_000
MAX_ERROR_COUNT	?= 1
SIMULATOR				?= vcs

TNOC_HOME					?= $(shell git rev-parse --show-toplevel)
TBCM_HOME					?= $(TNOC_HOME)/rtl/bcm
TUE_HOME					?= $(TNOC_HOME)/env/tue
TVIP_COMMON_HOME	?= $(TNOC_HOME)/env/vip_common
TVIP_AXI_HOME			?= $(TNOC_HOME)/env/axi_vip

export TNOC_HOME
export TBCM_HOME
export TUE_HOME
export TVIP_COMMON_HOME
export TVIP_AXI_HOME

-include local.mk
-include test_list.mk

ifdef IGNORED_TESTS
	FILTERED_TEST_LIST	= $(filter-out $(IGNORED_TESTS),$(TEST_LIST))
else
	FILTERED_TEST_LIST	= $(TEST_LIST)
endif

.PHONY: all $(FILTERED_TEST_LIST) clean clean_all

all: $(FILTERED_TEST_LIST)

$(FILTERED_TEST_LIST):
	make $(RUN_SIMULATION) TEST_NAME=$@

CLEAN_TARGETS	+= *.log *.h
clean:
	rm -rf $(CLEAN_TARGETS)

clean_all:
	make clean
	rm -rf $(FILTERED_TEST_LIST)

include $(TNOC_HOME)/sim/common/vcs.mk
include $(TNOC_HOME)/sim/common/xcelium.mk
