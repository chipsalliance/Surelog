FILE_LISTS		+= $(TBCM_HOME)/compile.f
FILE_LISTS		+= $(TNOC_HOME)/rtl/common/compile.f
FILE_LISTS		+= $(TNOC_HOME)/rtl/router/compile.f
FILE_LISTS		+= $(TUE_HOME)/compile.f
FILE_LISTS		+= $(TNOC_HOME)/env/bfm/compile.f
FILE_LISTS		+= $(TNOC_HOME)/env/common/compile.f
FILE_LISTS		+= $(TNOC_HOME)/env/router/compile.f
FILE_LISTS		+= $(TNOC_HOME)/test/router/compile.f
SOURCE_FILES	+= $(TNOC_HOME)/env/router/top.sv

DEFINES	+= TNOC_ROUTER_ENV_DATA_WIDTH=64
DEFINES	+= TNOC_ROUTER_ENV_VIRTUAL_CHANNELS=1

TOP_MODULE	+= top

IGNORED_TESTS	+= tnoc_router_virtual_channel_test

