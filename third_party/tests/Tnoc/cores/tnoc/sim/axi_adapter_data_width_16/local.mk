FILE_LISTS		+= $(TBCM_HOME)/compile.f
FILE_LISTS		+= $(TNOC_HOME)/rtl/common/compile.f
FILE_LISTS		+= $(TNOC_HOME)/rtl/axi_adapter/compile.f
FILE_LISTS		+= $(TNOC_HOME)/rtl/router/compile.f
FILE_LISTS		+= $(TNOC_HOME)/rtl/fabric/compile.f
FILE_LISTS		+= $(TUE_HOME)/compile.f
FILE_LISTS		+= $(TNOC_HOME)/env/bfm/compile.f
FILE_LISTS		+= $(TVIP_COMMON_HOME)/compile.f
FILE_LISTS		+= $(TVIP_AXI_HOME)/compile.f
FILE_LISTS		+= $(TNOC_HOME)/env/common/compile.f
FILE_LISTS		+= $(TNOC_HOME)/env/fabric/compile.f
FILE_LISTS		+= $(TNOC_HOME)/env/axi_adapter/compile.f
FILE_LISTS		+= $(TNOC_HOME)/test/axi_adapter/compile.f
SOURCE_FILES	+= $(TNOC_HOME)/env/axi_adapter/top.sv

DEFINES	+= TNOC_AXI_ADAPTER_ENV_DATA_WIDTH=16

TOP_MODULE	+= top

