ifeq ($(SIMULATOR), xcelium)
	RUN_SIMULATION	:= run_xcelium_simulation
endif

CLEAN_TARGETS	+= xcelium.d *.history

SV_DEBUG	?= off

XRUN_COMMON_ARGS	+= -64bit
XRUN_COMMON_ARGS	+= -zlib 4
XRUN_COMMON_ARGS	+= -timedetail
XRUN_COMMON_ARGS	+= -status

XMVLOG_ARGS	+= -compile
XMVLOG_ARGS	+= -uvmhome CDNS-$(UVM_VERSION)
XMVLOG_ARGS	+= -plusperf
XMVLOG_ARGS	+= -parseinfo include
XMVLOG_ARGS	+= -l xmvlog.log

XMELAB_ARGS	+= -elaborate
XMELAB_ARGS	+= -uvmhome CDNS-$(UVM_VERSION)
XMELAB_ARGS	+= -uvmnoautocompile
XMELAB_ARGS	+= -nxmbind
XMELAB_ARGS	+= -plusperf
XMELAB_ARGS	+= -newperf
XMELAB_ARGS	+= -mccodegen
XMELAB_ARGS	+= -timescale '1ns/1ps'
XMELAB_ARGS	+= -top worklib.$(TOP_MODULE)
XMELAB_ARGS	+= -warn_multiple_driver
XMELAB_ARGS	+= -l xmelab.log

XMSIM_ARGS	+= -R
XMSIM_ARGS	+= -xmlibdirname ../xcelium.d
XMSIM_ARGS	+= -xceligen on
XMSIM_ARGS	+= -uvmhome CDNS-$(UVM_VERSION)
XMSIM_ARGS	+= +UVM_TESTNAME=$(TEST_NAME)
XMSIM_ARGS	+= +UVM_VERBOSITY=$(VERBOSITY)
XMSIM_ARGS	+= +UVM_TIMEOUT=$(TIMEOUT),NO
XMSIM_ARGS	+= +UVM_MAX_QUIT_COUNT=$(MAX_ERROR_COUNT),NO
XMSIM_ARGS	+= -l xmsim.log

ifeq ($(GUI), indago)
	XMVLOG_ARGS	+= -classlinedebug
	XMELAB_ARGS	+= -xmdebug
	XMELAB_ARGS	+= -lwdgen
	XMSIM_ARGS	+= -mcdump
	XMSIM_ARGS	+= -gui -indago
	XMSIM_ARGS	+= -input @"ida_probe -log"
	XMSIM_ARGS	+= -input @"ida_probe -wave -wave_probe_args=\"-all -depth to_cells\""
endif
ifeq ($(GUI), simvision)
	XMVLOG_ARGS	+= -classlinedebug
	XMELAB_ARGS	+= -xmdebug
	XMSIM_ARGS	+= -gui
	XMSIM_ARGS	+= -mcdump
	XMSIM_ARGS	+= -input @"database -open dump.shm -default;probe -all -depth to_cells"
endif
ifeq ($(GUI), off)
	XMSIM_ARGS	+= -run
endif

ifeq ($(DUMP), ida)
	XMELAB_ARGS	+= -xmdebug
	XMELAB_ARGS	+= -lwdgen
	XMSIM_ARGS	+= -mcdump
	XMSIM_ARGS	+= -input @"ida_probe -log"
	XMSIM_ARGS	+= -input @"ida_probe -wave -wave_probe_args=\"-all -depth to_cells\""
	ifeq ($(SV_DEBUG), on)
		XMVLOG_ARGS	+= -classlinedebug
		XMSIM_ARGS	+= -input @"ida_probe -sv_flow -ignore_sv_files \"tnoc_*_item tvip_*_item tvip_axi_slave_default_sequence tvip_axi_memory tvip_axi_payload_store tue_* *_configuration *_agent *_monitor *_driver *_component_base *_agent_base *_driver_base *_monitor_base cdns_*\""
		XMSIM_ARGS	+= -nowarn LMTMSG
	endif
	ifeq ($(TR_DEBUG), on)
		XMSIM_ARGS	+= -input @"uvm_set -config * recording_detail UVM_FULL"
	endif
endif
ifeq ($(DUMP), shm)
	XMELAB_ARGS	+= -xmdebug
	XMSIM_ARGS	+= -mcdump
	XMSIM_ARGS	+= -input @"database -open dump.shm -default;probe -all -depth to_cells"
	ifeq ($(TR_DEBUG), on)
		XMSIM_ARGS	+= -input @"uvm_set -config * recording_detail UVM_FULL"
	endif
endif

ifeq ($(RANDOM_SEED), auto)
	XMSIM_ARGS	+= -svseed random
else
	XMSIM_ARGS	+= -svseed $(RANDOM_SEED)
endif

XMVLOG_ARGS	+= $(addprefix +define+, $(DEFINES))
XMVLOG_ARGS	+= $(addprefix -f , $(FILE_LISTS))
XMVLOG_ARGS	+= $(SOURCE_FILES)

.PHONY: compile_xcelium_sim run_xcelium_simulation

compile_xcelium_simulation:
	xrun $(XRUN_COMMON_ARGS) $(XMVLOG_ARGS)
	xrun $(XRUN_COMMON_ARGS) $(XMELAB_ARGS)

run_xcelium_simulation:
	xmls -64bit -nolog -snapshot | grep SSS || make compile_xcelium_simulation
	if [ ! -d $(TEST_NAME) ] ; then \
		mkdir $(TEST_NAME); \
	fi
	cd $(TEST_NAME); xrun $(XRUN_COMMON_ARGS) $(XMSIM_ARGS)
