all: work
	touch .stamp

clean::
	rm -f .stamp

define template
work:: $(addprefix $(1)/.stamp_,sim falsify $(2))

$(1)/.stamp_sim:
	bash run.sh $(1) sim
	touch $$@

$(1)/.stamp_falsify: $(1)/.stamp_sim
	bash run.sh $(1) falsify
	touch $$@

$(1)/.stamp_%: $(1)/.stamp_sim
	bash run.sh $(1) $$*
	touch $$@

clean::
	rm -rf $(1)/.stamp_* $(1)/work_*
	rm -f $(1)_{cmos,ice40,falsify,ecp5,xilinx}{,_abc9}.status
endef

$(eval $(call template,navre,cmos ice40 ice40_abc9 ecp5 ecp5_abc9 xilinx xilinx_abc9))
ifeq ($(ENABLE_HEAVY_TESTS),1)
$(eval $(call template,picorv32,cmos ice40 ice40_abc9 ecp5 ecp5_abc9 xilinx xilinx_abc9))
endif
.PHONY: all clean
