all: work
	touch .stamp

clean::
	rm -f .stamp

define template
$(foreach design,$(1),
$(foreach script,$(2),
work:: $(design)/work_$(script)/.stamp

$(design)/work_$(script)/.stamp:
	./run.sh $(design) $(script)

clean::
	rm -rf $(design)/work_$(script)
))
endef

#yosys
$(eval $(call template,yosys,yosys))

#yosys_help
$(eval $(call template,yosys_help,yosys))

#yosys_no_banner
$(eval $(call template,yosys_no_banner,yosys))

#yosys_no_footer
$(eval $(call template,yosys_no_footer,yosys))

#yosys_quiet
$(eval $(call template,yosys_quiet,yosys))

#yosys_headers
$(eval $(call template,yosys_headers,yosys))

#yosys_time
$(eval $(call template,yosys_time,yosys))

#yosys_detailed_timing
$(eval $(call template,yosys_detailed_timing,yosys))

#yosys_log_file
$(eval $(call template,yosys_log_file,yosys))

#yosys_log_file_lb_mode
$(eval $(call template,yosys_log_file_lb_mode,yosys))

#yosys_write_des_to_file
$(eval $(call template,yosys_write_des_to_file,yosys))

#yosys_backends
$(eval $(call template,yosys_backends,yosys))

#yosys_frontends
$(eval $(call template,yosys_frontends,yosys))

#yosys_command_list
$(eval $(call template,yosys_command_list,yosys))

#yosys_help_for_command
$(eval $(call template,yosys_help_for_command,yosys))

#yosys_script
$(eval $(call template,yosys_script,yosys))

#yosys_tcl_script
$(eval $(call template,yosys_tcl_script,yosys))

#yosys_exec_command
$(eval $(call template,yosys_exec_command,yosys))

#yosys_enable_tracing
$(eval $(call template,yosys_enable_tracing,yosys))

#yosys_randomize_alloc_point_addr
$(eval $(call template,yosys_randomize_alloc_point_addr,yosys))

#yosys_abort
$(eval $(call template,yosys_abort,yosys))

#yosys_macro
$(eval $(call template,yosys_macro,yosys))

#yosys_header
$(eval $(call template,yosys_header,yosys))

#yosys_regexp
$(eval $(call template,yosys_regexp,yosys))

#yosys_regexp_w
$(eval $(call template,yosys_regexp_w,yosys))

#yosys_regexp_e
$(eval $(call template,yosys_regexp_e,yosys))

#yosys_dependencies
$(eval $(call template,yosys_dependencies,yosys))

#yosys_globally_en_log_mes
$(eval $(call template,yosys_globally_en_log_mes,yosys))

#yosys_version
$(eval $(call template,yosys_version,yosys))

#yosys_synth
$(eval $(call template,yosys_synth,yosys))


.PHONY: all clean
