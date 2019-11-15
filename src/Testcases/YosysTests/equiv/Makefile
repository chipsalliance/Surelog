all: work
	touch .stamp

clean::
	rm -f .stamp

define template
$(foreach design,$(1),
$(foreach script,$(2),
work:: $(design)/work_$(script)/.stamp

$(design)/work_$(script)/.stamp:
	bash run.sh $(design) $(script)

clean::
	rm -rf $(design)/work_$(script)
))
endef

#equiv_make
$(eval $(call template,equiv_make,equiv_make equiv_make_inames equiv_make_blacklist equiv_make_encfile))
$(eval $(call template,equiv_make_fsm,equiv_make_encfile equiv_make_encfile_fsm))
$(eval $(call template,equiv_make_error,equiv_make_synth_error equiv_make_cant_open_encfile equiv_make_cant_open_blacklist equiv_make_cant_find_gate_mod equiv_make_cant_find_gold_mod equiv_make_invalid_num_of_args equiv_make_cant_match equiv_make_cant_match_gold_to_gate equiv_make_equiv_mod_already_exists equiv_make_gold_mod_contains_proc equiv_make_gate_mod_contains_proc))
$(eval $(call template,equiv_make_fsm_error,equiv_make_redefenition_of_signal))

#equiv_simple
$(eval $(call template,equiv_simple,equiv_simple equiv_simple_v equiv_simple_undef equiv_simple_short equiv_simple_seq equiv_simple_nogroup))
$(eval $(call template,equiv_simple_fsm,equiv_simple equiv_simple_v equiv_simple_undef equiv_simple_short equiv_simple_seq equiv_simple_nogroup))

#equiv_status
$(eval $(call template,equiv_status,equiv_status))
$(eval $(call template,equiv_status_error,equiv_status_assert))

#equiv_struct
$(eval $(call template,equiv_struct,equiv_struct equiv_struct_fwd equiv_struct_fwonly equiv_struct_icells equiv_struct_maxiter))

#equiv_remove
$(eval $(call template,equiv_remove,equiv_remove equiv_remove_gold equiv_remove_gate ))
$(eval $(call template,equiv_remove_error,equiv_remove_gold_gate ))

#equiv_purge
$(eval $(call template,equiv_purge,equiv_purge ))

#equiv_miter
#equiv_miter_invalid_num_of_args - no error
$(eval $(call template,equiv_miter,equiv_miter equiv_miter_trigger equiv_miter_cmp equiv_miter_assert equiv_miter_undef))
$(eval $(call template,equiv_miter_error,equiv_miter_miter_module_already_exists equiv_miter_one_module_must_be_selected))

#equiv_mark
$(eval $(call template,equiv_mark,equiv_mark ))

#equiv_induct
$(eval $(call template,equiv_induct,equiv_induct equiv_induct_undef equiv_induct_seq ))

#equiv_add
$(eval $(call template,equiv_add,equiv_add equiv_add_try ))
# ERROR: This command must be executed in module context!
#equiv_add_cant_find_gold_cell equiv_add_cant_find_gate_cell equiv_add_invalid_number_of_args
$(eval $(call template,equiv_add_error,equiv_add_module_context ))

#equiv_opt
$(eval $(call template,equiv_opt,equiv_opt equiv_opt_run equiv_opt_map equiv_opt_undef))
$(eval $(call template,equiv_opt_error,equiv_opt_unknown_option equiv_opt_no_opt equiv_opt_fully_selected_des))

.PHONY: all clean
