all: work
	touch .stamp

clean::
	rm -f .stamp

define template
$(foreach design,$(1),
$(foreach script,verify falsify $(2),
work:: $(design)/work_$(script)/.stamp

$(design)/work_$(script)/.stamp:
	bash run.sh $(design) $(script)

clean::
	rm -rf $(design)/work_$(script)
))
endef

define template_error
$(foreach design,$(1),
$(foreach script,$(2),
work:: $(design)/work_$(script)/.stamp

$(design)/work_$(script)/.stamp:
	bash run.sh $(design) $(script)

clean::
	rm -rf $(design)/work_$(script)
))
endef

$(eval $(call template,alu,gates luts))

# DFF with constant drivers
$(eval $(call template,dff_d0, dff))
$(eval $(call template,dffr, dff))
$(eval $(call template,dffc, dff))
$(eval $(call template,dffcp, dff))
$(eval $(call template,dffsr, dff))

# Tri-state buffers general use
$(eval $(call template,tristate, tristate))
$(eval $(call template,tristate_case, tristate))
$(eval $(call template,tristate_if, tristate))
$(eval $(call template,tristate_proc_asmt, tristate))

# Tri-state buffers with constant
$(eval $(call template,tristate_const_0, tristate))
$(eval $(call template,tristate_const_1, tristate))
$(eval $(call template,tristate_const_data, tristate))

# Demoting I/O port
$(eval $(call template,inout_port, deminout deminout_synth))
$(eval $(call template,inout_port_demote, deminout deminout_synth))

# MACC cells
$(eval $(call template,macc, macc))

#FSM with unreachable state
$(eval $(call template,fsm_unreach, fsm))
# Optimization of FSM when signal connected to input/input and output
$(eval $(call template,fsm, fsm))
$(eval $(call template,fsm_opt, fsm))

#Extract full and half adders
$(eval $(call template,full_adder,full_adder half_adder full_adder_d full_adder_b full_adder_wo_opt))

#Extract reduce
$(eval $(call template,reduce,reduce reduce_allow_off_chain))

#nlutmap
$(eval $(call template,nlutmap,nlutmap))
$(eval $(call template,nlutmap_opt,nlutmap_luts nlutmap_assert))
$(eval $(call template_error,nlutmap_error,nlutmap_error))

#zinit
$(eval $(call template,zinit,zinit zinit_singleton))
$(eval $(call template_error,zinit_error,zinit_failed_to_handle))

#clk2fflogic (104 - 144,180-195 is not reached)
$(eval $(call template,clk2fflogic,clk2fflogic))
$(eval $(call template,clk2fflogic_latch,clk2fflogic))
$(eval $(call template,clk2fflogic_mem,clk2fflogic_mem))

#muxcover
$(eval $(call template,muxcover,muxcover muxcover_nodecode muxcover_mux4 muxcover_mux4_nodecode muxcover_mux16 muxcover_mux16_nodecode muxcover_4_8_16_nodecode muxcover_mux2 muxcover_dmux))
$(eval $(call template,muxcover_mux8,muxcover_mux8 muxcover_mux8_nodecode))

#aigmap
$(eval $(call template,aigmap,aigmap aigmap_nand))

#memory_memx, memory_nordff(75-101 not covered), memory_unpack(91-108 not covered)
$(eval $(call template,memory,memory memory_memx memory_nordff memory_unpack memory_nomap memory_nordff_opt memory_memx_opt memory_bram_opt memory_share))
$(eval $(call template,memory_single_port,memory memory_memx memory_nordff memory_unpack memory_nomap memory_nordff_opt memory_memx_opt memory_bram_opt memory_share))
$(eval $(call template_error,memory_bram_error, memory_bram_syntax_error_in_rules memory_bram_cant_open_rules_file ))

#uniquify
$(eval $(call template,uniquify,uniquify))

#hierarchy (44% increased to 61,3%)
$(eval $(call template,hierarchy,hierarchy hierarchy_top hierarchy_check hierarchy_simcheck hierarchy_purge_lib hierarchy_libdir hierarchy_keep_positionals hierarchy_keep_portwidths hierarchy_nokeep_asserts hierarchy_auto_top hierarchy_generate hierarchy_chparam hierarchy_chparam_overwr))
$(eval $(call template,hierarchy_huge,hierarchy_huge))
$(eval $(call template_error,hierarchy_error, hierarchy_no_top_module hierarchy_top_requires_args hierarchy_module_not_found ))

#attrmap
$(eval $(call template,attrmap,attrmap attrmap_modattr))

#dff2dffe -unmap
# dff2dffe_unmap_direct - skipped: ERROR: Found error in internal cell \dffe.$procdff$47 ($dffe) at
$(eval $(call template,dff2dffe_unmap,dff2dffe_unmap dff2dffe_unmap_mince dff2dffe_unmap_direct))
$(eval $(call template_error,dff2dffe_error,dff2dffe_error))

#dff2dffs
$(eval $(call template,dff2dffs,dff2dffs))

#dffsr2dff
$(eval $(call template,dffsr2dff,dffsr2dff))

#extract
$(eval $(call template,extract,extract_cell_attr extract_compat extract_constports extract_map_design extract_ignore_parameters extract_ignore_param  extract_map extract_mine_cells_span extract_mine_limit_matches_per_module extract_mine_max_fanout extract_mine_min_freq extract_mine_split extract_mine extract_nodefaultswaps extract_perm extract_swap extract_verbose extract_wire_attr ))
$(eval $(call template_error,extract_error, extract_mine_and_map extract_map_and_mine extract_args_to_perm extract_missing_opt extract_cant_open_map_file extract_cant_open_output ))

#extract_counter
$(eval $(call template,extract_counter,extract_counter extract_counter_maxwidth extract_counter_pout))
$(eval $(call template,extract_counter_down,extract_counter extract_counter_maxwidth extract_counter_pout))
$(eval $(call template_error,extract_counter_error,extract_counter_pout_without_args))

#shregmap
$(eval $(call template,shregmap,shregmap shregmap_clkpol_any shregmap_clkpol_neg shregmap_clkpol_pos shregmap_enpol_any shregmap_enpol_any_or_none shregmap_enpol_neg shregmap_enpol_none shregmap_enpol_pos shregmap_init shregmap_keep_after shregmap_keep_before shregmap_match shregmap_maxlen shregmap_minlen shregmap_params shregmap_tech shregmap_zinit))
$(eval $(call template,shregmap_resetable,shregmap shregmap_clkpol_any shregmap_clkpol_neg shregmap_clkpol_pos shregmap_enpol_any shregmap_enpol_any_or_none shregmap_enpol_neg shregmap_enpol_none shregmap_enpol_pos shregmap_init shregmap_keep_after shregmap_keep_before shregmap_match shregmap_maxlen shregmap_minlen shregmap_params shregmap_tech shregmap_zinit))
$(eval $(call template_error,shregmap_error,shregmap_zinit_init shregmap_match_clkpol shregmap_match_enpol shregmap_match_params))

#design_import
$(eval $(call template,design_import, design_import design_import_as ))

#async2sync
$(eval $(call template,async2sync,async2sync))

#flowmap
$(eval $(call template,flowmap,flowmap flowmap_cells flowmap_debug_relax flowmap_debug flowmap_maxlut flowmap_minlut flowmap_optarea flowmap_r_alpha flowmap_r_beta flowmap_r_gamma flowmap_relax flowmap_relax_debug flowmap_relax_debug_relax flowmap_top))
$(eval $(call template,flowmap_latch,flowmap flowmap_cells flowmap_debug_relax flowmap_debug flowmap_maxlut flowmap_minlut flowmap_optarea flowmap_r_alpha flowmap_r_beta flowmap_r_gamma flowmap_relax  flowmap_relax_debug flowmap_relax_debug_relax flowmap_top))
$(eval $(call template,flowmap_mem,flowmap flowmap_cells flowmap_debug_relax flowmap_debug flowmap_maxlut flowmap_minlut flowmap_optarea flowmap_r_alpha flowmap_r_beta flowmap_r_gamma flowmap_relax flowmap_relax_debug flowmap_relax_debug_relax flowmap_top))

#iopadmap
$(eval $(call template,iopadmap,iopadmap iopadmap_dont_map))

#tribuf
$(eval $(call template,tribuf,tribuf tribuf_top tribuf_merge_top))
$(eval $(call template,tribuf_logic,tribuf_logic_top tribuf_merge_logic_top))

#expose
$(eval $(call template,expose,expose_cut expose_input expose_evert expose_sep expose_shared expose_dff expose_evert_dff expose_evert_shared expose_evert_dff_shared))
$(eval $(call template,expose_dff,expose_cut expose_input expose_evert expose_sep expose_shared expose_dff expose_evert_dff expose_evert_shared expose_evert_dff_shared))
$(eval $(call template,expose_ffs,expose_cut expose_input expose_evert expose_sep expose_shared expose_dff expose_evert_shared expose_evert_dff_shared))

#opt_demorgan
$(eval $(call template,opt_demorgan,opt_demorgan))
$(eval $(call template,opt_demorgan_reduce,opt_demorgan))

#fsm_expand
$(eval $(call template,fsm_expand, fsm_expand fsm_expand_full))

#fsm_export
$(eval $(call template,fsm_export, fsm_export fsm_export_noauto fsm_export_o fsm_export_origenc))
$(eval $(call template_error,fsm_export_error, fsm_export_couldnt_open_file))

#fsm_recode
$(eval $(call template,fsm_recode, fsm_recode fsm_recode_encoding_binary fsm_recode_encoding_binary_twice fsm_recode_encoding_one_hot fsm_recode_fm_set_fsm_file fsm_recode_all_opt))
$(eval $(call template_error,fsm_recode_error, fsm_recode_encoding_isnt_supported fsm_recode_cant_open_fm_set_fsm_file fsm_recode_cant_open_encfile ))

#fsm command
$(eval $(call template,fsm_command, fsm_command fsm_fm_set_fsm_file fsm_encfile fsm_encoding_binary fsm_encoding_one-hot fsm_encoding_auto fsm_encoding_none fsm_encoding_user fsm_encoding_unknown fsm_nodetect fsm_norecode fsm_nomap fsm_command_expand fsm_fullexpand fsm_command_export ))

#share
$(eval $(call template,share, share share_force share_aggressive share_fast share_limit))
$(eval $(call template,share_shr, share share_force share_aggressive share_fast share_limit))
$(eval $(call template,share_macc, share_force_macc share_aggressive_macc share_fast_macc share_limit_macc share_macc))
#+ yosys -ql yosys.log ../../scripts/share_force.ys
#ERROR: Abort in passes/opt/share.cc:724.
#make: *** [Makefile:152: share_fsm/work_share_force/.stamp] Error 1
$(eval $(call template,share_fsm, share share_force share_aggressive share_fast share_limit))

#opt_expr
$(eval $(call template,opt_expr, opt_expr))

#ice40_dsp
$(eval $(call template,ice40_dsp_mult, ice40_dsp))
$(eval $(call template,ice40_dsp_mult_b_larger, ice40_dsp))
$(eval $(call template,ice40_dsp_mult_a_larger, ice40_dsp))
$(eval $(call template,ice40_dsp_mult_out_larger, ice40_dsp))
$(eval $(call template,ice40_dsp_mult_acc, ice40_dsp))
$(eval $(call template,ice40_dsp_mult_signed, ice40_dsp))

#opt_lut
$(eval $(call template,opt_lut, opt_lut opt_lut_limit opt_lut_dlogic opt_lut_limit_0))
$(eval $(call template,opt_lut_ice40, opt_lut opt_lut_limit opt_lut_dlogic opt_lut_limit_0))

#wreduce -memx
$(eval $(call template,wreduce_memx, wreduce wreduce_memx wreduce_keepdc wreduce_memx_keepdc))
$(eval $(call template,wreduce_reduce, wreduce wreduce_memx wreduce_keepdc wreduce_memx_keepdc))
$(eval $(call template,wreduce_adder, wreduce wreduce_memx wreduce_keepdc wreduce_memx_keepdc))
$(eval $(call template,wreduce_mul, wreduce wreduce_memx wreduce_keepdc wreduce_memx_keepdc))
$(eval $(call template,wreduce_div, wreduce wreduce_memx wreduce_keepdc wreduce_memx_keepdc))

#opt_merge -share_all
$(eval $(call template,opt_merge_share_all, opt_merge_share_all))
$(eval $(call template,opt_merge_reduce, opt_merge_share_all))

#opt
$(eval $(call template,opt, opt opt_mux_bool opt_clkinv opt_share_all opt_purge opt_keepdc))

#proc_arst
$(eval $(call template,proc_arst, proc_arst proc_arst_global_rst))
$(eval $(call template,proc_arst_reduce, proc_arst proc_arst_global_rst  proc_arst_global_rst_a))

#submod
$(eval $(call template, submod, submod submod_top submod_copy submod_name submod_no_proc submod_no_hier))
$(eval $(call template, submod_mem, submod submod_top submod_copy submod_name submod_no_proc submod_no_hier submod_mem))
$(eval $(call template_error, submod_error, submod_error))

#prep
$(eval $(call template, prep, prep prep_top prep_auto_top prep_flatten prep_ifx prep_memx prep_nomem prep_nordff prep_rdff prep_nokeepdc prep_run prep_run_begin))
$(eval $(call template_error, prep_error, prep_error))

#synth
$(eval $(call template, synth, synth synth_top synth_auto_top synth_encfile synth_run synth_run_full synth_flatten synth_lut synth_nofsm synth_noabc synth_noabc_lut synth_noalumacc synth_nordff synth_noshare synth_abc9))
$(eval $(call template_error, synth_error, synth_error synth_abc9_no_lut))

#simplemap
$(eval $(call template, simplemap, simplemap simplemap_top simplemap_slice_concat))
$(eval $(call template, simplemap_reduce, simplemap simplemap_top simplemap_slice_concat))
$(eval $(call template, simplemap_mem_slice_concat, simplemap simplemap_top simplemap_slice_concat))

#techmap
$(eval $(call template, techmap, techmap techmap_wb techmap_autoproc techmap_recursive techmap_extern techmap_assert techmap_i techmap_d techmap_max_iter techmap_map))

#test_pmgen
$(eval $(call template, test_pmgen, test_pmgen_eqpmux test_pmgen_generate_eqpmux test_pmgen_generate_ice40_dsp test_pmgen_generate_peepopt_muldiv test_pmgen_generate_peepopt_shiftmul test_pmgen_generate_reduce test_pmgen_generate_xilinx_srl_fixed test_pmgen_generate_xilinx_srl_variable test_pmgen_reduce_chain test_pmgen_reduce_tree))

.PHONY: all clean
