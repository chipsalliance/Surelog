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

#test_abcloop
$(eval $(call template,test_abcloop,test_abcloop test_abcloop_n test_abcloop_s ))

#test_cell
#test_cell_map - takes a lot of time
# test_cell_mux, test_cell_pmux - is not supported
$(eval $(call template,test_cell,test_cell test_cell_aigmap test_cell_const test_cell_edges test_cell_f  test_cell_div test_cell_muxdiv test_cell_n test_cell_noeval test_cell_nosat test_cell_s test_cell_script test_cell_simlib test_cell_v test_cell_vlog test_cell_w test_cell_alu test_cell_sop test_cell_lut test_cell_macc test_cell_lcu test_cell_fa test_cell_wo_synth test_cell_map))
$(eval $(call template,test_cell_error, test_cell_failed_to_open test_cell_unexpected_opt test_cell_cell_type_not_supported test_cell_no_cell_t_specified test_cell_dont_spec_cell_type_with_f ))

#torder
$(eval $(call template,torder,torder torder_stop torder_noautostop ))

#trace
$(eval $(call template,trace,trace ))
$(eval $(call template,trace_mem,trace_mem ))

#write_file
$(eval $(call template,write_file,write_file write_file_a ))
$(eval $(call template,write_file_error,write_file_missing_name write_file_a_missing_name ))

#stat
$(eval $(call template,stat, stat stat_top stat_width stat_liberty stat_tech_xilinx ))
$(eval $(call template,stat_error, stat_unsupported_tech stat_cant_find_module stat_cant_open_lib_file ))

#show
# show_pause - skipped
$(eval $(call template,show, show show_colorattr show_colors show_color show_enum show_format show_label show_lib show_long show_notitle show_prefix show_signed show_stretch show_viewer show_width))
$(eval $(call template,show_error, show_only_one_module show_cant_open_dot_file show_cant_open_lib_file show_nothing_there_to_show))
#scc
$(eval $(call template,scc, scc scc_all_cell_types scc_expect scc_max_depth scc_nofeedback scc_select scc_set_attr ))
$(eval $(call template,scc_feedback, scc scc_all_cell_types scc_expect1 scc_max_depth scc_nofeedback scc_select scc_set_attr ))
$(eval $(call template,scc_hier_feedback, scc scc_all_cell_types scc_expect scc_max_depth scc_nofeedback scc_select scc_set_attr ))
$(eval $(call template,scc_error, scc_expect1 ))


#scatter
$(eval $(call template,scatter, scatter ))

#rename
$(eval $(call template,rename, rename rename_top rename_src rename_hide rename_enumerate rename_enumerate_pat rename_wire rename_top_top rename_low))
$(eval $(call template,rename_error, rename_obj_not_found rename_no_top_module rename_invalid_number_of_args rename_invalid_number_of_args_top rename_mode_out_requires))

#qwp
#qwp_v - exception (issue #923)
#+ yosys -ql yosys.log ../../scripts/qwp_v.ys
#run.sh: line 11: 28262 Floating point exception(core dumped) yosys -ql yosys.log ../../scripts/$2.ys
$(eval $(call template,qwp, qwp qwp_v qwp_ltr qwp_grid qwp_dump qwp_alpha))

#ltp
$(eval $(call template,ltp, ltp ltp_noff ))

#edgetypes
$(eval $(call template,edgetypes, edgetypes ))

#delete
$(eval $(call template,delete, delete delete_input delete_output delete_port delete_cell delete_wire delete_proc ))
$(eval $(call template,delete_mem, delete_mem ))

#cover
$(eval $(call template,cover, cover cover_q cover_o cover_dir cover_a ))
$(eval $(call template,cover_error, cover_cant_create_file ))

#insbuf
$(eval $(call template,insbuf,insbuf insbuf_cell))

#add
$(eval $(call template,add, add add_wire add_input add_output add_inout add_global_input ))
$(eval $(call template,add_error, add_error ))

#blackbox
$(eval $(call template,blackbox, blackbox ))
$(eval $(call template,blackbox_mem, blackbox blackbox_top))

# - issue #925
#bugpoint ERROR: No such command: autoidx (type 'help' for a command overview)
$(eval $(call template,bugpoint,bugpoint_yosys bugpoint_script bugpoint_grep bugpoint_fast bugpoint_clean bugpoint_modules bugpoint_ports bugpoint_cells bugpoint_connections  ))
$(eval $(call template,bugpoint_error, bugpoint_missing_script bugpoint_do_not_crash bugpoint_fully_selected_des))
#bugpoint_grep_string_not_found - no error

#chformal
$(eval $(call template,chformal, chformal chformal_ff chformal_assert2assume chformal_assert chformal_assume2assert chformal_assume chformal_cover chformal_delay chformal_early chformal_proc_early chformal_fair2live_assert2assume chformal_fair2live chformal_fair chformal_live2fair chformal_live chformal_skip ))
$(eval $(call template,chformal_dff, chformal chformal_ff chformal_assert2assume chformal_assert chformal_assume2assert chformal_assume chformal_cover chformal_delay chformal_early chformal_proc_early chformal_fair2live_assert2assume chformal_fair2live chformal_fair chformal_live2fair chformal_live chformal_skip ))
$(eval $(call template,chformal_ff, chformal chformal_ff chformal_assert2assume chformal_assert chformal_assume2assert chformal_assume chformal_cover chformal_delay chformal_early chformal_proc_early chformal_fair2live_assert2assume chformal_fair2live chformal_fair chformal_live2fair chformal_live chformal_skip ))
$(eval $(call template,chformal_error, chformal_error ))

#chtype
$(eval $(call template,chtype, chtype chtype_map chtype_selection chtype_set))

#connect
$(eval $(call template,connect, connect_nomap_set connect_nomap_unset connect_nounset_set connect_set connect_unset connect_port connect_nomap_port))
$(eval $(call template,connect_error, connect_multiple_modules connect_found_process connect_no_modules connect_set_with_unset connect_set_with_port connect_set_with_unset_and_port connect_cannot_parse_set_lhs_expr connect_cannot_parse_set_rhs_expr connect_unset_with_nounset connect_unset_with_port connect_unset_with_nounset_and_port connect_failed_parse_unset connect_port_with_nounset connect_cant_find_cell connect_failed_to_parse_port_expr connect_opt_expected))

#connwrappers
$(eval $(call template,connwrappers, connwrappers connwrappers_signed connwrappers_unsigned connwrappers_port ))

#plugin
$(eval $(call template,plugin, plugin plugin_i plugin_a plugin_l ))
$(eval $(call template,plugin_error, plugin_error ))

#select
$(eval $(call template,select, select select_all select_add select_add_all select_assert_any select_assert_count select_assert_max select_assert_min select_assert_none select_clear select_count select_del select_list select_module select_none select_read select_set select_write select_add_A_eq select_add_a_eq select_add_A_lesseq select_add_a_lesseq select_add_A_less select_add_a_less select_add_A_moreeq select_add_a_moreeq select_add_A_more select_add_a_more select_add_A select_add_a select_add_c select_add_i select_add_mid select_add_m select_add_n select_add_obj select_add_o select_add_p select_add_r_eq select_add_r_lesseq select_add_r_less select_add_r_moreeq select_add_r_more select_add_r select_add_ss select_add_s select_add_t select_add_w select_add_x ))
$(eval $(call template,select_mem, select select_all select_add select_add_all select_assert_any select_assert_count_mem select_assert_max_mem select_assert_min select_assert_none select_clear select_count select_del select_list select_module_mem ))
$(eval $(call template,select_ls, select_ls select_ls_top))
$(eval $(call template,select_cd, select_cd select_cd_up select_cd_module ))
$(eval $(call template,select_stack,select_%a select_%cie select_%ci select_%coe select_%co select_%C select_%c select_%i select_%M select_%m select_%n select_%R4 select_%R select_%s select_%u select_%x_%D select_%x_%d select_%xe select_%))
$(eval $(call template,select_error, select_add_with_del select_assert_any_failed select_assert_any_with_count select_assert_count_failed select_assert_list_with_assert_max select_assert_list_with_del select_assert_max_failed select_assert_max_with_del select_assert_min_failed select_assert_none_failed select_assert_none_with_min select_cant_open_for_reading select_cant_open_for_writing select_clear_with_other_opt select_count_with_assert_min select_count_with_assert_none select_error_in_expand_op select_none_with_other_opt select_no_sel_to_check_as_any select_no_sel_to_check_as_count select_no_sel_to_check_as_max select_no_sel_to_check_as_min select_no_sel_to_check_as_none select_no_such_module select_nothing_to_add select_nothing_to_del select_one_elem_for__a select_one_elem_for__cie select_one_elem_for__ci select_one_elem_for__coe select_one_elem_for__co select_one_elem_for__C select_one_elem_for__c select_one_elem_for__D select_one_elem_for__d select_one_elem_for__i select_one_elem_for__m select_one_elem_for__M select_one_elem_for__n select_one_elem_for__R select_one_elem_for__s select_one_elem_for__u select_one_elem_for__xe select_one_elem_for__x select_read_with_selection_expr select_selection_isnt_defined select_set_with_assert_any select_set_with_assert_max select_set_with_count select_set_with_del select_set_with_list select_unknown_opt select_unknown_selection select_write_with_assert_count select_write_with_del))
$(eval $(call template,select_cd_error, select_cd_invalid_number_of_args select_cd_no_such_module ))


#setattr
$(eval $(call template,setattr, setattr setattr_mod setattr_set setattr_top setattr_unset setattr_set_proc ))
$(eval $(call template,setattr_mem, setattr setattr_mod setattr_set setattr_top setattr_unset setattr_set_proc ))
$(eval $(call template,setattr_error, setattr_cant_decode_value ))
#setparam
#setparam_type - issue #926
#ERROR: Found error in internal cell \top.$procdff$4 ($dff) at kernel/rtlil.cc:715:
$(eval $(call template,setparam, setparam setparam_set  setparam_unset setparam_top setparam_type))
#chparam
$(eval $(call template,chparam, chparam chparam_set chparam_top chparam_list ))
$(eval $(call template,chparam_error, chparam_error))

#setundef
$(eval $(call template,setundef, setundef_one setundef_anyseq setundef_anyconst setundef_init setundef_random setundef_undef setundef_undriven setundef_expose))
# issue #1092
$(eval $(call template,setundef_error, setundef_expose_without_undriven setundef_init_with_anyconst setundef_init_with_anyseq setundef_one_of_options setundef_undriven_with_process))

#assertpmux
$(eval $(call template,assertpmux, assertpmux assertpmux_noinit assertpmux_always))
$(eval $(call template,assertpmux_mux, assertpmux assertpmux_noinit assertpmux_always))

#eval
$(eval $(call template,eval, eval eval_set eval_set_undef eval_table eval_show eval_brute_force_equiv_checker eval_show_not_set eval_table_set eval_vloghammer_report eval_vloghammer_report_rtl))
$(eval $(call template,eval_error, eval_only_one_module eval_failed_to_parse_lhs eval_failed_to_parse_rhs eval_rhs_expr eval_diff_lhs_rhs_sizes eval_failed_to_parse_show_expr eval_failed_to_parse_table_expr eval_empty_selection eval_port_doesnt_match eval_cant_find_mod_1 eval_cant_find_mod_2 eval_mods_arent_equiv eval_cant_find_mod_in_curr_des eval_no_output_wire eval_cant_find_input eval_wire_isnt_an_input eval_failed_to_parse_pattern eval_pattern_is_to_short eval_two_distinct_solutions))

#freduce
$(eval $(call template,freduce, freduce freduce_v freduce_vv freduce_inv freduce_stop freduce_dump ))
$(eval $(call template,freduce_dff, freduce freduce_v freduce_vv freduce_inv freduce_stop freduce_dump ))
$(eval $(call template,freduce_ffs, freduce freduce_v freduce_vv freduce_inv freduce_stop freduce_dump ))
$(eval $(call template,freduce_mem, freduce freduce_v freduce_vv freduce_inv freduce_stop freduce_dump ))
$(eval $(call template,freduce_error, freduce_logic_loop ))

#miter -assert
$(eval $(call template,miter_assert, miter_assert miter_assert_flatten ))
$(eval $(call template,miter_assert_assume, miter_assert miter_assert_flatten ))
$(eval $(call template,miter_error, miter_cant_find_gate_module miter_cant_find_gold_module miter_cant_find_module miter_missing_mode_param miter_no_match_in_gate miter_no_match_in_gold miter_there_is_already_a_module ))

#sat
#sat_tempinduct_def  sat_tempinduct_tempinduct_def - issue #883
#ERROR: Assert `!undef_mode || model_undef' failed in ./kernel/satgen.h:90.
$(eval $(call template,sat, sat_dump_cnf sat_dump_json sat_dump_vcd sat_initsteps sat_maxsteps sat_max sat_prove_x sat_set_all_undef_at sat_set_all_undef sat_set_any_undef_at sat_set_any_undef sat_set_def_at sat_set_def sat_set_init sat_set sat_show sat_stepsize sat_tempinduct_skip sat_unset_at sat_set_at sat_seq sat_prove_skip sat_timeout sat_prove sat_tempinduct sat sat_all sat_ignore_unknown_cells sat_enable_undef sat_max_undef sat_show_inputs sat_show_outputs sat_show_ports sat_show_regs sat_show_public sat_show_all sat_set_assumes sat_set_init_undef sat_set_init_def sat_set_init_zero  sat_tempinduct_baseonly sat_tempinduct_inductonly sat_verify sat_verify_no_timeout sat_falsify sat_falsify_no_timeout sat_prove_asserts sat_tempinduct_tempinduct_baseonly sat_set_def_inputs sat_tempinduct_baseonly_maxsteps sat_tempinduct_def sat_tempinduct_tempinduct_def))
$(eval $(call template,sat_error, sat_show_fail sat_provex_diff_size sat_provex_lhs_fail sat_provex_rhs_fail sat_prove_rhs_fail sat_prove_lhs_fail sat_prove_diff_size sat_set_all_undef_fail sat_set_any_undef_fail sat_set_def_fail sat_set_diff_size sat_set_rhs_fail sat_set_lhs_fail sat_cnf_open_json_file sat_cant_open_json_file sat_cant_open_vcd_file sat_falsify_fail sat_verify_fail sat_all_with_tempinduct sat_maxundef_with_tempinduct sat_max_with_tempinduct sat_max_max_undef_with_tempinduct sat_max_all_with_tempinduct sat_max_maxundef_with_tempinduct sat_max_maxundef_all_with_tempinduct sat_maxsteps_only_for_tempinduct sat_si_def_zero sat_si_undef_zero sat_si_def_undef sat_si_def_undef_zero sat_failed_to_import_cell sat_prove_skip_must_be_smaller_than_seq sat_prove_and_tempinduct sat_got_tempinduct_but_nothing_to_prove sat_cant_perform_sat_on_empty_sel sat_only_one_module_must_be_sel))

#sat_set_all_undef_at_fail sat_set_any_undef_at_fail sat_set_def_at_fail sat_unset_at_fail sat_set_at_diff_size sat_set_at_lhs_fail sat_set_at_rhs_fail - no errors

#sim
$(eval $(call template,sim,sim sim_a sim_clock sim_d sim_n sim_rstlen sim_vcd sim_w sim_zinit ))
$(eval $(call template,sim_mem,sim sim_a sim_clockn sim_clock_mem sim_d sim_n sim_resetn sim_reset sim_rstlen sim_vcd sim_w sim_zinit_mem ))

#splitnets
$(eval $(call template,splitnets, splitnets splitnets_format splitnets_ports splitnets_driver splitnets_dpf ))
$(eval $(call template,splitnets_logic, splitnets splitnets_format splitnets_ports splitnets_driver splitnets_dpf ))

#splice
$(eval $(call template,splice, splice splice_sel_by_cell splice_sel_by_wire splice_sel_any_bit splice_wires splice_no_outputs splice_port splice_no_port ))
$(eval $(call template,splice_error, splice_sel_by_cell_and_sel_by_wire splice_sel_by_cell_and_sel_any_bit splice_port_and_no_port ))

#supercover
$(eval $(call template,supercover, supercover))

#rmports
$(eval $(call template,rmports, rmports))

#check
$(eval $(call template,check, check check_noinit check_initdrv check_assert))
$(eval $(call template,check_error, check_error ))

#design
$(eval $(call template,design, design_import design_copy_from design_copy_to design_as))
$(eval $(call template,design_error, design_no_saved_design_copy_from design_no_saved_design_import design_no_saved_design_load design_no_pushed_design design_no_top_module))

#log
$(eval $(call template,log, log log_stdout log_stderr log_nolog log_n))

#tee
$(eval $(call template,tee, tee))
$(eval $(call template,tee_error, tee_o_cant_create_file tee_a_cant_create_file ))

#test_autotb
$(eval $(call template,test_autotb, test_autotb test_autotb_file test_autotb_n test_autotb_seed))

#abc
$(eval $(call template,abc, abc_D abc_g_aig abc_g_cmos2 abc_g_cmos abc_g_simple abc_mux16 abc_mux4 abc_mux8 abc_S abc_dff abc_constr_liberty))
$(eval $(call template,abc_dff, abc_D abc_g_aig abc_g_cmos2 abc_g_cmos abc_g_simple abc_mux16 abc_mux4 abc_mux8 abc_S abc_dff abc_constr_liberty))
$(eval $(call template,abc_mux, abc_D abc_g_aig abc_g_cmos2 abc_g_cmos abc_g_simple abc_mux16 abc_mux4 abc_mux8 abc_S abc_dff abc_constr_liberty))
$(eval $(call template,abc_error, abc_cannot_open abc_constr_no_liberty abc_lut_liberty abc_unsup_gate_type abc_inv_luts_synt  abc_return_code abc_clk_domain_not_found abc_script_o abc_script_top))

#hilomap
$(eval $(call template,hilomap, hilomap hilomap_hicell hilomap_locell hilomap_singleton hilomap_hicell_singleton hilomap_locell_singleton hilomap_hicell_locell_singleton))

#cutpoint
$(eval $(call template,cutpoint, cutpoint cutpoint_undef))

#mutate
$(eval $(call template,mutate, mutate_list mutate_cnot1 mutate_cnot0 mutate_const1 mutate_const0 mutate_inv mutate_all mutate_list_cfg mutate_list_ctrl mutate_list_none mutate_list_o mutate_list_seed mutate_list_s))
$(eval $(call template,mutate_mem, mutate_list mutate_all))
$(eval $(call template,mutate_error, mutate_error))

#fmconbine
#fmcombine_gate_cell_not_found - failed #1063
$(eval $(call template,fmcombine, fmcombine fmcombine_fwd fmcombine_bwd fmcombine_nop fmcombine_bwd_fwd fmcombine_anyeq fmcombine_initeq))
$(eval $(call template,fmcombine_assert_assume, fmcombine fmcombine_fwd fmcombine_bwd fmcombine_nop fmcombine_bwd_fwd fmcombine_anyeq fmcombine_initeq))
$(eval $(call template,fmcombine_error, fmcombine_invalid_number_of_param fmcombine_module_not_found fmcombine_gold_cell_not_found fmcombine_gate_cell_not_found fmcombine_types_not_match fmcombine_nop_with_fwd fmcombine_nop_with_bwd fmcombine_nop_with_fwd_bwd))

#pmuxtree
$(eval $(call template,pmuxtree, pmuxtree))

#opt_rmdff_sat
$(eval $(call template,opt_rmdff_sat, opt_rmdff_sat))

#wbflip
$(eval $(call template,wbflip, wbflip wbflip_top))

#pmux2shiftx
$(eval $(call template,pmux2shiftx, pmux2shiftx_norange pmux2shiftx_onehot_shiftx pmux2shiftx_onehot_pmux pmux2shiftx_onehot_ignore pmux2shiftx_min_choices_0 pmux2shiftx_min_choices_3000 pmux2shiftx_min_dens_3000 pmux2shiftx_min_dens_0 pmux2shiftx_vv pmux2shiftx_v pmux2shiftx_top pmux2shiftx ))
$(eval $(call template,pmux2shiftx_2, pmux2shiftx_norange pmux2shiftx_onehot_shiftx pmux2shiftx_onehot_pmux pmux2shiftx_onehot_ignore pmux2shiftx_min_choices_0 pmux2shiftx_min_choices_3000 pmux2shiftx_min_dens_3000 pmux2shiftx_min_dens_0 pmux2shiftx_vv pmux2shiftx_v pmux2shiftx_top pmux2shiftx ))
$(eval $(call template,pmux2shiftx_fsm, pmux2shiftx_norange pmux2shiftx_onehot_shiftx pmux2shiftx_onehot_pmux pmux2shiftx_onehot_ignore pmux2shiftx_min_choices_0 pmux2shiftx_min_choices_3000 pmux2shiftx_min_dens_3000 pmux2shiftx_min_dens_0 pmux2shiftx_vv pmux2shiftx_v pmux2shiftx_top pmux2shiftx ))

#onehot
$(eval $(call template,onehot, onehot onehot_v onehot_vv ))

#help
$(eval $(call template,help, help_celltype_plus help_celltype help_cells help_all help_command help help_no_such_command ))

#echo
$(eval $(call template,echo, echo echo_off echo_on ))

#debug
$(eval $(call template,debug, debug ))

#muxpack
$(eval $(call template,muxpack, muxpack ))

#history
$(eval $(call template,history, history ))

#script
$(eval $(call template,script, script script_from_to script_scriptwire ))

#tcl
$(eval $(call template,tcl, tcl ))

#abc9
$(eval $(call template,abc9, abc9_markgroups abc9_showtmp abc9_nocleanup abc9_luts abc9_lut abc9_fast abc9_D abc9_W abc9_wo_proc abc9_wo_synth abc9_box abc9_script))
$(eval $(call template,abc9_dff, abc9_markgroups abc9_showtmp abc9_nocleanup abc9_luts abc9_lut abc9_fast abc9_D abc9_W abc9_wo_proc abc9_wo_synth))
$(eval $(call template,abc9_mux, abc9_markgroups abc9_showtmp abc9_nocleanup abc9_luts abc9_lut abc9_fast abc9_D abc9_W abc9_wo_proc abc9_wo_synth))
$(eval $(call template,abc9_mem, abc9_markgroups abc9_showtmp abc9_nocleanup abc9_luts abc9_lut abc9_fast abc9_D abc9_W abc9_wo_proc abc9_wo_synth))
$(eval $(call template,abc9_error, abc9_invalid_luts_syntax abc9_cant_open_output_file))


.PHONY: all clean
