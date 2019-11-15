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

#write_aiger
$(eval $(call template,write_aiger,write_aiger write_aiger_ascii write_aiger_zinit write_aiger_miter write_aiger_symbols write_aiger_map write_aiger_vmap write_aiger_I write_aiger_O write_aiger_B ))
$(eval $(call template,write_aiger_error, write_aiger_cant_find_top_module write_aiger_cant_open_file write_aiger_miter_and_asserts write_aiger_unsupported_cell_type ))


#write_xaiger
$(eval $(call template,write_xaiger,write_xaiger write_xaiger_ascii write_xaiger_map write_xaiger_vmap ))
$(eval $(call template,write_xaiger_fsm,write_xaiger write_xaiger_ascii write_xaiger_map write_xaiger_vmap ))
$(eval $(call template,write_xaiger_mem,write_xaiger write_xaiger_ascii write_xaiger_map write_xaiger_vmap ))
$(eval $(call template,write_xaiger_error, write_xaiger_cant_find_top_module write_xaiger_cant_open_file ))

#write_blif
$(eval $(call template,write_blif,write_blif write_blif_top write_blif_buf write_blif_unbuf write_blif_true  write_blif_false  write_blif_undef  write_blif_noalias  write_blif_icells  write_blif_gates  write_blif_conn  write_blif_attr  write_blif_param  write_blif_cname  write_blif_iname  write_blif_iattr  write_blif_blackbox  write_blif_impltf))
$(eval $(call template,write_blif_error, write_blif_unmapped_mem write_blif_cant_find_top_module write_blif_unmapped_proc))

#write_btor
$(eval $(call template,write_btor,write_btor write_btor_v write_btor_s))
$(eval $(call template,write_btor_shift,write_btor write_btor_v write_btor_s))
$(eval $(call template,write_btor_div_mod,write_btor write_btor_v write_btor_s))
$(eval $(call template,write_btor_fsm,write_btor write_btor_v write_btor_s write_btor_shift))
$(eval $(call template,write_btor_shift_shiftx,write_btor_shift))
$(eval $(call template,write_btor_logic,write_btor write_btor_v write_btor_s))
$(eval $(call template,write_btor_mem,write_btor_mem write_btor_mem_v write_btor_mem_s))
$(eval $(call template,write_btor_pmux,write_btor_pmux))
$(eval $(call template,write_btor_and_or,write_btor_and_or))
$(eval $(call template,write_btor_shiftx,write_btor write_btor_v write_btor_s))
$(eval $(call template,write_btor_init_assert,write_btor write_btor_v write_btor_s))
$(eval $(call template,write_btor_error, write_btor_no_top_module write_btor_unsupported_cell_type))

#write_edif
$(eval $(call template,write_edif,write_edif write_edif_top write_edif_nogndvcc write_edif_pvector_par write_edif_pvector_bra write_edif_pvector_ang write_edif_attrprop ))
$(eval $(call template,write_edif_error, write_edif_cyclic_dependency write_edif_constant_nodes write_edif_unmapped_mem write_edif_unmapped_proc write_edif_no_module_found ))

#write_firrtl
$(eval $(call template,write_firrtl,write_firrtl))
$(eval $(call template,write_firrtl_fsm,write_firrtl_fsm))
$(eval $(call template,write_firrtl_mem,write_firrtl_mem write_firrtl_mem_wr))
$(eval $(call template,write_firrtl_logic,write_firrtl ))
$(eval $(call template,write_firrtl_reduce,write_firrtl ))
$(eval $(call template,write_firrtl_shift,write_firrtl ))
$(eval $(call template,write_firrtl_shiftx,write_firrtl ))
$(eval $(call template,write_firrtl_paramod,write_firrtl))
$(eval $(call template,write_firrtl_mul,write_firrtl))
$(eval $(call template,write_firrtl_sub,write_firrtl))
$(eval $(call template,write_firrtl_pow,write_firrtl))
$(eval $(call template,write_firrtl_error, write_firrtl_fully_selected write_firrtl_negative_edge_ff write_firrtl_inout_port write_firrtl_unclocked_write_port write_firrtl_complex_write_enable ))

#write_ilang
$(eval $(call template,write_ilang,write_ilang write_ilang_selected))
$(eval $(call template,write_ilang_mem,write_ilang_mem))
$(eval $(call template,write_ilang_mux,write_ilang write_ilang_selected))
$(eval $(call template,write_ilang_fsm,write_ilang write_ilang_selected))
$(eval $(call template,write_ilang_tri,write_ilang write_ilang_selected))
$(eval $(call template,write_ilang_error,write_ilang_error))

#write_intersynth
$(eval $(call template,write_intersynth,write_intersynth write_intersynth_selected write_intersynth_lib write_intersynth_notypes))
$(eval $(call template,write_intersynth_error, write_intersynth_cant_export write_intersynth_unprocessed_proc write_intersynth_cant_open_lib_file))

#write_json
$(eval $(call template,write_json,write_json write_json_aig json json_o json_o_aig json_aig))
$(eval $(call template,write_json_error,write_json_error))

#write_simplec
$(eval $(call template,write_simplec,write_simplec write_simplec_cmos3 write_simplec_cmos4 write_simplec_verbose write_simplec_i8 write_simplec_i16 write_simplec_i32 write_simplec_i64))
$(eval $(call template,write_simplec_mux,write_simplec write_simplec_cmos3 write_simplec_cmos4 write_simplec_verbose write_simplec_i8 write_simplec_i16 write_simplec_i32 write_simplec_i64))
$(eval $(call template,write_simplec_logic,write_simplec write_simplec_cmos3 write_simplec_cmos4 write_simplec_verbose write_simplec_i8 write_simplec_i16 write_simplec_i32 write_simplec_i64))
$(eval $(call template,write_simplec_error,write_simplec_no_c_model write_simplec_not_top_module ))

#write_smt2
$(eval $(call template,write_smt2,write_smt2 write_smt2_synth write_smt2_verbose write_smt2_stbv write_smt2_stdt write_smt2_nomem write_smt2_wires write_smt2_tpl write_smt2_bv write_smt2_mem write_smt2_nobv))
$(eval $(call template,write_smt2_logic,write_smt2 write_smt2_synth write_smt2_verbose write_smt2_stbv write_smt2_stdt write_smt2_nomem write_smt2_wires write_smt2_tpl write_smt2_bv write_smt2_mem write_smt2_nobv))
$(eval $(call template,write_smt2_mem,write_smt2 write_smt2_verbose write_smt2_stbv write_smt2_stdt write_smt2_wires write_smt2_tpl write_smt2_bv write_smt2_mem write_smt2_mem_memtest write_smt2_memtest write_smt2_stbv_memtest write_smt2_anyseq))
$(eval $(call template,write_smt2_fsm,write_smt2 write_smt2_synth write_smt2_verbose write_smt2_stbv write_smt2_stdt write_smt2_nomem write_smt2_wires write_smt2_tpl write_smt2_bv write_smt2_mem write_smt2_nobv))
$(eval $(call template,write_smt2_init_assert,write_smt2_init_assert))
$(eval $(call template,write_smt2_reduce,write_smt2 write_smt2_synth write_smt2_verbose write_smt2_stbv write_smt2_stdt write_smt2_nomem write_smt2_wires write_smt2_tpl write_smt2_bv write_smt2_mem write_smt2_nobv))
$(eval $(call template,write_smt2_shiftx,write_smt2 write_smt2_synth write_smt2_verbose write_smt2_stbv write_smt2_stdt write_smt2_nomem write_smt2_wires write_smt2_tpl write_smt2_bv write_smt2_mem write_smt2_nobv))
$(eval $(call template,write_smt2_error, write_smt2_cyclic_dependency write_smt2_cant_open_tpl write_smt2_multiple_drivers write_smt2_logic_loop ))

#write_smv
$(eval $(call template,write_smv,write_smv write_smv_synth write_smv_noproc write_smv_verbose write_smv_tpl))
$(eval $(call template,write_smv_wide,write_smv write_smv_verbose write_smv_tpl))
$(eval $(call template,write_smv_shift,write_smv_shift))
$(eval $(call template,write_smv_fsm,write_smv write_smv_noproc write_smv_verbose write_smv_tpl))
$(eval $(call template,write_smv_reduce,write_smv_noproc))
$(eval $(call template,write_smv_logic,write_smv write_smv_synth write_smv_noproc write_smv_verbose write_smv_tpl))
$(eval $(call template,write_smv_init_assert,write_smv_init_assert))
$(eval $(call template,write_smv_cmos4,write_smv_cmos4))
$(eval $(call template,write_smv_shiftx,write_smv write_smv_synth write_smv_noproc write_smv_verbose write_smv_tpl))
$(eval $(call template,write_smv_error,write_smv_cant_open_template write_smv_unsupported_cell))

#write_spice
$(eval $(call template,write_spice,write_spice write_spice_top write_spice_big_endian write_spice_neg_i write_spice_pos_i write_spice_nc_prefix write_spice_inames ))
$(eval $(call template,write_spice_error, write_spice_cant_find_top_module write_spice_unmapped_mem write_spice_unmapped_proc))

#write_table
$(eval $(call template,write_table,write_table ))

#write_verilog
$(eval $(call template,write_verilog,write_verilog write_verilog_nostr write_verilog_siminit write_verilog_v write_verilog_slice write_verilog_lut))
$(eval $(call template,write_verilog_tri,write_verilog write_verilog_nostr write_verilog_siminit write_verilog_v ))
$(eval $(call template,write_verilog_ffs,write_verilog write_verilog_nostr write_verilog_siminit write_verilog_v ))
$(eval $(call template,write_verilog_latch,write_verilog write_verilog_nostr write_verilog_siminit write_verilog_v ))
$(eval $(call template,write_verilog_concat,write_verilog write_verilog_nostr write_verilog_siminit write_verilog_v ))
$(eval $(call template,write_verilog_shiftx,write_verilog write_verilog_nostr write_verilog_siminit write_verilog_v ))
$(eval $(call template,write_verilog_shift_shiftx,write_verilog_shift ))



.PHONY: all clean
