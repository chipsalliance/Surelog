#!/bin/bash

set -x
test -d $1
test -f scripts/$2.ys

rm -rf $1/work_$2
mkdir $1/work_$2
if [ $2  == "cover_dir" ]; then
    mkdir $1/work_$2/out_dir
fi
cd $1/work_$2

touch .start

# cases where 'syntax error' or other errors are expected
if echo "$1" | grep ".*_error"; then

	expected_string=""
	expect_fail=0
    #Change checked string for check other errors
	if [ "$2" = "abc_constr_no_liberty" ]; then
		expected_string="ERROR: Got -constr but no -liberty!"
	elif [ "$2" = "abc_cannot_open" ]; then
		expected_string="ERROR: Can't open ABC output file"
	elif [ "$2" = "abc_lut_liberty" ]; then
		expected_string="ERROR: Got -lut and -liberty! This two options are exclusive."
	elif [ "$2" = "abc_unsup_gate_type" ]; then
		expected_string="ERROR: Command syntax error: Unsupported gate type:"
	elif [ "$2" = "abc_inv_luts_synt" ]; then
		expected_string="Invalid -luts syntax"
	elif [ "$2" = "abc_dff" ]; then
		expected_string="Unknown option or option in arguments"
	elif [ "$2" = "abc_return_code" ]; then
		expected_string="failed: return code"
	elif [ "$2" = "abc_clk_domain_not_found" ]; then
		expected_string="ERROR: Clock domain u not found"
	elif [ "$2" = "abc_script_o" ]; then
		expected_string="ERROR: Can't open ABC output file"
	elif [ "$2" = "abc_script_top" ]; then
		expected_string="ERROR: Can't open ABC output file"
	elif [ "$2" = "add_error" ]; then
		expected_string="ERROR: Found incompatible object with same name in module"
	elif [ "$2" = "bugpoint_missing_script" ]; then
		expected_string="ERROR: Missing -script option"
	elif [ "$2" = "bugpoint_do_not_crash" ]; then
		expected_string="ERROR: The provided script file and Yosys binary do not crash on this design"
	elif [ "$2" = "bugpoint_grep_string_not_found" ]; then
		expected_string="ERROR: The provided grep string is not found in the log file"
	elif [ "$2" = "bugpoint_fully_selected_des" ]; then
		expected_string="ERROR: This command only operates on fully selected designs"
	elif [ "$2" = "check_error" ]; then
		expected_string="ERROR: Found 1 problems in 'check -assert'"
	elif [ "$2" = "chformal_error" ]; then
		expected_string="ERROR: Mode option is missing"
	elif [ "$2" = "chparam_error" ]; then
		expected_string="ERROR: The options -set and -list cannot be used together"
	elif [ "$2" = "connect_multiple_modules" ]; then
		expected_string="ERROR: Multiple modules selected:"
	elif [ "$2" = "connect_found_process" ]; then
		expected_string="ERROR: Found processes in selected module"
	elif [ "$2" = "connect_no_modules" ]; then
		expected_string="ERROR: No modules selected."
	elif [ "$2" = "connect_set_with_unset" ] || \
		 [ "$2" = "connect_set_with_port" ] || \
		 [ "$2" = "connect_set_with_unset_and_port" ]; then
		expected_string="ERROR: Can't use -set together with -unset and/or -port."
	elif [ "$2" = "connect_cannot_parse_set_lhs_expr" ]; then
		expected_string="ERROR: Failed to parse set lhs expression"
	elif [ "$2" = "connect_cannot_parse_set_rhs_expr" ]; then
		expected_string="ERROR: Failed to parse set rhs expression"
	elif [ "$2" = "connect_unset_with_nounset" ] || \
		 [ "$2" = "connect_unset_with_port" ] || \
		 [ "$2" = "connect_unset_with_nounset_and_port" ]; then
		expected_string="ERROR: Can't use -unset together with -port and/or -nounset."
	elif [ "$2" = "connect_failed_parse_unset" ]; then
		expected_string="ERROR: Failed to parse unset expression"
	elif [ "$2" = "connect_port_with_nounset" ]; then
		expected_string="ERROR: Can't use -port together with -nounset."
	elif [ "$2" = "connect_cant_find_cell" ]; then
		expected_string="ERROR: Can't find cell"
	elif [ "$2" = "connect_failed_to_parse_port_expr" ]; then
		expected_string="ERROR: Failed to parse port expression"
	elif [ "$2" = "connect_opt_expected" ]; then
		expected_string="Expected -set, -unset, or -port."
	elif [ "$2" = "cover_cant_create_file" ]; then
		expected_string="ERROR: Can't create file"
	elif [ "$2" = "design_no_saved_design_copy_from" ] || \
		 [ "$2" = "design_no_saved_design_import" ] || \
		 [ "$2" = "design_no_saved_design_load" ]; then
		expected_string="ERROR: No saved design"
	elif [ "$2" = "design_no_pushed_design" ]; then
		expected_string="ERROR: No pushed designs"
	elif [ "$2" = "design_no_top_module" ]; then
		expected_string="ERROR: No top module found in source design."
	elif [ "$2" = "eval_only_one_module" ]; then
		expected_string="ERROR: Only one module must be selected for the EVAL pass!"
	elif [ "$2" = "eval_failed_to_parse_lhs" ]; then
		expected_string="ERROR: Failed to parse lhs set expression"
	elif [ "$2" = "eval_failed_to_parse_rhs" ]; then
		expected_string="ERROR: Failed to parse rhs set expression"
	elif [ "$2" = "eval_rhs_expr" ]; then
		expected_string="ERROR: Right-hand-side set expression"
	elif [ "$2" = "eval_diff_lhs_rhs_sizes" ]; then
		expected_string="ERROR: Set expression with different lhs and rhs sizes:"
	elif [ "$2" = "eval_failed_to_parse_show_expr" ]; then
		expected_string="ERROR: Failed to parse show expression"
	elif [ "$2" = "eval_failed_to_parse_table_expr" ]; then
		expected_string="ERROR: Failed to parse table expression"
	elif [ "$2" = "eval_empty_selection" ]; then
		expected_string="ERROR: Can't perform EVAL on an empty selection!"
	elif [ "$2" = "eval_port_doesnt_match" ]; then
		expected_string="in module 1 does not match its counterpart in module 2!"
	elif [ "$2" = "eval_has_no_counterpart" ]; then
		expected_string="in module 1 has no counterpart in module 2!"
	elif [ "$2" = "eval_cant_find_mod_1" ] || \
		 [ "$2" = "eval_cant_find_mod_2" ]; then
		expected_string="ERROR: Can't find module"
	elif [ "$2" = "eval_mods_arent_equiv" ]; then
		expected_string="ERROR: Modules are not equivalent!"
	elif [ "$2" = "eval_cant_find_mod_in_curr_des" ]; then
		expected_string="ERROR: Can't find module dle in current design!"
	elif [ "$2" = "eval_no_output_wire" ]; then
		expected_string="ERROR: No output wire"
	elif [ "$2" = "eval_cant_find_input" ]; then
 		expected_string="ERROR: Can't find input s in module middle!"
	elif [ "$2" = "eval_wire_isnt_an_input" ]; then
 		expected_string="ERROR: Wire w in module middle is not an input!"
	elif [ "$2" = "eval_failed_to_parse_pattern" ]; then
 		expected_string="ERROR: Failed to parse pattern d!"
	elif [ "$2" = "eval_pattern_is_to_short" ]; then
 		expected_string="ERROR: Pattern 1'b1 is to short!"
	elif [ "$2" = "eval_two_distinct_solutions" ]; then
 		expected_string="ERROR: Found two distinct solutions to SAT problem."
	elif [ "$2" = "fmcombine_invalid_number_of_param" ]; then
 		expected_string="ERROR: Invalid number of arguments."
	elif [ "$2" = "fmcombine_module_not_found" ]; then
 		expected_string="ERROR: Module topp not found."
	elif [ "$2" = "fmcombine_gold_cell_not_found" ]; then
 		expected_string="ERROR: Gold cell u_mid8 not found in module top."
	elif [ "$2" = "fmcombine_gate_cell_not_found" ]; then
 		expected_string="ERROR: Gate cell u_mid8 not found in module top."
	elif [ "$2" = "fmcombine_types_not_match" ]; then
 		expected_string="ERROR: Types of gold and gate cells do not match."
	elif [ "$2" = "fmcombine_nop_with_fwd" ] || \
		 [ "$2" = "fmcombine_nop_with_bwd" ] || \
		 [ "$2" = "fmcombine_nop_with_fwd_bwd" ]; then
		expected_string="ERROR: Option -nop can not be combined with -fwd and/or -bwd."
	elif [ "$2" = "freduce_logic_loop" ]; then
 		expected_string="ERROR: Found logic loop:"
	elif [ "$2" = "miter_cant_find_gate_module" ]; then
 		expected_string="ERROR: Can't find gate module"
	elif [ "$2" = "miter_cant_find_gold_module" ]; then
 		expected_string="ERROR: Can't find gold module"
	elif [ "$2" = "miter_cant_find_module" ]; then
 		expected_string="ERROR: Can't find module"
	elif [ "$2" = "miter_missing_mode_param" ]; then
 		expected_string="ERROR: Missing mode parameter!"
	elif [ "$2" = "miter_no_match_in_gate" ]; then
 		expected_string="ERROR: No matching port in gate module was found for"
	elif [ "$2" = "miter_no_match_in_gold" ]; then
 		expected_string="ERROR: No matching port in gold module was found for"
	elif [ "$2" = "miter_there_is_already_a_module" ]; then
 		expected_string="ERROR: There is already a module"
	elif [ "$2" = "mutate_error" ]; then
 		expected_string="ERROR: Invalid mode:"
	elif [ "$2" = "plugin_error" ]; then
 		expected_string="ERROR: Can't load module"
	elif [ "$2" = "rename_obj_not_found" ]; then
 		expected_string="ERROR: Object \`u' not found!"
	elif [ "$2" = "rename_no_top_module" ]; then
 		expected_string="ERROR: No top module found!"
	elif [ "$2" = "rename_invalid_number_of_args" ] || \
		 [ "$2" = "rename_invalid_number_of_args_top" ]; then
 		expected_string="ERROR: Invalid number of arguments!"
	elif [ "$2" = "rename_mode_out_requires" ]; then
 		expected_string="ERROR: Mode -output requires that there is an active module selected."
	elif [ "$2" = "sat_show_fail" ]; then
 		expected_string="ERROR: Failed to parse show expression"
	elif [ "$2" = "sat_provex_diff_size" ]; then
 		expected_string="ERROR: Proof-x expression with different lhs and rhs sizes:"
	elif [ "$2" = "sat_provex_lhs_fail" ]; then
 		expected_string="ERROR: Failed to parse lhs proof-x expression "
	elif [ "$2" = "sat_provex_rhs_fail" ]; then
 		expected_string="ERROR: Failed to parse rhs proof-x expression "
	elif [ "$2" = "sat_prove_rhs_fail" ]; then
 		expected_string="ERROR: Failed to parse rhs proof expression "
	elif [ "$2" = "sat_prove_lhs_fail" ]; then
 		expected_string="ERROR: Failed to parse lhs proof expression "
	elif [ "$2" = "sat_prove_diff_size" ]; then
 		expected_string="ERROR: Proof expression with different lhs and rhs sizes:"
	elif [ "$2" = "sat_set_all_undef_at_fail" ] || \
		 [ "$2" = "sat_set_any_undef_at_fail" ] || \
		 [ "$2" = "sat_set_def_at_fail" ] || \
		 [ "$2" = "sat_set_all_undef_fail" ] || \
		 [ "$2" = "sat_set_any_undef_fail" ] || \
		 [ "$2" = "sat_set_def_fail" ]; then
 		expected_string="ERROR: Failed to parse set-def expression "
	elif [ "$2" = "sat_unset_at_fail" ]; then
 		expected_string="ERROR: Failed to parse lhs set expression "
	elif [ "$2" = "sat_set_at_diff_size" ]; then
 		expected_string="ERROR: Set expression with different lhs and rhs sizes:"
	elif [ "$2" = "sat_set_at_lhs_fail" ]; then
 		expected_string="ERROR: Failed to parse lhs set expression"
	elif [ "$2" = "sat_set_at_rhs_fail" ]; then
 		expected_string="ERROR: Failed to parse rhs set expression"
	elif [ "$2" = "sat_set_diff_size" ]; then
 		expected_string="ERROR: Set expression with different lhs and rhs sizes:"
	elif [ "$2" = "sat_set_rhs_fail" ]; then
 		expected_string="ERROR: Failed to parse rhs set expression"
	elif [ "$2" = "sat_set_lhs_fail" ]; then
 		expected_string="ERROR: Failed to parse lhs set expression"
	elif [ "$2" = "sat_cnf_open_json_file" ] || \
		 [ "$2" = "sat_cant_open_json_file" ] || \
		 [ "$2" = "sat_cant_open_vcd_file" ] ; then
 		expected_string="ERROR: Can't open output file"
	elif [ "$2" = "sat_falsify_fail" ]; then
 		expected_string="ERROR: Called with -falsify and found a model"
	elif [ "$2" = "sat_verify_fail" ]; then
 		expected_string="ERROR: Called with -verify and proof did fail!"
	elif [ "$2" = "sat_maxundef_with_tempinduct" ] || \
		 [ "$2" = "sat_max_with_tempinduct" ] || \
		 [ "$2" = "sat_max_max_undef_with_tempinduct" ] || \
		 [ "$2" = "sat_max_maxundef_with_tempinduct" ] || \
		 [ "$2" = "sat_max_maxundef_all_with_tempinduct" ]; then
 		expected_string="ERROR: The options -max, -all, and -max_undef are not supported for temporal induction proofs!"
	elif [ "$2" = "sat_all_with_tempinduct" ] || \
		 [ "$2" = "sat_max_all_with_tempinduct" ]; then
		expect_fail=1
 		expected_string="SAT temporal induction proof finished - model found for base case: FAIL!"
	elif [ "$2" = "sat_maxsteps_only_for_tempinduct" ]; then
 		expected_string="ERROR: The options -maxsteps is only supported for temporal induction proofs!"
	elif [ "$2" = "sat_si_def_zero" ] || \
		 [ "$2" = "sat_si_undef_zero" ] || \
		 [ "$2" = "sat_si_def_undef" ] || \
		 [ "$2" = "sat_si_def_undef_zero" ]; then
 		expected_string="ERROR: The options -set-init-undef, -set-init-def, and -set-init-zero are exclusive!"
	elif [ "$2" = "sat_failed_to_import_cell" ]; then
 		expected_string="ERROR: Failed to import cell "
	elif [ "$2" = "sat_prove_skip_must_be_smaller_than_seq" ]; then
 		expected_string="ERROR: The value of -prove-skip must be smaller than the one of -seq."
	elif [ "$2" = "sat_prove_and_tempinduct" ]; then
 		expected_string="ERROR: Options -prove-skip and -tempinduct don't work with each other. Use -seq instead of -prove-skip."
	elif [ "$2" = "sat_got_tempinduct_but_nothing_to_prove" ]; then
 		expected_string="ERROR: Got -tempinduct but nothing to prove!"
	elif [ "$2" = "sat_cant_perform_sat_on_empty_sel" ]; then
 		expected_string="ERROR: Can't perform SAT on an empty selection!"
	elif [ "$2" = "sat_only_one_module_must_be_sel" ]; then
 		expected_string="ERROR: Only one module must be selected for the SAT pass! "
	elif [ "$2" = "scc_expect1" ]; then
 		expected_string="ERROR: Found 0 SCCs but expected 1"
	elif [ "$2" = "select_add_with_del" ] || \
		 [ "$2" = "select_assert_any_with_count" ] || \
		 [ "$2" = "select_assert_max_with_del" ] || \
		 [ "$2" = "select_assert_none_with_min" ]; then
 		expected_string="ERROR: Options -add, -del, -assert-none, -assert-any, assert-count, -assert-max or -assert-min can not be combined"
	elif [ "$2" = "select_assert_any_failed" ]; then
 		expected_string="ERROR: Assertion failed: selection is empty: uuu"
	elif [ "$2" = "select_assert_count_failed" ]; then
 		expected_string="ERROR: Assertion failed: selection contains 11 elements instead of the asserted 30: top"
	elif [ "$2" = "select_assert_list_with_assert_max" ] || \
		 [ "$2" = "select_assert_list_with_del" ] || \
		 [ "$2" = "select_write_with_assert_count" ] || \
		 [ "$2" = "select_write_with_del" ] || \
		 [ "$2" = "select_count_with_assert_min" ] || \
		 [ "$2" = "select_count_with_assert_none" ]; then
 		expected_string="ERROR: Options -list, -write and -count can not be combined with -add, -del, -assert-none, -assert-any, assert-count, -assert-max, or -assert-min."
	elif [ "$2" = "select_assert_max_failed" ]; then
 		expected_string="ERROR: Assertion failed: selection contains 11 elements, more than the maximum number 1: top"
	elif [ "$2" = "select_assert_min_failed" ]; then
 		expected_string="ERROR: Assertion failed: selection contains 11 elements, less than the minimum number 30: top"
	elif [ "$2" = "select_assert_none_failed" ]; then
 		expected_string="ERROR: Assertion failed: selection is not empty: top"
	elif [ "$2" = "select_cant_open_for_reading" ]; then
 		expected_string="ERROR: Can't open 'txt.txt' for reading: No such file or directory"
	elif [ "$2" = "select_cant_open_for_writing" ]; then
 		expected_string="ERROR: Can't open './tt/ot.txt' for writing: No such file or directory"
	elif [ "$2" = "select_clear_with_other_opt" ]; then
 		expected_string="ERROR: Option -clear can not be combined with any other options."
	elif [ "$2" = "select_error_in_expand_op" ]; then
 		expected_string="ERROR: Syntax error in expand operator '%x:'."
	elif [ "$2" = "select_none_with_other_opt" ]; then
 		expected_string="ERROR: Option -none can not be combined with any other options."
	elif [ "$2" = "select_no_sel_to_check_as_any" ] || \
		 [ "$2" = "select_no_sel_to_check_as_count" ] || \
		 [ "$2" = "select_no_sel_to_check_as_max" ] || \
		 [ "$2" = "select_no_sel_to_check_as_min" ] || \
		 [ "$2" = "select_no_sel_to_check_as_none" ]; then
 		expected_string="ERROR: No selection to check."
	elif [ "$2" = "select_no_such_module" ]; then
 		expected_string="ERROR: No such module: x"
	elif [ "$2" = "select_nothing_to_add" ]; then
 		expected_string="ERROR: Nothing to add to selection."
	elif [ "$2" = "select_nothing_to_del" ]; then
 		expected_string="ERROR: Nothing to delete from selection."
	elif [ "$2" = "select_one_elem_for__a" ] || \
		 [ "$2" = "select_one_elem_for__cie" ] || \
		 [ "$2" = "select_one_elem_for__ci" ] || \
		 [ "$2" = "select_one_elem_for__coe" ] || \
		 [ "$2" = "select_one_elem_for__co" ] || \
		 [ "$2" = "select_one_elem_for__C" ] || \
		 [ "$2" = "select_one_elem_for__c" ] || \
		 [ "$2" = "select_one_elem_for__m" ] || \
		 [ "$2" = "select_one_elem_for__M" ] || \
		 [ "$2" = "select_one_elem_for__n" ] || \
		 [ "$2" = "select_one_elem_for__R" ] || \
		 [ "$2" = "select_one_elem_for__s" ] || \
		 [ "$2" = "select_one_elem_for__xe" ] || \
		 [ "$2" = "select_one_elem_for__x" ]; then
 		expected_string="ERROR: Must have at least one element on the stack for operator"
	elif [ "$2" = "select_one_elem_for__D" ] || \
		 [ "$2" = "select_one_elem_for__d" ] || \
		 [ "$2" = "select_one_elem_for__i" ] || \
		 [ "$2" = "select_one_elem_for__u" ]; then
 		expected_string="ERROR: Must have at least two elements on the stack for operator"
	elif [ "$2" = "select_read_with_selection_expr" ]; then
 		expected_string="ERROR: Option -read can not be combined with a selection expression."
	elif [ "$2" = "select_selection_isnt_defined" ]; then
 		expected_string="ERROR: Selection @ is not defined!"
	elif [ "$2" = "select_set_with_assert_any" ] || \
		 [ "$2" = "select_set_with_assert_max" ] || \
		 [ "$2" = "select_set_with_count" ] || \
		 [ "$2" = "select_set_with_del" ] || \
		 [ "$2" = "select_set_with_list" ]; then
 		expected_string="ERROR: Option -set can not be combined with -list, -write, -count, -add, -del, -assert-none, -assert-any, -assert-count, -assert-max, or -assert-min."
	elif [ "$2" = "select_unknown_opt" ]; then
 		expected_string="ERROR: Unknown option -x."
	elif [ "$2" = "select_unknown_selection" ]; then
 		expected_string="ERROR: Unknown selection operator '%xmux'"
	elif [ "$2" = "select_cd_invalid_number_of_args" ]; then
 		expected_string="ERROR: Invalid number of arguments."
	elif [ "$2" = "select_cd_no_such_module" ]; then
 		expected_string="ERROR: No such module \`tt/tt' found!"
	elif [ "$2" = "setattr_cant_decode_value" ]; then
 		expected_string="ERROR: Can't decode value "
	elif [ "$2" = "setundef_expose_without_undriven" ]; then
 		expected_string="ERROR: Option -expose must be used with option -undriven."
	elif [ "$2" = "setundef_init_with_anyconst" ] || \
		 [ "$2" = "setundef_init_with_anyseq" ]; then
 		expected_string="ERROR: The options -init and -anyseq / -anyconst are exclusive."
	elif [ "$2" = "setundef_one_of_options" ]; then
 		expected_string="ERROR: One of the options -zero, -one, -anyseq, -anyconst, or -random <seed> must be specified."
	elif [ "$2" = "setundef_undriven_with_process" ]; then
 		expected_string="ERROR: The 'setundef' command can't operate in -undriven mode on modules with processes. Run 'proc' first."
	elif [ "$2" = "show_only_one_module" ]; then
 		expected_string="ERROR: For formats different than 'ps' or 'dot' only one module must be selected."
	elif [ "$2" = "show_cant_open_dot_file" ]; then
 		expected_string="ERROR: Can't open dot file "
	elif [ "$2" = "show_cant_open_lib_file" ]; then
 		expected_string="ERROR: Can't open lib file "
	elif [ "$2" = "show_nothing_there_to_show" ]; then
 		expected_string="ERROR: Nothing there to show."
	elif [ "$2" = "splice_port_and_no_port" ]; then
 		expected_string="ERROR: The options -port and -no_port are exclusive!"
	elif [ "$2" = "splice_sel_by_cell_and_sel_any_bit" ]; then
 		expected_string="ERROR: The options -sel_by_cell and -sel_any_bit are exclusive!"
	elif [ "$2" = "splice_sel_by_cell_and_sel_by_wire" ]; then
 		expected_string="ERROR: The options -sel_by_cell and -sel_by_wire are exclusive!"
	elif [ "$2" = "stat_unsupported_tech" ]; then
 		expected_string="ERROR: Unsupported technology: "
	elif [ "$2" = "stat_cant_find_module" ]; then
 		expected_string="ERROR: Can't find module"
	elif [ "$2" = "stat_cant_open_lib_file" ]; then
 		expected_string="ERROR: Can't open liberty file "
	elif [ "$2" = "tee_o_cant_create_file" ] || \
		 [ "$2" = "tee_a_cant_create_file" ]; then
 		expected_string="ERROR: Can't create file"
	elif [ "$2" = "test_cell_failed_to_open" ]; then
 		expected_string="ERROR: Failed to open output file "
	elif [ "$2" = "test_cell_unexpected_opt" ]; then
 		expected_string="ERROR: Unexpected option: "
	elif [ "$2" = "test_cell_cell_type_not_supported" ]; then
 		expected_string="ERROR: The cell type \`\$_XOR_' is currently not supported. Try one of these:"
	elif [ "$2" = "test_cell_no_cell_t_specified" ]; then
 		expected_string="ERROR: No cell type to test specified."
	elif [ "$2" = "test_cell_dont_spec_cell_type_with_f" ]; then
 		expected_string="ERROR: Do not specify any cell types when using -f."
	elif [ "$2" = "write_file_missing_name" ] || \
		 [ "$2" = "write_file_a_missing_name" ]; then
 		expected_string="ERROR: Missing output filename."
	elif [ "$2" = "abc9_invalid_luts_syntax" ]; then
 		expected_string="ERROR: Invalid -luts syntax."
	elif [ "$2" = "abc9_cant_open_output_file" ]; then
 		expected_string="ERROR: Can't open ABC output file"
	fi


	if   [ "$expect_fail" = "0" ]; then
		if yosys -ql yosys.log ../../scripts/$2.ys; then
			echo FAIL > ${1}_${2}.status
		else
			if  grep "$expected_string" yosys.log && [ "$expected_string" != "" ]; then
				echo PASS > ${1}_${2}.status
			else
				echo FAIL > ${1}_${2}.status
			fi
		fi
	else
		if yosys -ql yosys.log ../../scripts/$2.ys; then
			echo PASS > ${1}_${2}.status
		else
			if  grep "$expected_string" yosys.log && [ "$expected_string" != "" ]; then
				echo FAIL > ${1}_${2}.status
			else
				echo PASS > ${1}_${2}.status
			fi
		fi
	fi
else

	yosys -ql yosys.log ../../scripts/$2.ys
	if [ $? != 0 ] ; then
		echo FAIL > ${1}_${2}.status
		touch .stamp
		exit 0
	fi

	#cases where some object names are/aren't expected in output file (tee -o result.log in the test script)
	cell_failed="0"
	expected_string=""
	expected="1"

	if   [ "$2" = "add" ]; then
		expected_string="wire width 0 \\\w"
	elif [ "$2" = "add_global_input" ]; then
		expected_string="wire width 32000 input 6 \\\gi"
	elif [ "$2" = "add_input" ]; then
		expected_string="wire width 2 input 6 \\\i"
	elif [ "$2" = "add_output" ]; then
		expected_string="wire width 3 output 6 \\\o"
	elif [ "$2" = "add_inout" ]; then
		expected_string="wire width 3 inout 6 \\\34"
	elif [ "$2" = "add_wire" ]; then
		expected_string="wire \\\w"
	elif [ "$2" = "assertpmux" ]; then
		expected_string="cell \$assert"
	elif [ "$2" = "assertpmux_always" ]; then
		expected_string="cell \$assert"
	elif [ "$2" = "assertpmux_noinit" ]; then
		expected_string="cell \$assert"
	elif [ "$1" = "blackbox" ]; then
		expected_string="attribute \\\blackbox 1"
	elif [ "$2" = "chformal" ]; then
		expected_string="cell \$assert"
		expected="0"
	elif [ "$2" = "chformal_assert" ]; then
		expected_string="cell \$assert"
		expected="0"
	elif [ "$2" = "chformal_assert2assume" ]; then
		expected_string="cell \$assert"
		expected="0"
	elif [ "$2" = "chformal_assume" ]; then
		expected_string="cell \$assume"
		expected="0"
	elif [ "$2" = "chformal_assume2assert" ]; then
		expected_string="cell \$assume"
		expected="0"
	elif [ "$2" = "chformal_fair" ]; then
		expected_string="cell \$fair"
		expected="0"
	elif [ "$2" = "chformal_fair2live" ]; then
		expected_string="cell \$fair"
		expected="0"
	elif [ "$2" = "chformal_fair2live_assert2assume" ]; then
		expected_string="cell \$fair"
		expected="0"
	elif [ "$2" = "chformal_live" ]; then
		expected_string="cell \$live"
		expected="0"
	elif [ "$2" = "chformal_live2fair" ]; then
		expected_string="cell \$live"
		expected="0"
	elif [ "$2" = "delete" ]; then
		expected_string="module \\\middle"
		expected="0"
	elif [ "$2" = "delete_proc" ]; then
		expected_string="process \$proc\$../top.v:13\$1"
		expected="0"
	elif [ "$2" = "delete_input" ]; then
		expected_string="wire input 1 \\\x"
		expected="0"
	elif [ "$2" = "delete_output" ]; then
		expected_string="wire output 3 \\\o"
		expected="0"
	elif [ "$2" = "delete_port" ]; then
		expected_string="wire output 4 \\\A"
		expected="0"
	elif [ "$2" = "delete_cell" ]; then
		expected_string="cell \$mux \$ternary\$../top.v:16\$2"
		expected="0"
	elif [ "$2" = "delete_wire" ]; then
		expected_string="wire \\\o"
		expected="0"
	elif [ "$2" = "delete_mem" ]; then
		expected_string="cell \$memrd \$memrd\$\ram\$../top.v:30\$7"
		expected="0"
	elif [ "$2" = "edgetypes" ]; then
		expected_string="\$add"
	elif [ "$1" = "fmcombine" ]; then
		expected_string="Combining cells "
	elif [ "$1" = "insbuf" ]; then
		expected_string="cell \$_BUF_ \$auto\$insbuf"
	elif [ "$1" = "ltp" ]; then
		expected_string="Longest topological path in"
	elif [ "$1" = "mutate" ]; then
		if [ "$2" = "mutate_all" ] || \
		[ "$2" = "mutate_cnot0" ] || \
		[ "$2" = "mutate_cnot1" ] || \
		[ "$2" = "mutate_const0" ] || \
		[ "$2" = "mutate_const1" ] || \
		[ "$2" = "mutate_inv" ]; then
		expected_string="\$auto\$mutate"
		fi
	elif [ "$1" = "mutate_mem" ]; then
		if [ "$2" = "mutate_all" ]; then
		expected_string="\$auto\$mutate"
		fi
	elif [ "$2" = "pmuxtree" ]; then
		expected_string="cell \$pmux"
		expected="0"
	elif [ "$1" = "pmux2shiftx" ]; then
		if [ "$2" = "pmux2shiftx_min_choices_3000" ] || \
		   [ "$2" = "pmux2shiftx_min_dens_3000" ]; then
		   expected="0"
		fi
		expected_string="cell \$shiftx"
	elif [ "$1" = "qwp" ]; then
		expected_string="attribute \\\qwp_position"
	elif [ "$2" = "rename" ]; then
		expected_string="module \\\mid_module"
	elif [ "$2" = "rename_low" ]; then
		expected_string="module \\\newlow"
	elif [ "$2" = "rename_top" ]; then
		expected_string="module \\\new_top"
	elif [ "$2" = "rmports" ]; then
		expected_string="wire output 5 \\\cout"
		expected="0"
	elif [ "$2" = "scatter" ]; then
		expected_string="\$auto\$scatter"
	elif [ "$1" = "scc" ] || \
		[ "$1" = "scc_hier_feedback" ]; then
		expected_string="0 SCCs"
		if [ "$1" = "scc_hier_feedback" ] && [ "$2" = "scc_all_cell_types" ]; then
			expected="0"
		fi
	elif [ "$1" = "scc_feedback" ]; then
		expected_string="0 SCCs"
		expected="0"
	elif [ "$1" = "setattr" ] || \
		[ "$1" = "setattr_mem" ]; then
		if [ "$2" = "setattr" ] || \
		[ "$2" = "setattr_top" ] || \
		[ "$2" = "setattr_unset" ]; then
		expected_string="attribute \\\u 1"
		expected="0"
		else
		expected_string="attribute \\\u 1"
		fi
	elif [ "$1" = "sim" ] || \
		[ "$1" = "sim_mem" ]; then
		if [ "$2" != "sim_d" ]; then
		expected_string="Simulating cycle"
		fi
	elif [ "$1" = "splice" ]; then
		expected_string="\$auto\$splice"
	elif [ "$1" = "splitnets" ]; then
		if [ "$2" = "splitnets_dpf" ] || \
		[ "$2" = "splitnets_driver" ]; then
		expected_string="wire width 8 \$memwr"
		else
		expected_string="wire width 8 \$memwr"
		expected="0"
		fi
	elif [ "$1" = "stat" ]; then
		expected_string="middle                          1"
	elif [ "$1" = "supercover" ]; then
		expected_string="cell \$cover \$auto\$supercover"
	elif [ "$1" = "help" ]; then
		if [ "$2" = "help" ]; then
		expected_string="abc                  use ABC for technology mapping"
		elif [ "$2" = "help_all" ]; then
		expected_string="abc  --  use ABC for technology mapping"
		elif [ "$2" = "help_cells" ]; then
		expected_string="\$_ANDNOT_        (A, B, Y)"
		elif [ "$2" = "help_celltype" ]; then
		expected_string="\$dff (CLK, D, Q)"
		elif [ "$2" = "help_celltype_plus" ]; then
		expected_string="\$dff (CLK, D, Q);"
		elif [ "$2" = "help_command" ]; then
		expected_string="read_verilog \[options\] \[filename\]"
		elif [ "$2" = "help_no_such_command" ]; then
		expected_string="No such command or cell type:"
		fi
	fi

	if [ "$expected_string" != "" ]; then
	if grep "$expected_string" result.log; then
		if [ $expected = "1" ]; then
			cell_failed="0"
		else
			cell_failed="1"
		fi
	else
		if [ $expected = "1" ]; then
			cell_failed="1"
		else
			cell_failed="0"
		fi
	fi
	fi

	if grep 'Assert' result.log || grep 'failed in' result.log || grep 'ERROR' result.log; then
		echo FAIL > ${1}_${2}.status
	elif [ $cell_failed = '1' ]; then
		echo FAIL > ${1}_${2}.status
	else
		echo PASS > ${1}_${2}.status
	fi


fi
touch .stamp
