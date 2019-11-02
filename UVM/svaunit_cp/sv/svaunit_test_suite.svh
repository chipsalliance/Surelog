/******************************************************************************
 * (C) Copyright 2015 AMIQ Consulting
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * NAME:        svaunit_test_suite.svh
 * PROJECT:     svaunit
 * Description: svaunit test suite class definition
 *******************************************************************************/

`ifndef SVAUNIT_TEST_SUITE_SVH
`define SVAUNIT_TEST_SUITE_SVH

// svaunit test suite class definition
class svaunit_test_suite extends svaunit_test;
	`uvm_component_utils(svaunit_test_suite)

	// List of tests of the current test suite
	local svaunit_test lof_tests[$];

	// If 1 the test suite will continue to run if the previous test was failed, if 0 it will be stopped
	bit continue_driving;

	/* Constructor for svaunit_test_suite
	 * @param name   : instance name for svaunit_test_suite object
	 * @param parent : hierarchical parent for svaunit_test_suite
	 */
	function new (string name = "svaunit_test_suite", uvm_component parent);
		super.new(name, parent);

		continue_driving = 1;
	endfunction

	/* Build phase method used to instantiate components
	 * @param phase : the phase scheduled for build_phase method
	 */
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		set_name_for_test();
	endfunction

	/* Set continue driving switch
	 * @param a_continue_driving : value of continue driving
	 */
	virtual function void set_continue_driving(bit a_continue_driving);
		continue_driving = a_continue_driving;
	endfunction

	/* Get continue driving switch value
	 * @return the value of continue driving
	 */
	virtual function bit get_continue_driving();
		return continue_driving;
	endfunction

	/* Create a test or a sequence instance name
	 * @param a_test_or_seq_type : the test or the sequence type used to create the object
	 * @return the name of the object to be created
	 */
	virtual function string create_test_name(string a_test_or_seq_type);
		int index[$];

		index = lof_tests.find_index() with (vpiw.find(item.get_test_name(), a_test_or_seq_type) != -1);

		if(index.size() > 0) begin
			return $sformatf("%s@%0d", a_test_or_seq_type, index.size());
		end else begin
			return a_test_or_seq_type;
		end
	endfunction

	/* Add a given unit test into test list
	 * @param a_obj : a test or a sequence which needs to be added into the list
	 */
	virtual function void add_test (uvm_object a_obj);
		svaunit_base_sequence a_seq;
		svaunit_test a_test;
		uvm_component parent;
		string new_name = "";

		if ($cast(a_seq, a_obj)) begin

			automatic svaunit_sequence_test#(svaunit_base_sequence) the_test = svaunit_sequence_test#(svaunit_base_sequence
			)::type_id::create(create_test_name(a_seq.get_type_name()), this);


			if(!($cast(the_test.seq, a_seq))) begin
				`uvm_fatal("SVAUNIT_CAST_ERR", $sformatf("Could not cast the %s sequence to svaunit_sequence_base",
						the_test.get_test_name()))
			end

			parent = the_test.get_parent();
			new_name = {new_name, parent.get_type_name(), ".", a_seq.get_type_name()};
			the_test.update_test_name(create_test_name(new_name));
			the_test.stop_test = a_seq.get_stop();
			lof_tests.push_back(the_test);
		end
		if ($cast(a_test, a_obj)) begin
			a_test.set_name_for_test();
			lof_tests.push_back(a_test);
		end
	endfunction

	// Update status for a test-suite
	virtual function void update_status();
		int unsigned nof_tests_not_run = 0;

		foreach(lof_tests[test_index]) begin
			lof_tests[test_index].update_status();
		end

		set_nof_tests(get_nof_tests());
		set_nof_failures(get_nof_tests_failed());
		nof_tests_not_run = get_nof_tests_did_not_run();

		set_status(compute_status(get_nof_tests(), get_nof_tests_failed()));
	endfunction

	// {{{ Functions to get test info
	/* Get the tests which ran from current test suite
	 * @param a_tests_ran : list of test which has ran from current test suite
	 */
	virtual function void get_ran_tests(ref svaunit_test a_tests_ran[$]);
		foreach(lof_tests[test_index]) begin
			if(lof_tests[test_index].started()) begin
				a_tests_ran.push_back(lof_tests[test_index]);
			end
		end
	endfunction

	/* Get the tests which didn't run from current test suite
	 * @param a_tests_ran : list of test which didn't run from current test suite
	 */
	virtual function void get_did_not_run_tests(ref svaunit_test a_tests_ran[$]);
		foreach(lof_tests[test_index]) begin
			if(!(lof_tests[test_index].started())) begin
				a_tests_ran.push_back(lof_tests[test_index]);
			end
		end
	endfunction

	/* Compute the number of tests from current test suite
	 * @return the number of tests from current test suite
	 */
	virtual function int unsigned get_nof_tests();
		return lof_tests.size();
	endfunction

	/* Compute the number of tests from current test suite which have failed
	 * @return the number of tests from current test suite which have failed
	 */
	virtual function int unsigned get_nof_tests_failed();
		int unsigned nof_tests_failed = 0;

		foreach(lof_tests[test_index]) begin
			if(lof_tests[test_index].get_status() == SVAUNIT_FAIL) begin
				nof_tests_failed = nof_tests_failed + 1;
			end
		end

		return nof_tests_failed;
	endfunction

	/* Compute the number of tests from current test suite which did not run
	 * @return the number of tests from current test suite which did not run
	 */
	virtual function int unsigned get_nof_tests_did_not_run();
		int unsigned nof_tests_did_not_run = 0;

		foreach(lof_tests[test_index]) begin
			if(lof_tests[test_index].get_status() == SVAUNIT_DID_NOT_RUN) begin
				nof_tests_did_not_run = nof_tests_did_not_run + 1;
			end
		end

		return nof_tests_did_not_run;
	endfunction

	/* Compute the number of active tests during simulation for current test suite
	 * @return the number of active tests during simulation for current test suite
	 */
	virtual function int unsigned get_nof_active_tests();
		// Variable used to store all tests which ran during simulation
		svaunit_test tests_ran[$];

		// Variable used to store the number of active tests during simulation for current test suite
		int unsigned nof_active_tests;

		// Get all tests which ran during simulation
		get_ran_tests(tests_ran);
		nof_active_tests = tests_ran.size();
		tests_ran.delete();

		return nof_active_tests;
	endfunction

	/* Get the tests names as a string
	 * @return a string with all tests names from this test suite
	 */
	virtual function string get_tests_names();
		// Variable used to store the test_names from this test suite
		string test_names = "";

		// Compute the string with all test names
		foreach(lof_tests[test_index]) begin
			test_names = $sformatf("%s\n\t%s", test_names, lof_tests[test_index].get_test_name());
		end

		return test_names;
	endfunction

	/* Get the tests names which ran as a string
	 * @return a string with the tests names which ran from this test suite
	 */
	virtual function string get_tests_names_ran();
		// Variable used to store the test_names from this test suite
		string test_names = "";

		// Get all tests which ran during simulation
		svaunit_test tests_ran[$];
		get_ran_tests(tests_ran);

		// Compute the string with all test names
		foreach(tests_ran[test_index]) begin
			test_names = $sformatf("%s\n\t\t%s", test_names, tests_ran[test_index].get_test_name());
		end
		tests_ran.delete();

		return test_names;
	endfunction

	/* Get the tests names which didn't run as a string
	 * @return a string with the tests names which didn't run from this test suite
	 */
	virtual function string get_tests_names_did_not_run();
		// Variable used to store the test_names from this test suite
		string test_names = "";

		// Get all tests which ran during simulation
		svaunit_test tests_ran[$];
		get_did_not_run_tests(tests_ran);

		// Compute the string with all test names
		foreach(tests_ran[test_index]) begin
			test_names = $sformatf("%s\n\t\t%s", test_names, tests_ran[test_index].get_test_name());
		end
		tests_ran.delete();

		return test_names;
	endfunction
	// }}}

	// {{{ Functions to get SVA info
	/* Get the total number of SVAs tested from all tests
	 * @return the total number of SVAs tested from all tests
	 */
	virtual function int unsigned get_total_nof_tested_sva();
		// Variable used to store the number of times an SVA was tested
		int unsigned nof_tested_sva = 0;

		foreach(lof_tests[test_index]) begin
			// Get the number of times an SVA was tested
			nof_tested_sva = nof_tested_sva + lof_tests[test_index].get_nof_tested_sva();
		end

		return nof_tested_sva;
	endfunction

	/* Get the names of the SVAs which were tested during test
	 * @param a_tested_sva_names : the names of the SVAs which were tested during test
	 */
	virtual function void get_sva_tested_names(ref string a_tested_sva_names[$]);
		foreach(lof_tests[test_index]) begin
			lof_tests[test_index].get_sva_tested_names(a_tested_sva_names);
		end
	endfunction

	/* Get the names of the SVAs which were not tested during test
	 * @param a_sva_not_tested : the names of the SVAs which were not tested during test
	 */
	virtual function void get_sva_not_tested_names(ref string a_sva_not_tested[$]);
		// Variable used to store the names of the SVA which were tested
		string tested_sva_names[$];

		// Variable used to store the names of the SVA which were tested/per test
		string not_tested_sva_names[$];

		int not_tested_index[$];
		int n_tested_index[$];

		foreach(lof_tests[test_index]) begin
			lof_tests[test_index].get_sva_not_tested_names(not_tested_sva_names);
		end

		// Get tested SVAs
		get_sva_tested_names(tested_sva_names);

		foreach(not_tested_sva_names[sva_index]) begin
			n_tested_index = tested_sva_names.find_index() with (item == not_tested_sva_names[sva_index]);

			if(n_tested_index.size() == 0) begin
				not_tested_index = a_sva_not_tested.find_index() with
					(item == not_tested_sva_names[sva_index]);

				if(not_tested_index.size() == 0) begin
					a_sva_not_tested.push_back(not_tested_sva_names[sva_index]);
				end
			end
		end
	endfunction
	// }}}

	// {{{ Function to get checks info
	/* Get a list with all immediate assertions tested into tests
	 * @param a_checks : a list with all immediate assertions tested
	 */
	virtual function void get_checks(ref svaunit_immediate_assertion_info a_checks[$]);
		// Get the checks used in each test
		foreach(lof_tests[test_index]) begin
			lof_tests[test_index].get_checks(a_checks);
		end
	endfunction
	// }}}

	// {{{ Tasks to start testing
	// Task used to start testing - The user should create here scenarios to verify SVAs
	virtual task test();
	endtask

	// Pre-run behavior
	virtual task pre_run();
		`uvm_info(get_test_name(), "Start test suite", UVM_DEBUG)
		// Raise objection mechanism for this test
		uvm_test_done.raise_objection(this, "", 1);

		// Set start bit
		start_test();
	endtask

	// Post-run behavior
	virtual task post_run();
		`uvm_info(get_test_name(), "End test suite", UVM_DEBUG)
		// Raise objection mechanism for this test
		uvm_test_done.drop_objection(this, "", 1);
	endtask

	// Will start the test suite
	virtual task start_ut();
		if(enable == 1) begin
			fork
				begin
					// Variable used to store the process id for test task
					process simulate_ts;
					fork
						begin
							simulate_ts = process::self();
							fork
								begin
									// Run tests
									foreach(lof_tests[test_index]) begin
										if(((stop_test == 0) && (continue_driving == 0)) || (continue_driving == 1)) begin
											lof_tests[test_index].start_test();
											lof_tests[test_index].start_ut();
											stop_test = lof_tests[test_index].get_stop();
										end
									end
								end

								begin
									while(((stop_test == 0) && (continue_driving == 0)) || (continue_driving == 1)) begin
										#1ns;
									end
								end
							join_any
						end
					join
					disable fork;
					simulate_ts.kill();
				end
			join

			// Update status
			update_status();

			// Compact immediate assertions
			get_checks(lof_checks);

			// Print report
			print_report();
		end
	endtask

	/* Run phase method used to run test
	 * @param phase : the phase scheduled for run_phase method
	 */
	virtual task run_phase(uvm_phase phase);
		// Get parent of this test
		uvm_component parent = get_parent();

		// If the test haven't started and its parent is null, it should start from here
		if((!started()) && (parent.get_name() == "")) begin
			if(enable == 1) begin
				pre_run();

				// Run test body of this test suite
				fork
					begin
						// Variable used to store the process id for start_up task
						process start_ut_p;
						fork
							begin
								start_ut_p = process::self();
								start_ut();
								disable fork;
							end
						join
						start_ut_p.kill();
					end
				join

				create_html_report();
				post_run();
			end
		end
	endtask
	// }}}

	// {{{ Reports
	/* Get status as a string
	 * @return represents the status to be printed
	 */
	virtual function string get_status_as_string();
		string nice_string = "";
		string star = " ";
		svaunit_status_type computed_test_status = get_status();

		if(get_status() == SVAUNIT_FAIL) begin
			star = "*";
		end


		nice_string = $sformatf("\n\t%s   %s %s (%0d/%0d test cases PASSED)", star, get_test_name(),
			computed_test_status.name(), get_nof_tests() - get_nof_tests_failed() - get_nof_tests_did_not_run(),
			get_nof_tests());

		return nice_string;
	endfunction

	/* Form the status of the test as a string
	 * @return a string which contains the status of test
	 */
	virtual function string get_status_tests();
		string nice_string = "";
		string extra = "";

		// Get parent of this test
		uvm_component parent = get_parent();

		// If the test haven't started and it's parent is null, it should start from here
		if(parent.get_name() != "") begin
			extra = $sformatf("%s::", get_type_name());
		end

		nice_string = $sformatf("\n\n-------------------- %s test suite status --------------------\n", get_test_name());
		nice_string = $sformatf("%s\t%s::%s\n", nice_string, get_type_name(), get_test_name());

		foreach(lof_tests[test_index]) begin
			nice_string = {nice_string, "\t\t  ",  lof_tests[test_index].get_status_tests()};
		end

		return nice_string;
	endfunction

	// Print status of test
	virtual function void print_status();
		string nice_string = "";
		string star = " ";
		svaunit_status_type computed_test_status = get_status();

		if(get_status() == SVAUNIT_FAIL) begin
			star = "*";
		end

		lof_tests.rsort(item) with (item.get_status() == SVAUNIT_FAIL);

		nice_string = $sformatf("\n\n-------------------- %s test suite: Tests status statistics --------------------\n\n",
			get_test_name());
		nice_string = $sformatf("%s   %s   %s %s (%0d/%0d test cases PASSED)\n", nice_string, star, get_test_name(),
			computed_test_status.name(), get_nof_tests() - get_nof_failures() - get_nof_tests_did_not_run(),
			get_nof_tests());

		foreach(lof_tests[test_index]) begin
			nice_string = $sformatf("%s\t%s", nice_string, lof_tests[test_index].get_status_as_string());
		end

		nice_string = $sformatf("%s\n\n", nice_string);

		`uvm_info(get_test_name(), nice_string, UVM_LOW)
	endfunction

	// Print the tests names which ran and the tests names which didn't run during simulation
	virtual function void print_tests();
		// Variable used to store the report string
		string nice_string = "";

		// Variable used to store the number of tests
		int unsigned total_nof_tests = get_nof_tests();

		// Variable used to store the number of active tests
		int unsigned nof_active_tests = get_nof_active_tests();

		string not_run_tests = get_tests_names_did_not_run();
		
		nice_string = $sformatf("\n\n-------------------- %s test suite: Ran tests statistics --------------------\n\n", get_test_name());
		// Form report string
		nice_string = $sformatf("%s\t%0d/%0d Ran tests",
			nice_string, nof_active_tests, total_nof_tests);
		nice_string = $sformatf("%s\n\t%s\n\n", nice_string, get_tests_names_ran());

		if(not_run_tests != "") begin
			nice_string = $sformatf("\n%s\n\t%0d/%0d Tests did not run during simulation",
				nice_string, total_nof_tests - nof_active_tests, total_nof_tests);
			nice_string = $sformatf("%s\n\t%s\n\n", nice_string, not_run_tests);
		end

		`uvm_info(get_test_name(), nice_string, UVM_LOW)
	endfunction

	/* Form the test topology as a tree
	 * @param a_level : the level where the test is created
	 * @return a string representing the tree
	 */
	virtual function string form_tree(int a_level);
		string extra = "";
		string nice_string;

		for(int level_idx = 0; level_idx < a_level; level_idx++) begin
			extra = {"\t", extra};
		end

		if(a_level == 0) begin
			extra = {"\t", extra};
		end
		
		nice_string = {extra, get_test_name()};

		foreach(lof_tests[test_index]) begin
			nice_string = {nice_string, "\n", extra, lof_tests[test_index].form_tree(a_level + 1)};
		end

		return nice_string;
	endfunction
// }}}
endclass

`endif
