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
 * MODULE:       svaunit_base.svh
 * PROJECT:      svaunit
 * Description:  svaunit base class for tests and test suites
 *******************************************************************************/

`ifndef SVAUNIT_BASE_SVH
`define SVAUNIT_BASE_SVH

// svaunit base class for tests and test suites
class svaunit_base extends uvm_test;
	// Shows that the test is enable or disable during simulation
	bit enable;

	// When this bit is 1, the test should stop
	bit stop_test;

	`uvm_component_utils(svaunit_base)

	// Test status
	local svaunit_status_type test_status;

	// Shows that the test ran or not during a simulation
	local bit has_started;

	// Stores the number of immediate assertions which fails during a test
	local int unsigned nof_failures;

	// Stores the total number of immediate assertions tested
	local int unsigned nof_tests;

	// Stores the name of the current test
	local string test_name;

	// Stores the type of the current test
	local string test_type;

	// List of immediate assertions tested during a specific test
	svaunit_immediate_assertion_info lof_checks[$];

	// Pointer to VPI wrapper
	svaunit_vpi_wrapper vpiw;

	// List with sequence names started from this test
	string sequence_name[$];

	/* Constructor for svaunit_base
	 * @param name   : instance name for svaunit_base object
	 * @param parent : hierarchical parent for svaunit_base
	 */
	function new(string name = "svaunit_base", uvm_component parent);
		super.new(name, parent);

		// Initialize the counters
		nof_failures = 0;
		nof_tests = 0;
		has_started = 0;
		stop_test = 0;
		enable = 1;
	endfunction

	/* Build phase method used to instantiate components
	 * @param phase : the phase scheduled for build_phase method
	 */
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		// Get the VPI wrapper from UVM config db
		if (!uvm_config_db#(svaunit_vpi_wrapper)::get(uvm_root::get(), "*", "VPIW", vpiw)) begin
			`uvm_fatal("SVAUNIT_VPI_TEST_NO_WRAPPER_ERR", $sformatf(
					"SVAUnit VPI wrapper for the %s unit test is not set! Please enable SVAUnit package!", get_test_name()))
		end

		set_test_name();
	endfunction

	/* Connect phase method used to connect pointers
	 * @param phase : the phase scheduled for connect_phase method
	 */
	virtual function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
	endfunction

	/* Will update the test_name
	 * @param a_test_name : the newest test name to be updated
	 */
	virtual function void update_test_name(string a_test_name);
		test_name = a_test_name;
	endfunction

	// Will set the name of the current test
	virtual function void set_test_name();
	endfunction

	/* Will set the name of the current test
	 * a test name will look like this : test_suite_type_name.test_type_name
	 */
	virtual function void set_name_for_test();
		// Get parent of this test
		uvm_component parent = get_parent();

		if(parent.get_name() == "") begin
			test_name = $sformatf("%s", get_type_name());
		end else begin
			if(parent.get_name() == "uvm_test_top") begin
				test_name = $sformatf("%s.%s", parent.get_type_name(), get_name());
			end else begin
				if(get_name() == "uvm_test_top") begin
					test_name = $sformatf("%s", get_name());
				end else begin
					test_name = $sformatf("%s.%s", parent.get_name(), get_name());
				end
			end
		end
	endfunction

	/* Get the name of the test
	 * @return the test name
	 */
	virtual function string get_test_name();
		return test_name;
	endfunction


	// Sets the custom message reporter
	virtual function void start_of_simulation();
		// Create a new reporter server and set as server used
		svaunit_reporter sva_unit_server = svaunit_reporter::type_id::create("sva_unit_server", this);
		uvm_report_server::set_server(sva_unit_server);
	endfunction

	/* Get the number of immediate assertions verified during test
	 * @return the number of immediate assertions verified during test
	 */
	virtual function int unsigned get_nof_tests();
		return nof_tests;
	endfunction

	/* Set the number of immediate assertions/tests verified during test
	 * @param a_nof_tests : the number of immediate assertions/tests verified during test
	 */
	virtual function void set_nof_tests(int unsigned a_nof_tests);
		nof_tests = a_nof_tests;
	endfunction

	/* Get the test type
	 * @return the test type
	 */
	virtual function string get_test_type();
		return test_type;
	endfunction

	/* Set the test type
	 * @param a_test_type : the test type to be updated
	 */
	virtual function void set_test_type(string a_test_type);
		test_type = a_test_type;
	endfunction


	/* Get the number of checks which have failed
	 * @return the number of checks which have failed
	 */
	virtual function int unsigned get_nof_failures();
		return nof_failures;
	endfunction

	/* Set the number of checks which have failed
	 * @param a_nof_failures : the number of checks which have failed
	 */
	virtual function void set_nof_failures(int unsigned a_nof_failures);
		nof_failures = a_nof_failures;
	endfunction

	// Start test - set has_started bit
	virtual function void start_test();
		has_started = 1;
	endfunction

	/* Get the fact that the test ran or not during simulation
	 * @return 1 if the test ran or 0 otherwise
	 */
	virtual function bit started();
		return has_started;
	endfunction

	/* Get status of test
	 * @return the status of test
	 */
	virtual function svaunit_status_type get_status();
		return test_status;
	endfunction

	/* Set status of test
	 * @param a_status : the status of test to be updated
	 */
	virtual function void set_status(svaunit_status_type a_status);
		test_status = a_status;
	endfunction

	/* Get stop bit for test
	 * @return the stop bit for test
	 */
	virtual function bit get_stop();
		return stop_test;
	endfunction

	/* Compute the status according to a_nof_tests and a_nof_failures
	 * @param a_nof_tests : a number of total tests exercised during test simulation
	 * @param a_nof_failures : a number of total failed tests exercised during test simulation
	 * @return the computed status
	 */
	virtual function svaunit_status_type compute_status(int unsigned a_nof_tests, int unsigned a_nof_failures);
		// Stores the number of tests which didn't run
		int unsigned nof_tests_not_run = 0;

		nof_tests_not_run = get_nof_tests_did_not_run();

		// If no failure have been found, the test will PASS and it's status is PASSED
		// If some failure have been found, the test will FAIL and it's status is FAILED
		// if the test did not run, it's status is DID_NOT_RUN
		if(a_nof_failures == 0) begin
			if((a_nof_tests == 0) || (nof_tests_not_run == a_nof_tests)) begin
				return SVAUNIT_DID_NOT_RUN;
			end else begin
				return SVAUNIT_PASS;
			end
		end else begin
			return SVAUNIT_FAIL;
		end
	endfunction

	// Update status
	virtual function void update_status();
	endfunction

	/* Compute the number of tests from current test which did not run
	 * @return the number of tests from current test which did not run
	 */
	virtual function int unsigned get_nof_tests_did_not_run();
		return 0;
	endfunction

	// {{{ Functions used for immediate assertions
	/* Get a list with names for all immediate assertion used
	 * @param a_lof_used_checks : the string list which contains the name of the checks used in this unit test
	 */
	virtual function void get_checks_names(ref string a_lof_used_checks[$]);
	endfunction


	/* Get the number of times an SVAUnit check was tested during simulation
	 * @param a_check_name : the name of the SVAUnit check
	 * @return the number of times an SVAUnit check was tested during simulation
	 */
	virtual function int unsigned get_nof_times_check_was_tested(ref string a_check_name);
		return 0;
	endfunction

	/* Get the number of times an SVAUnit check passed during simulation
	 * @param a_check_name : the name of the SVAUnit check
	 * @return the number of times an SVAUnit check passed during simulation
	 */
	virtual function int unsigned get_nof_times_check_has_passed(ref string a_check_name);
		return 0;
	endfunction
	// }}}

	// {{{ Print functions

	// Print the tests names which ran and the tests names which didn't run during simulation
	virtual function void print_tests();
	endfunction

	// Print status of test
	virtual function void print_status();
	endfunction

	/* Get the names of the SVAs which were tested during test
	 * @param a_tested_sva_names : the names of the SVAs which were tested during test
	 */
	virtual function void get_sva_tested_names(ref string a_tested_sva_names[$]);
	endfunction

	/* Get the names of the SVAs which were not tested during test
	 * @param a_sva_not_tested : the names of the SVAs which were not tested during test
	 */
	virtual function void get_sva_not_tested_names(ref string a_sva_not_tested[$]);
	endfunction

	// Print a list with all SVAs
	virtual function void print_sva();
		// Variable used to store the report string
		string nice_string = "";

		// Variable used to store the SVA names which were tested
		string tested_sva_names[$];

		// Variable used to store the SVA names which were not tested
		string sva_not_tested[$];

		// Variable used to store the number of tested SVA
		int unsigned nof_tested_sva;

		// Variable used to store the number of not tested SVA
		int unsigned nof_sva_not_tested;

		get_sva_tested_names(tested_sva_names);
		get_sva_not_tested_names(sva_not_tested);

		nof_tested_sva = tested_sva_names.size();
		nof_sva_not_tested = sva_not_tested.size();

		// Form report string
		nice_string = $sformatf("\n\n-------------------- %s: Exercised SVAs --------------------\n", get_test_name());
		nice_string = $sformatf("%s\n\t%0d/%0d SVA were exercised", nice_string, nof_tested_sva,
			nof_sva_not_tested + nof_tested_sva);

		foreach(tested_sva_names[index]) begin
			nice_string = $sformatf("%s\n\t\t%s", nice_string, tested_sva_names[index]);
		end

		// Verify if there were SVAs which have not been tested. In this case, in the report will appear also the SVAs
		// which were not tested
		if(nof_sva_not_tested > 0) begin
			nice_string = $sformatf("%s\n\n\t%0d SVA were not exercised", nice_string, nof_sva_not_tested);

			foreach(sva_not_tested[index]) begin
				nice_string = $sformatf("%s\n\t\t%s", nice_string, sva_not_tested[index]);
			end
		end

		nice_string = $sformatf("%s\n\n", nice_string);

		`uvm_info(get_test_name(), nice_string, UVM_MEDIUM)
	endfunction

	/* Get a list with all immediate assertions tested into tests
	 * @param a_checks : a list with all immediate assertions tested
	 */
	virtual function void get_checks(ref svaunit_immediate_assertion_info a_checks[$]);
	endfunction

	// Print a report for all checks tested for the current unit test
	virtual function void print_checks();
		vpiw.print_checks_from_specific_list(get_test_name(), lof_checks);
	endfunction

	// Print a report for all checks tested for the SVAs
	virtual function void print_sva_and_checks();
		string a_test_name = get_test_name();

		vpiw.print_sva_and_checks_for_specific_list(a_test_name, lof_checks);
	endfunction

	// Print a report for all SVA which have failed
	virtual function void print_failed_sva();
		string crt_test_name = get_test_name();

		vpiw.print_failed_sva_for_specific_list(crt_test_name, lof_checks);
	endfunction

	/* Form the test topology as a tree
	 * @param a_level : the level where the test is created
	 * @return a string representing the tree
	 */
	virtual function string form_tree(int a_level);
	endfunction

	// Print the the SVAUnit topology
	virtual function void print_tree();
		string nice_string = "";

		nice_string = $sformatf("\n\n-------------------- %s test suite: Project hierarchy --------------------\n", get_test_name());
		nice_string = {nice_string, $sformatf("\n%s", form_tree(0)), "\n\n"};

		`uvm_info(get_test_name(), nice_string, UVM_MEDIUM)
	endfunction

	// Print report for current test suite
	virtual function void print_report();
		print_tree();
		print_status();
		print_tests();
		print_sva();
		print_checks();
		print_sva_and_checks();
		print_failed_sva();
	endfunction
// }}}
endclass

`endif
