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
 * NAME:        amiq_svaunit_ex_extended_test_with_parameter.sv
 * PROJECT:     svaunit
 * Description: Unit test with a parameter used to verify MY_NESTED_SVA
 *******************************************************************************/

`ifndef AMIQ_SVAUNIT_EX_EXTENDED_TEST_WITH_PARAMETER_SV
`define AMIQ_SVAUNIT_EX_EXTENDED_TEST_WITH_PARAMETER_SV

// Unit test used to verify the MY_NESTED_SVA - example with a parameter
class amiq_svaunit_ex_extended_test_with_parameter#(int unsigned A_PARAM = 10) extends svaunit_test;
	`uvm_component_param_utils(amiq_svaunit_ex_extended_test_with_parameter#(A_PARAM))
	`SVAUNIT_TEST_WITH_PARAM_UTILS

	// Reference to virtual interface containing MY_NESTED_SVA
	local virtual nested_interface my_nested_if;

	/* Constructor for amiq_svaunit_ex_extended_test_with_parameter
	 * @param name   : instance name for amiq_svaunit_ex_extended_test_with_parameter object
	 * @param parent : hierarchical parent for amiq_svaunit_ex_extended_test_with_parameter
	 */
	function new(string name = "amiq_svaunit_ex_extended_test_with_parameter", uvm_component parent);
		super.new(name, parent);
	endfunction


	virtual function void build_phase(input uvm_phase phase);
		super.build_phase(phase);

		// Get the reference to nested_interface from UVM config db
		if (!uvm_config_db#(virtual nested_interface)::get(uvm_root::get(), "*", "MY_NESTED_IF", my_nested_if)) begin
			`uvm_fatal("SVAUNIT_NO_VIF_ERR", $sformatf("SVA interface for %s unit test is not set!", get_test_name()))
		end
	endfunction

	// Create scenarios for MY_NESTED_SVA
	virtual task test();
		// Initialize signals
		my_nested_if.read <=  1'b1;
		my_nested_if.read_and_clear  <=  1'b0;

		// Configure assertions
		vpiw.disable_all_assertions();
		vpiw.enable_assertion("MY_NESTED_SVA");

		// Start the scenario
		@(posedge my_nested_if.clk);
		my_nested_if.read_and_clear <= 1'b1;
		
		repeat(A_PARAM) begin	
			@(posedge my_nested_if.clk);
			vpiw.check_sva_failed("MY_NESTED_SVA", "The SVA should have failed");
		end
	endtask
endclass

`endif
