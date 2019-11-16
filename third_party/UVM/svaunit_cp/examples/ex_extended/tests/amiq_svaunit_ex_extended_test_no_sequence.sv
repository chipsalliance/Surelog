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
 * NAME:        amiq_svaunit_ex_extended_test_no_sequence.sv
 * PROJECT:     svaunit
 * Description: Unit test used to verify MY_SVA
 *******************************************************************************/

`ifndef AMIQ_SVAUNIT_EX_EXTENDED_TEST_NO_SEQUENCE_SV
`define AMIQ_SVAUNIT_EX_EXTENDED_TEST_NO_SEQUENCE_SV

// Test used to verify the MY_SVA without using sequences
class amiq_svaunit_ex_extended_test_no_sequence extends svaunit_test;
	`uvm_component_utils(amiq_svaunit_ex_extended_test_no_sequence)

	local virtual my_interface my_if;
	
	/* Constructor for amiq_svaunit_ex_extended_test_no_sequence
	 * @param name   : instance name for amiq_svaunit_ex_extended_test_no_sequence object
	 * @param parent : hierarchical parent for amiq_svaunit_ex_extended_test_no_sequence
	 */
	function new(string name = "amiq_svaunit_ex_extended_test_no_sequence", uvm_component parent);
		super.new(name, parent);
	endfunction

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		// Get the reference to an_interface from UVM config db
		if (!uvm_config_db#(virtual my_interface)::get(uvm_root::get(), "*", "MY_IF", my_if)) begin
			`uvm_fatal("SVAUNIT_NO_VIF_ERR",
				$sformatf("SVA interface for amiq_svaunit_ex_extended_test_no_sequence is not set!"))
		end
	endfunction

	// Create scenarios for MY_SVA
	virtual task test();
		`uvm_info(get_test_name(), "START RUN PHASE", UVM_LOW)

		// Initialize signals
		my_if.pattern <=  1'b1;
		my_if.load  <=  1'b1;

		// Configure assertions
		vpiw.disable_all_assertions();
		vpiw.enable_assertion("MY_SVA");

		// Drive the signals according to specific scenarios
		@(posedge my_if.clk);
		repeat(2) begin
			@(posedge my_if.clk);
			vpiw.check_sva_passed("top.my_if.MY_SVA", "The assertion should have succeeded");
		end

		// Trigger error
		my_if.pattern <= 1'b0;

		repeat(2) begin
			@(posedge my_if.clk);
			vpiw.check_sva_failed("top.my_if.MY_SVA", "The assertion should have failed");
		end

		// Remove the error
		my_if.pattern <= 1'b1;
		@(posedge  my_if.clk);
		vpiw.check_sva_passed("top.my_if.MY_SVA", "The assertion should have succeeded");
		my_if.pattern <= 1'b0;
		@(posedge  my_if.clk);
		my_if.pattern <= 1'b1;
		@(posedge  my_if.clk);
		vpiw.check_sva_failed("top.my_if.MY_SVA", "The assertion should have failed");
		@(posedge  my_if.clk);

		`uvm_info(get_test_name(), "END RUN PHASE", UVM_LOW)
	endtask
endclass


`endif
