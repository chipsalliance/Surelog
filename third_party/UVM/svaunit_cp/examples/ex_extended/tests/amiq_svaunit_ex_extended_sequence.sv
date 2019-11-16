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
 * NAME:        amiq_svaunit_ex_extended_sequence.sv
 * PROJECT:     svaunit
 * Description: Example of a simple sequence
 *******************************************************************************/

`ifndef AMIQ_SVAUNIT_EX_EXTENDED_SEQUENCE_SV
`define AMIQ_SVAUNIT_EX_EXTENDED_SEQUENCE_SV

// Example of a simple sequence
class amiq_svaunit_ex_extended_sequence extends svaunit_base_sequence;
	`uvm_object_utils(amiq_svaunit_ex_extended_sequence)

	// Reference to virtual interface containing the SVA
	local virtual nested_interface my_nested_if;

	/* Constructor for an amiq_svaunit_ex_extended_sequence
	 * @param name   : instance name for amiq_svaunit_ex_extended_sequence object
	 */
	function new(string name = "amiq_svaunit_ex_extended_sequence");
		super.new(name);

		// Get the reference to an_interface from UVM config db
		if (!uvm_config_db#(virtual nested_interface)::get(uvm_root::get(), "*", "MY_NESTED_IF", my_nested_if)) begin
			`uvm_fatal("SVAUNIT_NO_VIF_ERR",
				$sformatf("SVA interface for amiq_svaunit_ex_extended_sequence is not set!"))
		end
	endfunction


	// Create scenarios for MY_NESTED_SVA
	virtual task body();
		`uvm_info(get_test_name(), "START RUN PHASE", UVM_LOW)

		// Initialize signals
		my_nested_if.read <= 1'b1;
		my_nested_if.read_and_clear <= 1'b0;
		
		// Configure assertions
		vpiw.disable_all_assertions();
		vpiw.enable_assertion("MY_NESTED_SVA");

		// Drive the signals according to specific scenarios
		@(posedge my_nested_if.clk);
		repeat(2) begin
			@(posedge my_nested_if.clk);
			vpiw.check_sva_passed("top.my_if.nested_if.MY_NESTED_SVA", "The assertion should have succeeded");
		end

		my_nested_if.read_and_clear <= 1'b1;
		@(posedge my_nested_if.clk);
		vpiw.check_sva_failed("MY_NESTED_SVA", "The assertion should have failed");
		
		`uvm_info(get_test_name(), "END RUN PHASE", UVM_LOW)
	endtask
endclass

`endif
