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
 * NAME:        amiq_svaunit_ex_basic_test.sv
 * PROJECT:     svaunit
 * Description: Test used to verify SLVERR_SVA and ENABLE_SVA
 *******************************************************************************/

`ifndef AMIQ_SVAUNIT_EX_BASIC_TEST_SV
`define AMIQ_SVAUNIT_EX_BASIC_TEST_SV

// Test used to verify SLVERR_SVA and ENABLE_SVA
class amiq_svaunit_ex_basic_test extends svaunit_test;
	`uvm_component_utils(amiq_svaunit_ex_basic_test)

	local virtual basic_interface basic_if;

	/* Constructor for amiq_svaunit_ex_basic_test
	 * @param name   : instance name for amiq_svaunit_ex_basic_test object
	 * @param parent : hierarchical parent for amiq_svaunit_ex_basic_test
	 */
	function new(string name = "amiq_svaunit_ex_basic_test", uvm_component parent);
		super.new(name, parent);
	endfunction

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		// Get the reference to an_interface from UVM config db
		if (!uvm_config_db#(virtual basic_interface)::get(uvm_root::get(), "*", "BASIC_IF", basic_if)) begin
			`uvm_fatal("SVAUNIT_NO_VIF_ERR",
				$sformatf("SVA interface for amiq_svaunit_ex_basic_test is not set!"))
		end
	endfunction


	virtual task test();
		`uvm_info(get_test_name(), "start of the run phase", UVM_LOW)

		// Initialize signals
		basic_if.enable <=  1'b0;
		basic_if.ready  <=  1'b0;
		basic_if.sel    <=  1'b0;
		basic_if.slverr <=  1'b0;

		// Configure assertions
		vpiw.disable_all_assertions();
		vpiw.enable_assertion("ENABLE_SVA");
		
		// Drive the signals according to specific scenarios
		@(posedge basic_if.clk);
		
		repeat(2) begin
			@(posedge basic_if.clk);
			vpiw.check_sva_passed("ENABLE_SVA", "The check should have passed.");
		end
		
		// Trigger error
		basic_if.sel    <= 1'b1;
		basic_if.enable <= 1'b1;
			
		@(posedge basic_if.clk);
		vpiw.check_sva_failed("ENABLE_SVA", "The check should have failed.");
		
		// Remove the error
		basic_if.sel <= 1'b0;
		@(posedge basic_if.clk);
		vpiw.check_sva_failed("ENABLE_SVA", "The check should have passed.");
		
		`uvm_info(get_test_name(), "end of the run phase", UVM_LOW)
	endtask
endclass


`endif
