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
 * NAME:        top.sv
 * PROJECT:     svaunit
 * Description: Top for an advanced example with an SVA
 *******************************************************************************/

`ifndef TOP_SV
`define TOP_SV

`include "amiq_svaunit_ex_extended_pkg.sv"
`timescale 1ns/1ps


module top;
	`SVAUNIT_UTILS
	import amiq_svaunit_ex_extended_pkg::*;

	reg clock;

	// my_interface instance
	my_interface my_if(.clk(clock));

	initial begin
		// Set clock initial value
		clock = 1'b0;
		
		// Register references to the virtual interfaces to config_db
		uvm_config_db#(virtual my_interface)::set(uvm_root::get(), "*", "MY_IF", my_if);
		uvm_config_db#(virtual nested_interface)::set(uvm_root::get(), "*", "MY_NESTED_IF", my_if.nested_if);

		// Start test specified with UVM_TESTNAME
		run_test();
	end

	// Clock generation
	always begin
		#5ns clock = ~clock;
	end
endmodule

`endif
