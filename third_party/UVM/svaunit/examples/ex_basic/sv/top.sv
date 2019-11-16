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
 * Description: Top for a basic example with an SVA
 *******************************************************************************/

`ifndef BASIC_TOP_SV
`define BASIC_TOP_SV

`include "amiq_svaunit_ex_basic_pkg.sv"
`timescale 1ns/1ps

module top;
	`SVAUNIT_UTILS
	import amiq_svaunit_ex_basic_pkg::*;

	reg clock;

	// basic_interface instance
	basic_interface basic_if(.clk(clock));

	initial begin
		// Set clock initial value
		clock = 1'b0;
		
		// Initialize my_if signals
		basic_if.enable <= 1'b0;
		basic_if.sel <= 1'b0;
		basic_if.ready <= 1'b0;
		basic_if.slverr <= 1'b0;

		// Register references to the virtual interfaces to config_db
		uvm_config_db#(virtual basic_interface)::set(uvm_root::get(), "*", "BASIC_IF", basic_if);

		// Start test specified with UVM_TESTNAME
		run_test();
	end

	// Clock generation
	always begin
		#5ns clock = ~clock;
	end
endmodule

`endif
