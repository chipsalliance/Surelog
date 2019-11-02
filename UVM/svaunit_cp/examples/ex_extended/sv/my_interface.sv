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
 * NAME:        my_interface.sv
 * PROJECT:     svaunit
 * Description: Example of one interface with a single SVA
 *******************************************************************************/

`ifndef MY_INTERFACE_SV
`define MY_INTERFACE_SV

`include  "nested_interface.sv"

// Example of one interface with a single SVA
interface my_interface (input clk);
	import uvm_pkg::*;
	`include "uvm_macros.svh"

	// nested_interface instance
	nested_interface nested_if(.clk(clk));

	// Signals
	logic pattern;
	logic load;

	// Property definition for valid load and pattern values
	property my_sva_property;
		@(posedge clk)
			load |-> pattern;
	endproperty
	// Check that if load is 1 on a clock cycle, pattern is also 1
	MY_SVA: assert property (my_sva_property) else
		`uvm_error("MY_SVA", "If load is 1, pattern should also be 1")

endinterface

`endif
