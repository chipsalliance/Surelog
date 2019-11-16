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
 * NAME:        nested_interface.sv
 * PROJECT:     svaunit
 * Description: Example of nested interface
 *******************************************************************************/

`ifndef ANOTHER_INTERFACE_SV
`define ANOTHER_INTERFACE_SV

// Example of nested interface
interface nested_interface (input clk);
	import uvm_pkg::*;
	`include "uvm_macros.svh"

	//Select signal
	logic read;

	//Enable signal
	logic read_and_clear;

	//Property definition for valid read and read_and_clear values
	property my_sva_property;
		@(posedge clk)
			~(read & read_and_clear);
	endproperty
	//Check that read and read_and_clear can not be 1 simultaneously
	MY_NESTED_SVA: assert property (my_sva_property) else
		`uvm_error("MY_NESTED_SVA", "read and read_and_clear can not be asserted simultaneously")

endinterface

`endif

