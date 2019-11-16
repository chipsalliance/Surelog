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
 * NAME:        basic_interface.sv
 * PROJECT:     svaunit
 * Description: Example of one interface with two simple SVAs
 *******************************************************************************/

`ifndef BASIC_INTERFACE_SV
`define BASIC_INTERFACE_SV


interface basic_interface(input clk);
	import uvm_pkg::*;
	`include "uvm_macros.svh"

	// Select signal
	logic sel;

	// Enable signal
	logic enable;

	// Ready signal
	logic ready;

	// Error signal
	logic slverr;

	// Property definition for valid slverr value when one of sel, enable, ready signal is de-asserted
	property slverr_property;
		@(posedge clk)
			!sel || !enable || !ready |-> !slverr;
	endproperty
	// Check that slverr is LOW when one of sel, enable or ready is LOW
	SLVERR_SVA: assert property(slverr_property) else
		`uvm_error("SLVERR_SVA", "slverr must be LOW when one of sel, enable or ready is LOW.")

	// Property definition for valid enable and sel values
	property enable_property;
		@(posedge clk)
			~(enable & sel);
	endproperty
	// Check that enable and sel can not be asserted simultaneously
	ENABLE_SVA: assert property(enable_property) else
		`uvm_error("ENABLE_SVA", "enable and sel can not be asserted simultaneously.")

endinterface

`endif
