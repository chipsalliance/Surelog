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
 * NAME:        amiq_svaunit_ex_extended_test_sequence.sv
 * PROJECT:     svaunit
 * Description: Unit test used to verify MY_SVA
 *******************************************************************************/

`ifndef AMIQ_SVAUNIT_EX_EXTENDED_TEST_SEQUENCE_SV
`define AMIQ_SVAUNIT_EX_EXTENDED_TEST_SEQUENCE_SV

// Unit test used to verify the MY_SVA
class amiq_svaunit_ex_extended_test_sequence extends svaunit_test;
	`uvm_component_utils(amiq_svaunit_ex_extended_test_sequence)

	/* Constructor for amiq_svaunit_ex_extended_test_sequence
	 * @param name   : instance name for amiq_svaunit_ex_extended_test_sequence object
	 * @param parent : hierarchical parent for amiq_svaunit_ex_extended_test_sequence
	 */
	function new(string name = "amiq_svaunit_ex_extended_test_sequence", uvm_component parent);
		super.new(name, parent);
	endfunction

	// Pointer to sequence used to check a scenario
	local amiq_svaunit_ex_extended_sequence seq;

	virtual function void build_phase(input uvm_phase phase);
		super.build_phase(phase);

		// Create the sequence
		seq = amiq_svaunit_ex_extended_sequence::type_id::create("seq", this);
	endfunction

	// Create scenarios for MY_SVA
	virtual task test();
		seq.start(sequencer);
	endtask
endclass

`endif
