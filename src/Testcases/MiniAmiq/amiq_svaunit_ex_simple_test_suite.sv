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
 * NAME:        amiq_svaunit_ex_simple_test_suite.sv
 * PROJECT:     svaunit
 * Description: SVAUnit test suite
 *******************************************************************************/

`ifndef AMIQ_SVAUNIT_EX_SIMPLE_TEST_SUITE_SV
`define AMIQ_SVAUNIT_EX_SIMPLE_TEST_SUITE_SV

`include "../svaunit/sv/svaunit_defines.svh"

// Unit test suite for a simple example
class amiq_svaunit_ex_simple_test_suite extends svaunit_test_suite;
   `uvm_component_utils(amiq_svaunit_ex_simple_test_suite)

   /* Constructor for amiq_svaunit_ex_simple_test_suite
    * @param name   : instance name for amiq_svaunit_ex_simple_test_suite object
    * @param parent : hierarchical parent for amiq_svaunit_ex_simple_test_suite
    */
   function new(string name = "amiq_svaunit_ex_simple_test_suite", uvm_component parent);
      super.new(name, parent);
   endfunction

   /* Build phase method used to instantiate components
    * @param phase : the phase scheduled for build_phase method
    */
   virtual function void build_phase(input uvm_phase phase);
      super.build_phase(phase);

      // Register unit tests and sequences to test suite
      `add_test(amiq_svaunit_ex_simple_test_unit)
      `add_test(amiq_svaunit_ex_simple_test_with_parameter#(10))
      `add_test(amiq_svaunit_ex_simple_test_head_sequence)
      `add_test(amiq_svaunit_ex_simple_test_sequence)
      `add_test(amiq_svaunit_ex_simple_test_sequence)
   endfunction
endclass

`endif

