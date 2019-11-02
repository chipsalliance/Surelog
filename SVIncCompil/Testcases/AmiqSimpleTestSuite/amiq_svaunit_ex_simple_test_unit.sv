
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
 * NAME:        amiq_svaunit_ex_simple_test_unit.sv
 * PROJECT:     svaunit
 * Description: Unit test used to verify AN_SVA
 *******************************************************************************/

`ifndef AMIQ_SVAUNIT_EX_SIMPLE_TEST_UNIT_SV
`define AMIQ_SVAUNIT_EX_SIMPLE_TEST_UNIT_SV

// Unit test used to verify the AN_SVA
class amiq_svaunit_ex_simple_test_unit extends svaunit_test;
   `uvm_component_utils(amiq_svaunit_ex_simple_test_unit)

   // Pointer to sequence used to check a scenario
   local amiq_svaunit_ex_simple_test_sequence sequence_random;

   /* Constructor for amiq_svaunit_ex_simple_test_unit
    * @param name   : instance name for amiq_svaunit_ex_simple_test_unit object
    * @param parent : hierarchical parent for amiq_svaunit_ex_simple_test_unit
    */
   function new(string name = "amiq_svaunit_ex_simple_test_unit", uvm_component parent);
      super.new(name, parent);
   endfunction

   /* Build phase method used to instantiate components
    * @param phase : the phase scheduled for build_phase method
    */
   virtual function void build_phase(input uvm_phase phase);
      super.build_phase(phase);

      sequence_random = amiq_svaunit_ex_simple_test_sequence::type_id::create("sequence_random", this);
   endfunction

   // Create scenarios for AN_SVA
   virtual task test();
      sequence_random.start(sequencer);
   endtask
endclass

`endif
