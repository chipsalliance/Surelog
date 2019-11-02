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
 * MODULE:       svaunit_sequence_test.svh
 * PROJECT:      svaunit
 * Description:  svaunit test class which starts a sequence
 *******************************************************************************/

`ifndef SVAUNIT_SEQUENCE_TEST_SVH
`define SVAUNIT_SEQUENCE_TEST_SVH

/* SVAUnit test class which starts a sequence
 * SEQ_TYPE : sequence type used to check a scenario
 */
class svaunit_sequence_test#(type SEQ_TYPE=svaunit_base_sequence) extends svaunit_test;
   `uvm_component_param_utils(svaunit_sequence_test#(SEQ_TYPE))

   // Sequence which contains the SVA scenario
   SEQ_TYPE seq;

   /* Constructor for svaunit_sequence_test
    * @param name   : instance name for svaunit_sequence_test object
    * @param parent : hierarchical parent for svaunit_sequence_test
    */
   function new(string name="svaunit_sequence_test", uvm_component parent);
      super.new(name, parent);
   endfunction

   // Will set the name of the current test
   virtual function void set_name_for_test();
      update_test_name(seq.get_test_name());
   endfunction

   /* Form the test topology as a tree
    * @param a_level : the level where the test is created
    * @return a string representing the tree
    */
   virtual function string form_tree(int a_level);
      string extra = "";

      for(int level_idx = 0; level_idx < a_level; level_idx++) begin
         extra = {"\t", extra};
      end

      return $sformatf("%s%s", extra, seq.form_tree(a_level));
   endfunction

   // Task used to start testing - a sequence will be started here
   virtual task test();
      if(!seq.randomize()) begin
         `uvm_error("SVAUNIT_SEQUENCE_TEST_RANDOMIZE_ERR",
            $sformatf("The sequence for %s could not be randomize", get_test_name()))
      end
      seq.start(sequencer);
   endtask
endclass

`endif
