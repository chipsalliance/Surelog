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
 * NAME:        svaunit_sequence.svh
 * PROJECT:     svaunit
 * Description: SVAUnit sequencer class definition and SVAUnit base sequence calss definition
 *******************************************************************************/

`ifndef SVAUNIT_SEQUENCE_SVH
`define SVAUNIT_SEQUENCE_SVH

// SVAUnit sequencer class
class svaunit_sequencer extends uvm_virtual_sequencer;
   `uvm_component_utils(svaunit_sequencer)

   // Pointer to VPI wrapper component
   svaunit_vpi_wrapper vpiw;

   /* Constructor for an svaunit_sequencer
    * @param name   : instance name for svaunit_sequencer object
    * @param parent : hierarchical parent for svaunit_sequencer
    */
   function new(string name = "svaunit_sequencer", uvm_component parent);
      super.new(name, parent);
   endfunction

   /* Build phase method used to instantiate components
    * @param phase : the phase scheduled for build_phase method
    */
   virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      // Get the VPI wrapper from UVM config db
      if (!uvm_config_db#(svaunit_vpi_wrapper)::get(uvm_root::get(), "*", "VPIW", vpiw)) begin
         `uvm_fatal("SVAUNIT_NO_VPIW_SEQUENCER_ERR",
            "SVAUnit VPI wrapper for the %s SVAUnit sequencer is not set! Please enable SVAUnit package!")
      end
      
   endfunction
endclass

// SVAUnit base virtual sequence
class svaunit_base_sequence extends uvm_sequence;
   `uvm_object_utils(svaunit_base_sequence)
   `uvm_declare_p_sequencer(svaunit_sequencer)

   // Pointer to VPI wrapper
   svaunit_vpi_wrapper vpiw;

   // When this bit is 1, the sequence should stop
   bit stop_test;

   // Stores the name of the test where this sequence is added
   local string test_name;

   // Stores all tests names which started from this sequence
   local string child_name[$];

   // List of immediate assertions tested during a specific test
   local svaunit_immediate_assertion_info lof_checks[$];

   // Stores the fact that the list with checks was updated or not
   local bit update_lof_checks;

   /* Constructor for svaunit_base_sequence
    * @param name   : instance name for svaunit_base_sequence object
    */
   function new(string name = "svaunit_base_sequence");
      super.new(name);

      // Get the VPI wrapper from UVM config db
      if (!uvm_config_db#(svaunit_vpi_wrapper)::get(uvm_root::get(), "*", "VPIW", vpiw)) begin
         `uvm_fatal("SVAUNIT_NO_VPIW_SEQUENCER_ERR",
            "SVAUnit VPI wrapper for the %s SVAUnit sequencer is not set! Please enable SVAUnit package!")
      end

      update_lof_checks = 0;
      stop_test = 0;
   endfunction

   /* Get stop bit for test
    * @return the stop bit for test
    */
   virtual function bit get_stop();
      return stop_test;
   endfunction
   

   /* Get a list with all immediate assertions tested into tests
    * @param a_checks : a list with all immediate assertions tested
    */
   local function void get_checks(ref svaunit_immediate_assertion_info a_checks[$]);
      if(update_lof_checks == 0) begin
         vpiw.get_checks_for_test(get_test_name(), a_checks);

         // Get the checks used in each test
         foreach(child_name[child_index]) begin
            vpiw.get_checks_for_test(child_name[child_index], a_checks);
         end

         update_lof_checks = 1;
      end
   endfunction

   /* Form the test topology as a tree
    * @param a_level : the level where the test is created
    * @return a string representing the tree
    */
   virtual function string form_tree(int a_level);
      string extra = "";
      string report = "";

      for(int level_idx = 0; level_idx < (a_level - 1); level_idx++) begin
         extra = {"\t", extra};
      end

      if(a_level == 0) begin
         extra = {"\t", extra};
      end

      report = {extra, get_test_name()};

      foreach(child_name[index]) begin
         extra = "";
         for(int level_idx = 0; level_idx < (a_level + index + 2) ; level_idx++) begin
            extra = {"\t", extra};
         end

         report = {report, "\n", extra, child_name[index]};
      end

      return report;
   endfunction

   // This task is called before the optional execution of pre_body and it is used to set the test name
   virtual task pre_start();
      uvm_sequence_base parent;
      svaunit_base_sequence seq_parent;
      string current_test_name;

      super.pre_start();

      parent = get_parent_sequence();

      if(parent != null) begin
         if(parent.get_name() == "") begin
            current_test_name = $sformatf("%s", get_name());
         end else begin
            if(parent.get_name() == "uvm_test_top") begin
               current_test_name = $sformatf("%s.%s", parent.get_type_name(), get_name());
            end else begin
               if(get_name() == "uvm_test_top") begin
                  current_test_name = $sformatf("%s", get_name());
               end else begin
                  if($cast(seq_parent, parent)) begin
                     current_test_name = $sformatf("%s.%s", seq_parent.get_test_name(), get_name());

                     child_name.push_back($sformatf("%s", current_test_name));
                     set_child_name(child_name[child_name.size() - 1]);
                  end
               end
            end
         end
      end else begin
         current_test_name = get_name();
      end

      set_test_name(current_test_name);
      vpiw.set_test_name_vpi(current_test_name);

      begin
         uvm_component seqr_parent = p_sequencer.get_parent();
         svaunit_base test;

         if($cast(test, seqr_parent)) begin
            test.sequence_name.push_back(current_test_name);
         end
      end
   endtask

   // Print a report for all checks tested for the current unit test
   virtual function void print_checks();
      get_checks(lof_checks);
      vpiw.print_checks_from_specific_list(get_test_name(), lof_checks);
   endfunction

   // Print a report for all checks tested for the SVAs
   virtual function void print_sva_and_checks();
      string a_test_name = get_test_name();

      get_checks(lof_checks);
      vpiw.print_sva_and_checks_for_specific_list(a_test_name, lof_checks);
   endfunction

   // Print a report for all SVA which have failed
   virtual function void print_failed_sva();
      string crt_test_name = get_test_name();

      get_checks(lof_checks);
      vpiw.print_failed_sva_for_specific_list(crt_test_name, lof_checks);
   endfunction

   // Print the SVAUnit topology
   virtual function void print_tree();
      string report = "";
      get_checks(lof_checks);

      report = $sformatf("\n%s", form_tree(0));

      `uvm_info(get_test_name(), report, UVM_LOW)
   endfunction

   // Print information about SVAUNIT checks
   virtual function void print_tests();
      get_checks(lof_checks);
   endfunction

   // Print status of test
   virtual function void print_status();
      get_checks(lof_checks);
   endfunction

   /* Get the names of the SVAs which were tested during test
    * @param a_tested_sva_names : the names of the SVAs which were tested during test
    */
   local function void get_sva_tested_names(ref string a_tested_sva_names[$]);
      svaunit_concurrent_assertion_info tested_sva[$];
      
      foreach(child_name[child_index]) begin
         vpiw.get_sva_tested(child_name[child_index], tested_sva);
         vpiw.get_sva_tested_names(tested_sva, a_tested_sva_names);
      end
   endfunction

   /* Get the names of the SVAs which were not tested during test
    * @param a_not_tested_sva : the names of the SVAs which were not tested during test
    */
   local function void get_sva_not_tested_names(ref string a_not_tested_sva[$]);
      // Variable used to store the names of the SVA which were tested
      string tested_sva_names[$];

      // Variable used to store the names of the SVA which were tested/per test
      string lof_not_tested_sva[$];

      int not_tested_index[$];
      int n_tested_index[$];
      
      svaunit_concurrent_assertion_info not_tested_sva[$];
      
      foreach(child_name[child_index]) begin
         vpiw.get_sva_not_tested(child_name[child_index], not_tested_sva);
         vpiw.get_sva_not_tested_names(not_tested_sva, lof_not_tested_sva);
      end

      // Get tested SVAs
      get_sva_tested_names(tested_sva_names);

      foreach(lof_not_tested_sva[sva_index]) begin
         n_tested_index = tested_sva_names.find_index() with (item == lof_not_tested_sva[sva_index]);

         if(n_tested_index.size() == 0) begin
            not_tested_index = a_not_tested_sva.find_index() with
            (item == lof_not_tested_sva[sva_index]);

            if(not_tested_index.size() == 0) begin
               a_not_tested_sva.push_back(lof_not_tested_sva[sva_index]);
            end
         end
      end
   endfunction

   // Print a list with all SVAs
   virtual function void print_sva();
      // Variable used to store the report string
      string report = "";

      // Variable used to store the SVA names which were tested
      string tested_sva_names[$];

      // Variable used to store the SVA names which were not tested
      string not_tested_sva[$];

      // Variable used to store the number of tested SVA
      int unsigned nof_tested_sva;

      // Variable used to store the number of not tested SVA
      int unsigned nof_not_tested_sva;

      get_sva_tested_names(tested_sva_names);
      get_sva_not_tested_names(not_tested_sva);

      nof_tested_sva = tested_sva_names.size();
      nof_not_tested_sva = not_tested_sva.size();

      // Form report string
      report = $sformatf("\n\n-------------------- %s : SVAs statistics --------------------\n", get_test_name());
      report = $sformatf("%s\n\t%0d/%0d SVA were exercised",
         report, nof_tested_sva, nof_not_tested_sva + nof_tested_sva);

      foreach(tested_sva_names[index]) begin
         report = $sformatf("%s\n\t\t%s", report, tested_sva_names[index]);
      end

      // Verify if there were SVAs which have not been tested. In this case, in the report will appear also the SVAs
      // which were not tested
      if(nof_not_tested_sva > 0) begin
         report = $sformatf("%s\n\n\t%0d SVA were not exercised", report, nof_not_tested_sva);

         foreach(not_tested_sva[index]) begin
            report = $sformatf("%s\n\t\t%s", report, not_tested_sva[index]);
         end
      end

      report = $sformatf("%s\n", report);

      `uvm_info(get_test_name(), report, UVM_LOW)
   endfunction

   // Print report for current test suite
   virtual function void print_report();
      get_checks(lof_checks);

      print_tree();
      print_status();
      print_tests();
      print_sva();
      print_checks();
      print_sva_and_checks();
      print_failed_sva();
   endfunction

   /* Add child name into parent list
    * @param a_child_name : the child name to be added inside list
    */
   local function void set_child_name(string a_child_name);
      uvm_sequence_base parent;
      svaunit_base_sequence seq_parent;

      parent = get_parent_sequence();

      if(parent != null) begin
         if($cast(seq_parent, parent)) begin
            seq_parent.child_name.push_back($sformatf("%s",a_child_name));
            seq_parent.set_child_name(a_child_name);
         end
      end
   endfunction


   /* Set the name of the test where the sequence is registered
    * @param a_test_name : the test name to de added
    */
   local function void set_test_name(string a_test_name);
      test_name = a_test_name;
   endfunction

   /* Get the name of the test where the sequence is registered
    * @return the test name
    */
   virtual function string get_test_name();
      return test_name;
   endfunction

   // Will start a scenario
   virtual task body();
      `uvm_info(get_test_name(), "Start a new sequence", UVM_LOW)
   endtask
endclass

`endif
