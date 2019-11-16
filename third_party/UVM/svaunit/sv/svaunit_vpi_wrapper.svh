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
 * MODULE:       svaunit_vpi_wrapper.svh
 * PROJECT:      svaunit
 * Description:  VPI wrapper - it contains a pointer to VPI interface and SVAUnit API's
 *******************************************************************************/

`ifndef SVAUNIT_VPI_WRAPPER_SVH
`define SVAUNIT_VPI_WRAPPER_SVH

//  VPI wrapper - it contains a pointer to VPI interface and SVAUnit API's
class svaunit_vpi_wrapper extends uvm_object;

   // Pointer to VPI interface with SVAs, imports and exports to VPI API
   virtual svaunit_vpi_interface vpi_vif;

   // String with the name of the test which is currently running
   local string test_name;

   // Provide implementations of virtual methods such as get_type_name and create
   `uvm_object_utils(svaunit_vpi_wrapper)

   // List of string which represents all the immediate assertions which can be tested
   local const string LOF_ALL_SVAUNIT_CHECKS[9];

   // List of immediate assertions tested during a specific test
   local svaunit_immediate_assertion_info lof_checks[$];

   // When this bit is 1, the test should stop
   bit stop_test;

   // Stores the current status of the check used
   svaunit_status_type current_check_status;

   /* Constructor for an svaunit_vpi_wrapper
    * @param name   : instance name for svaunit_vpi_wrapper object
    */
   function new(string name = "svaunit_vpi_wrapper");
      super.new(name);

      // Get the VPI interface from UVM config db
      if (!uvm_config_db#(virtual svaunit_vpi_interface)::get(uvm_root::get(), "*", "VPI_VIF", vpi_vif)) begin
         `uvm_fatal("SVAUNIT_VPI_WRAPPER_NO_VIF_ERR",
            "SVAUnit VPI interface for vpi_wrapper class is not set! Please enable SVAUnit package!")
      end

      LOF_ALL_SVAUNIT_CHECKS = '{
         "CHECK_SVA_EXISTS",
         "CHECK_SVA_ENABLED",
         "CHECK_SVA_DISABLED",
         "CHECK_SVA_PASSED",
         "CHECK_SVA_FAILED",
         "CHECK_SVA_FINISHED",
         "CHECK_SVA_NOT_FINISHED",
         "CHECK_ALL_SVA_PASSED",
         "CHECK_THAT"
      };

      current_check_status = SVAUNIT_DID_NOT_RUN;
   endfunction

   // Update the test's status according to the number of failed assertions
   virtual function void update_coverage();
      // Update status for SVA coverage
      vpi_vif.update_coverage(test_name);
   endfunction

   /* Will return the name of the test where the VPI wrapper is instantiated
    * @return a string with the name of the test where this component is instantiated
    */
   virtual function string get_test_name();
      return test_name;
   endfunction

   /* Set test name in VPI interface
    * @param a_test_name : the name of the test to be added inside VPI interface
    */
   virtual function void set_test_name_vpi(string a_test_name);
      test_name = a_test_name;

      vpi_vif.set_test_name(a_test_name);
   endfunction

   // {{{ Functions used for immediate assertions

   /* Create the list of immediate assertion if it doesn't exist any with the given name
    * @param a_sva : the SVA which was tested with immediate assertion
    * @param a_check_name : immediate assertion to be added
    * @param a_time : current time at which the immediate assertion has been tested
    * @param a_status : current status of the immediate assertion tested
    */
   local function void add_check(svaunit_concurrent_assertion_info a_sva, string a_check_name,
         time a_time, svaunit_status_type a_status);

      // Stores the fact that the SVA was tested before or not
      int check_index[$];

      // Verify if SVA was tested before or not - in this case add new detail to immediate assertion list
      check_index = lof_checks.find_index() with (item.get_sva_tested() == a_sva);

      if(check_index.size() > 0) begin
         foreach(check_index[index]) begin
            lof_checks[check_index[index]].add_new_check_detail(a_check_name, test_name, a_time, a_status);
         end
      end else begin
         svaunit_immediate_assertion_info check = svaunit_immediate_assertion_info::type_id::create($sformatf(
               "%s_immediate_assertions_%0d", get_name(), lof_checks.size() - 1));
         check.set_sva(a_sva);
         check.add_new_check_detail(a_check_name, test_name, a_time, a_status);

         lof_checks.push_back(check);
      end
   endfunction

   /* Get the immediate assertion info which corresponds to a given SVA
    * @param a_sva_name : a string represents the SVA name used to select the immediate assertion
    * @return the immediate assertion info which corresponds to a given SVA
    */
   virtual function svaunit_immediate_assertion_info get_check_for_sva(string a_sva_name);
      svaunit_immediate_assertion_info checks[$];

      checks = lof_checks.find_first() with (item.sva_tested.get_sva_name() == a_sva_name);

      return checks[0];
   endfunction

   /* Get the immediate assertions info which corresponds to a given test
    * @param a_test_name : a string represents the test name used to select the immediate assertion
    * @param a_checks_for_test : a list of immediate assertions info which corresponds to a given test
    */
   virtual function void get_checks_for_test(string a_test_name,
         ref svaunit_immediate_assertion_info a_checks_for_test[$]);

      foreach(lof_checks[check_index]) begin
         svaunit_immediate_assertion_info check = lof_checks[check_index].get_checks(a_test_name);

         if(check != null) begin
            int test_check_index[$];

            if(lof_checks[check_index].sva_tested != null) begin
               test_check_index = a_checks_for_test.find_index()
               with (item.sva_tested.get_sva_name() == check.sva_tested.get_sva_name());

               if(test_check_index.size() > 0) begin
                  foreach(test_check_index[index]) begin
                     foreach(check.checks_details[details_index]) begin
                        // Add new detail to this check
                        for(int time_idx = 0;
                              time_idx < check.checks_details[details_index].attempt_time.size(); time_idx++) begin
                           a_checks_for_test[test_check_index[index]].add_new_check_detail(
                              check.checks_details[details_index].get_check_name(),
                              a_test_name,
                              check.checks_details[details_index].attempt_time[time_idx],
                              check.checks_details[details_index].check_states[time_idx]);
                        end
                     end
                  end
               end else begin
                  a_checks_for_test.push_back(check);
               end
            end
         end
      end
   endfunction

   /* Get a list with names for all immediate assertion used
    * @param a_lof_used_checks : list of immediate assertions from where the report is made
    * @param a_lof_used_checks_names : list which contains the names of the checks used in this unit test
    */
   virtual function void get_checks_names(ref svaunit_immediate_assertion_info a_lof_used_checks[$],
         ref string a_lof_used_checks_names[$]);
      foreach(a_lof_used_checks[check_index]) begin
         foreach(a_lof_used_checks[check_index].checks_details[detail_index]) begin
            int indexes[$];

            indexes =  a_lof_used_checks_names.find_index() with (
                  a_lof_used_checks[check_index].checks_details[detail_index].get_check_name() == item);

            if(indexes.size() == 0) begin
               a_lof_used_checks_names.push_back(
                  a_lof_used_checks[check_index].checks_details[detail_index].get_check_name());
            end
         end
      end
   endfunction

   /* Get a list with names for all immediate assertion used which were not used
    * @param a_lof_used_checks : list of immediate assertions from where the report is made
    * @param a_lof_not_used_checks_names : list which contains the name of the checks not used in this unit test
    */
   virtual function void get_checks_not_used_names(ref svaunit_immediate_assertion_info a_lof_used_checks[$],
         ref string a_lof_not_used_checks_names[$]);
      // Variable used to store the indexes of the elements from a list which satisfied a given condition
      int check_index[$];

      // Variable used to store the indexes of the elements from a list which satisfied a given condition
      int string_index[$];

      // Iterate all over the lof_all_svaunit_checks to see if the check was used or not
      foreach(LOF_ALL_SVAUNIT_CHECKS[name_index]) begin

         // Iterate all over the immediate assertions used and all over the details to see if exits or not
         check_index = a_lof_used_checks.find_index() with (item.check_exists(LOF_ALL_SVAUNIT_CHECKS[name_index]));

         // If it was not found the check iterate all over the string queue to see if already exists in that list
         if(check_index.size() == 0) begin
            // Verify if the string exists or not
            string_index = a_lof_not_used_checks_names.find_index() with (item == LOF_ALL_SVAUNIT_CHECKS[name_index]);

            // If the string does not exists add to the string queue it's name
            if(string_index.size() == 0) begin
               a_lof_not_used_checks_names.push_back(LOF_ALL_SVAUNIT_CHECKS[name_index]);
            end
         end
      end
   endfunction

   /* Get immediate assertions from all tests
    * @return the total number of immediate assertions
    */
   virtual function int unsigned get_total_nof_checks();
      return lof_checks.size();
   endfunction

   /* Get the number of times an immediate assertion was tested during simulation
    * @param a_check_name : the check name
    * @param a_lof_used_checks : list of immediate assertions from where the report is made
    * @return the number of times an immediate assertion was tested during simulation
    */
   virtual function int unsigned get_nof_times_check_was_tested(string a_check_name,
         ref svaunit_immediate_assertion_info a_lof_used_checks[$]);
      // Variable used to store the number of times a check was tested
      int unsigned nof_times_check_was_tested = 0;

      // Iterate over the check list and it's detail to see if the given check name was tested and
      // increase the number with the proper number of times the check was tested
      foreach(a_lof_used_checks[check_index]) begin
         foreach(a_lof_used_checks[check_index].checks_details[details_index])begin
            if(a_lof_used_checks[check_index].checks_details[details_index].get_check_name() == a_check_name) begin
               nof_times_check_was_tested = nof_times_check_was_tested +
               a_lof_used_checks[check_index].checks_details[details_index].get_nof_times_check_was_tested();
            end
         end
      end

      return nof_times_check_was_tested;
   endfunction

   /* Get the number of times an immediate assertion passed during simulation
    * @param a_check_name : the check name
    * @param a_lof_used_checks : list of immediate assertions from where the report is made
    * @return the number of times an immediate assertion passed during simulation
    */
   virtual function int unsigned get_nof_times_check_has_passed(string a_check_name,
         ref svaunit_immediate_assertion_info a_lof_used_checks[$]);
      // Variable used to store the number of times a check has passed
      int unsigned nof_times_check_has_passed = 0;

      // Iterate over the check list and it's detail to see if the given check name was tested and
      // increase the number with the proper number of times the check has tested
      foreach(a_lof_used_checks[check_index]) begin
         foreach(a_lof_used_checks[check_index].checks_details[details_index])begin
            if(a_lof_used_checks[check_index].checks_details[details_index].get_check_name() == a_check_name) begin
               nof_times_check_has_passed = nof_times_check_has_passed +
               a_lof_used_checks[check_index].checks_details[details_index].get_nof_times_check_has_passed();
            end
         end
      end

      return nof_times_check_has_passed;
   endfunction
   // }}}

   // {{{ Functions used to find out SVA properties

   /* Get an assertion with a path from list
    * @param a_sva_path : assertion path to be found in SVA list
    * @return the assertion from SVA list
    */
   local function svaunit_concurrent_assertion_info get_assertion_by_path(string a_sva_path);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = vpi_vif.get_assertion_from_path(a_sva_path);

      // Verify that the SVA exists or not
      check_sva_exists(a_sva_path, $sformatf("Assertion %s doesn't exist.", a_sva_path));

      return assertion;
   endfunction

   /* Get an assertion with a name from list
    * @param a_sva_name : assertion name to be found in SVA list
    * @return the assertion from SVA list
    */
   local function svaunit_concurrent_assertion_info get_assertion_by_name(string a_sva_name);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = vpi_vif.get_assertion_by_name(a_sva_name);

      // Verify that the SVA exists or not
      check_sva_exists(a_sva_name, $sformatf("Assertion %s doesn't exist.", a_sva_name));

      return assertion;
   endfunction

   /* Get an assertion with a given name or path from list
    * @param a_sva : the assertion name or path to be found in SVA list
    * @return the assertion from SVA list
    */
   virtual function svaunit_concurrent_assertion_info get_assertion(string a_sva);
      if(is_a_path(a_sva)) begin
         return get_assertion_by_path(a_sva);
      end else begin
         return get_assertion_by_name(a_sva);
      end
   endfunction


   /* Verify that the SVA with a given name or path succeeded
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @return 1 if the assertion succeeded and 0 otherwise
    */
   virtual function bit assertion_succeeded(string a_sva_name);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.sva_passed();
      end else begin
         return 0;
      end
   endfunction


   /* Get the state of an SVA with a given name or path
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @return the state of assertion
    */
   virtual function svaunit_concurrent_assertion_state_type get_state(string a_sva_name);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.get_sva_state();
      end else begin
         return svaunit_concurrent_assertion_state_type'(0);
      end
   endfunction

   /* Verify that an SVA with a given name or path has finished
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @return 1 if the assertion has finished and 0 otherwise
    */
   virtual function bit is_finished(string a_sva_name);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.sva_finished();
      end else begin
         return 0;
      end
   endfunction

   /* Verify that an SVA with a given name or path has not finished
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @return 1 if the assertion has not finished and 0 otherwise
    */
   virtual function bit is_not_finished(string a_sva_name);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.sva_not_finished();
      end else begin
         return 0;
      end
   endfunction

   /* Verify that an SVA with a given name or path is enable
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @return 1 if the assertion is enable and 0 otherwise
    */
   virtual function bit is_enable(string a_sva_name);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.sva_enabled(get_test_name());
      end else begin
         return 0;
      end
   endfunction

   /* Compute the number of times an SVA with a given name or path has failed
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @return the number of times an assertion failed
    */
   virtual function int get_nof_times_assertion_failed(string a_sva_name);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.get_nof_times_sva_fails();
      end else begin
         return -1;
      end
   endfunction

   /* Compute the number of times an SVA with a given name or path succeeded
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @return the number of times an assertion succeeded
    */
   virtual function int get_nof_times_assertion_succeeded(string a_sva_name);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         return assertion.get_nof_times_sva_succeeded();
      end else begin
         return -1;
      end
   endfunction

   /* Get a list of all SVAs which have been tested from a_test_name
    * @param a_test_name : the name of the test where the SVA was exercised
    * @param a_sva_tested : a list of all SVAs which have the same tested status
    */
   virtual function void get_sva_tested(string a_test_name, ref svaunit_concurrent_assertion_info a_sva_tested[$]);
      foreach(vpi_vif.sva_info[index]) begin
         if(vpi_vif.sva_info[index].was_tested(a_test_name) == SVAUNIT_WAS_TESTED) begin
            if(!vpi_vif.sva_exists(vpi_vif.sva_info[index].get_sva_name(),
                     vpi_vif.sva_info[index].get_sva_path(), a_sva_tested)) begin
               a_sva_tested.push_back(vpi_vif.sva_info[index]);
            end
         end
      end
   endfunction

   // Get the total number of SVAs
   virtual function int unsigned get_nof_sva();
      return vpi_vif.get_nof_sva();
   endfunction

   /* Get the total number of SVAs tested from all tests
    * @param a_test_name : the name of the test where the SVA was exercised
    * @return the total number of SVAs tested from all tests
    */
   virtual function int unsigned get_nof_tested_sva(string a_test_name);
      // Variable used to store the tested SVAs
      svaunit_concurrent_assertion_info tested_sva[$];

      // Get all SVA tested
      get_sva_tested(a_test_name, tested_sva);

      return tested_sva.size();
   endfunction

   /* Get the names of the SVAs which were tested during test
    * @param a_tested_sva : the SVAs which were tested during a given test
    * @param a_tested_sva_names : list of SVAs names which were tested during test
    */
   virtual function void get_sva_tested_names(ref svaunit_concurrent_assertion_info a_tested_sva[$],
         string a_tested_sva_names[$]);

      foreach(a_tested_sva[index]) begin
         // Variable used to store the indexes of the elements which satisfied a given condition
         int tested_sva_index[$];

         // Iterate all over the SVA names to see if the SVA name exists or not
         tested_sva_index = a_tested_sva_names.find_index() with (item == a_tested_sva[index].get_sva_path());

         // If it does not exists add into out list the SVA path
         if(tested_sva_index.size() == 0) begin
            a_tested_sva_names.push_back(a_tested_sva[index].get_sva_path());
         end
      end
   endfunction

   /* Get the names of the SVAs which were not tested during test
    * @param a_not_tested_sva : the SVAs which were not tested during a given test
    * @param a_not_tested_sva_names : list of SVAUnit checks names which have not been tested
    */
   virtual function void get_sva_not_tested_names(ref svaunit_concurrent_assertion_info a_not_tested_sva[$],
         string a_not_tested_sva_names[$]);

      // Verify if the not tested SVA name exists into out list
      foreach(a_not_tested_sva[index]) begin
         // Variable used to store the indexes of the elements which satisfied a given condition
         int not_tested_index[$];

         // Iterate all over the SVA names to see if the SVA name exists or not
         not_tested_index = a_not_tested_sva_names.find_index() with (item == a_not_tested_sva[index].get_sva_path());

         // If it does not exists add into out list the SVA path
         if(not_tested_index.size() == 0) begin
            a_not_tested_sva_names.push_back(a_not_tested_sva[index].get_sva_path());
         end
      end
   endfunction

   /* Get all SVA from all tests which have not been tested
    * @param a_test_name : the name of the test where the SVA was exercised
    * @param a_sva_not_tested : list of all SVAs which have not been tested
    */
   virtual function void get_sva_not_tested(string a_test_name,
         ref svaunit_concurrent_assertion_info a_sva_not_tested[$]);

      // Variable used to store the tested SVAs
      svaunit_concurrent_assertion_info sva_tested[$];

      // Get all SVA tested
      get_sva_tested(a_test_name, sva_tested);

      // Verify if the not tested SVA name exists into out list
      foreach(vpi_vif.sva_info[index]) begin
         // Variable used to store the indexes for the list which satisfied the given condition
         int not_tested_index[$];

         // Iterate all over the SVAs to see if the SVA exists or not
         not_tested_index = sva_tested.find_index() with (item == vpi_vif.sva_info[index]);

         // If it does not exists add into out list
         if(not_tested_index.size() == 0) begin
            a_sva_not_tested.push_back(vpi_vif.sva_info[index]);
         end
      end
   endfunction
   // }}}


   // {{{ Functions used to control SVA

   //------------------------------- RESET --------------------------------
   /* Will discard all current attempts in progress for an SVA with a given name or path
    * and resets the SVA to its initial state
    * @param a_sva_name : assertion name or path to be found in SVA list
    */
   virtual function void reset_assertion(string a_sva_name);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         vpi_vif.reset_assertion(get_test_name(), assertion);
      end
   endfunction

   // Will discard all current attempts in progress for all SVAs and resets the SVAs to initial state
   virtual function void reset_all_assertions();
      vpi_vif.reset_all_assertions(get_test_name());
   endfunction

   //------------------------------- DISABLE --------------------------------
   /* Will disable the starting of any new attempt for a given SVA
    * (this will have no effect on any existing attempts or if SVA was already disable;
    * on default all SVAs are enable)
    * @param a_sva_name : assertion name or path to be found in SVA list
    */
   virtual function void disable_assertion(string a_sva_name);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         vpi_vif.disable_assertion(get_test_name(), assertion);
      end
   endfunction

   /* Will disable the starting of any new attempt for all SVAs
    * (this will have no effect on any existing attempts or if SVA was already disable;
    * on default all SVAs are enable)
    */
   virtual function void disable_all_assertions();
      vpi_vif.disable_all_assertions(get_test_name());
   endfunction

   //------------------------------- ENABLE --------------------------------
   /* Will enable starting any new attempts for a given SVA
    * (this will have no effect if SVA was already enable or on any current attempt)
    * @param a_sva_name : assertion name or path to be found in SVA list
    */
   virtual function void enable_assertion(string a_sva_name);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         vpi_vif.enable_assertion(get_test_name(), assertion);
      end
   endfunction

   /* Will enable starting any new attempts for all SVAs
    * (this will have no effect if SVA was already enable or on any current attempt)
    */
   virtual function void enable_all_assertions();
      vpi_vif.enable_all_assertions(get_test_name());
   endfunction

   //------------------------------- KILL --------------------------------
   /* Will discard any attempts of a given SVA
    * (the SVA will remain enabled and does not reset any state used by this SVA)
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @param a_sim_time : the simulation time from which the SVA attempts will be killed
    */
   virtual function void kill_assertion(string a_sva_name, time a_sim_time);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         vpi_vif.kill_assertion(get_test_name(), assertion, a_sim_time);
      end
   endfunction

   /* Will discard any attempts of all SVAs
    * (the SVA will remain enabled and does not reset any state used by any SVA)
    * @param a_sim_time : the simulation time from which the SVA attempts will be killed
    */
   virtual function void kill_all_assertions(time a_sim_time);
      vpi_vif.kill_all_assertions(get_test_name(), a_sim_time);
   endfunction

   //------------------------------- DISABLE STEP --------------------------------
   /* Will disable step callback for a given SVA
    * (this will have no effect if step callback is not enabled or it was already disabled)
    * @param a_sva_name : assertion name or path to be found in SVA list
    */
   virtual function void disable_step_assertion(string a_sva_name);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         vpi_vif.disable_step_assertion(get_test_name(), assertion);
      end
   endfunction

   /* Will disable step callback for all SVAs
    * (this will have no effect if step callback is not enabled or it was already disabled)
    */
   virtual function void disable_step_all_assertions();
      vpi_vif.disable_step_all_assertions(get_test_name());
   endfunction

   //------------------------------- ENABLE STEP --------------------------------

   /* Will enable step callback for a given SVA
    * (by default, stepping is disabled; this will have no effect if stepping was already enabled;
    * the stepping mode cannot be modified after the assertion attempt has started)
    * @param a_sva_name : assertion name or path to be found in SVA list
    */
   virtual function void enable_step_assertion(string a_sva_name);
      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         vpi_vif.enable_step_assertion(get_test_name(), assertion);
      end
   endfunction

   /* Will enable step callback for all SVAs
    * (by default, stepping is disabled; this will have no effect if stepping was already enabled;
    * the stepping mode cannot be modified after the assertion attempt has started)
    */
   virtual function void enable_step_all_assertions();
      vpi_vif.enable_step_all_assertions(get_test_name());
   endfunction

   //------------------------------- SYSTEM RESET --------------------------------
   /* Will discard all attempts in progress for all SVAs and restore the entire assertion system to its initial state.
    * (The vpiAssertionStepSuccess and vpiAssertionStepFailure callbacks will be removed)
    */
   virtual function void system_reset_all_assertions();
      vpi_vif.system_reset_all_assertions();
   endfunction

   //------------------------------- SYSTEM ON --------------------------------
   // Will restart the SVAs after it was stopped
   virtual function void system_on_all_assertions();
      vpi_vif.system_on_all_assertions(get_test_name());
   endfunction

   //------------------------------- SYSTEM OFF --------------------------------
   // Will disable any SVA to being started and all current attempts will be considered as unterminated
   virtual function void system_off_all_assertions();
      vpi_vif.system_off_all_assertions(get_test_name());
   endfunction

   //------------------------------- SYSTEM END --------------------------------
   /* Will discard any attempt in progress and disable any SVA to be started
    * (all callbacks will be removed)
    */
   virtual function void system_end_all_assertions();
      vpi_vif.system_end_all_assertions(get_test_name());
   endfunction
   // }}}

   // {{{ Functions used to check

   /* Find the position of the first character of the first match of s2 in s1
    * @param a_s1 : the string used to search in the s2
    * @param a_s2 : the string to search for.
    * @return the position of the first character of the first match.
    *         If no matches were found, the function will return -1
    */
   virtual function int find(string a_s1, string a_s2);
      if(a_s1.len() < a_s2.len()) begin
         return -1;
      end else begin
         for(int char_index = 0; char_index < a_s1.len(); char_index = char_index + 1) begin
            if(a_s1.substr(char_index, char_index + a_s2.len() - 1) == a_s2) begin
               return char_index;
            end
         end
      end

      return -1;
   endfunction

   /* Verify if the name as a string is a path or not
    * @param a_sva_name : the name or the path given to the SVAUnit APIs
    * @return 1 if a_sva_name is actually a path and 0 if a_sva_name represents a name
    */
   local function bit is_a_path(string a_sva_name);
      if(find(a_sva_name, ".") != -1) begin
         // There was found a "." into a_sva_name -> that means that actually represents a path
         return 1;
      end else begin
         // There was not found a "." into a_sva_name -> that means that actually represents a name
         return 0;
      end
   endfunction

   /* Verify if the test should fail according to expression and increase the test statistics
    * The test will fail if the expression is false
    * @param a_expression : the expression bit
    * @return 1 if the expression is TRUE and 0 otherwise
    */
   local function bit check_expression(bit a_expression);
      // Verify if the expression is FALSE or TRUE. If it is FALSE return 0 and increase the failures number
      // else return 1
      if (a_expression) begin
         current_check_status = SVAUNIT_PASS;
         return 1;
      end else begin
         stop_test = 1;
         current_check_status = SVAUNIT_FAIL;
         return 0;
      end
   endfunction

   /* Get the status after check used
    * @return the current check status to be updated
    */
   local function svaunit_status_type get_current_check_status();
      return current_check_status;
   endfunction

   /* Check that an assertion is enabled - it will wait for the "End of time slot"
    * @param a_sva_name : the SVA name or the SVA path
    */
   local task check_assertion_is_enabled(string a_sva_name);
      vpi_vif.wait_for_eots();
      vpi_vif.get_info_from_c(get_test_name());
      check_sva_enabled(a_sva_name, $sformatf("Assertion %s is not enabled", a_sva_name));
   endtask

   // ------------------ CHECK ENABLED -------------------------
   /* Verify if a given SVA is enabled - the test will pass if SVA is not enabled
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @param a_error_msg : user error message to be printed if the check fails
    * @param a_line : the line number where the check is exercised
    * @param a_filename : the file name where the check is exercised
    */
   virtual function void check_sva_enabled(string a_sva_name, string a_error_msg = "The SVA should have been enabled.",
         int unsigned a_line = 0, string a_filename = "");

      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         CHECK_SVA_ENABLED : assert(check_expression(assertion.sva_enabled(test_name)) == 1)
         else begin
            if((a_line != 0) && (a_filename != "")) begin
               `uvm_error("CHECK_SVA_ENABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg))
            end else begin
               `uvm_error("CHECK_SVA_ENABLED_ERR", $sformatf("[%s::%s %s] %s", get_test_name(),
                     get_type_name(), a_sva_name, a_error_msg))
            end
         end
         add_check(assertion, "CHECK_SVA_ENABLED", $time(), get_current_check_status());
      end
   endfunction

   // ------------------ CHECK DISABLED -------------------------
   /* Verify if a given SVA is disabled - the test will pass if SVA is enabled
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @param a_error_msg : user error message to be printed if the check fails
    * @param a_line : the line number where the check is exercised
    * @param a_filename : the file name where the check is exercised
    */
   virtual function void check_sva_disabled(string a_sva_name, string a_error_msg = "The SVA should have been disabled.",
         int unsigned a_line = 0, string a_filename = "");

      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         CHECK_SVA_DISABLED : assert(check_expression(assertion.sva_disabled(test_name)) == 1)
         else begin
            if((a_line != 0) && (a_filename != "")) begin
               `uvm_error("CHECK_SVA_DISABLED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg))
            end else begin
               `uvm_error("CHECK_SVA_DISABLED_ERR", $sformatf("[%s::%s %s] %s", get_test_name(),
                     get_type_name(), a_sva_name, a_error_msg))
            end
         end
         add_check(assertion, "CHECK_SVA_DISABLED", $time(), get_current_check_status());
      end
   endfunction

   // ------------------ CHECK EXISTS -------------------------
   /* Verify if a given SVA exists - the test will fail if SVA does not exist
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @param a_error_msg : user error message to be printed if the check fails
    * @param a_line : the line number where the check is exercised
    * @param a_filename : the file name where the check is exercised
    */
   virtual function void check_sva_exists(string a_sva_name, string a_error_msg = "The SVA does not exist.",
         int unsigned a_line = 0, string a_filename = "");

      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion;
      if(is_a_path(a_sva_name)) begin
         assertion = vpi_vif.get_assertion_from_path(a_sva_name);
      end else begin
         assertion = vpi_vif.get_assertion_by_name(a_sva_name);
      end

      CHECK_SVA_EXISTS : assert((check_expression(assertion != null)) == 1)  begin
         assertion.set_tested(get_test_name());
      end else begin
         if((a_line != 0) && (a_filename != "")) begin
            `uvm_error("CHECK_SVA_EXISTS_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename,
                  a_line, get_test_name(), get_type_name(), a_sva_name, a_error_msg))
         end else begin
            `uvm_error("CHECK_SVA_EXISTS_ERR", $sformatf("[%s::%s %s] %s", get_test_name(),
                  get_type_name(), a_sva_name, a_error_msg))
         end

         begin
            string sva_name = a_sva_name;
            string sva_path = "";
            string sva_type = "";

            assertion = svaunit_concurrent_assertion_info::type_id::create( "new_assertion");

            assertion.create_new_sva(sva_name, sva_path, sva_type);
         end
      end

      add_check(assertion, "CHECK_SVA_EXISTS", $time(), get_current_check_status());
   endfunction



   // ------------------ CHECK PASSED-------------------------
   /* Verify if a given SVA succeeded - the test will fail if SVA failed
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @param a_error_msg : user error message to be printed if the check fails
    * @param a_line : the line number where the check is exercised
    * @param a_filename : the file name where the check is exercised
    */
   virtual task check_sva_passed(string a_sva_name, string a_error_msg = "The SVA should have passed.",
         int unsigned a_line = 0, string a_filename = "");

      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         check_assertion_is_enabled(a_sva_name);

         CHECK_SVA_PASSED : assert(check_expression(assertion.sva_passed()) == 1)
         else begin
            if((a_line != 0) && (a_filename != "")) begin
               `uvm_error("CHECK_SVA_PASSED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg))
            end else begin
               `uvm_error("CHECK_SVA_PASSED_ERR", $sformatf("[%s::%s %s] %s", get_test_name(),
                     get_type_name(), a_sva_name, a_error_msg))
            end
         end

         add_check(assertion, "CHECK_SVA_PASSED", $time(), get_current_check_status());
      end
   endtask



   // ------------------ CHECK FAILED -------------------------
   /* Verify if a given SVA didn't succeed; the test should fail if the SVA passed
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @param a_error_msg : user error message to be printed if the check fails
    * @param a_line : the line number where the check is exercised
    * @param a_filename : the file name where the check is exercised
    */
   virtual task check_sva_failed(string a_sva_name, string a_error_msg = "The SVA should have failed.",
         int unsigned a_line = 0, string a_filename = "");

      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin

         check_assertion_is_enabled(a_sva_name);

         CHECK_SVA_FAILED :  assert(check_expression(!assertion.sva_passed()) == 1)
         else begin
            if((a_line != 0) && (a_filename != "")) begin
               `uvm_error("CHECK_SVA_FAILED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename,
                     a_line, get_test_name(), get_type_name(), a_sva_name, a_error_msg))
            end else begin
               `uvm_error("CHECK_SVA_FAILED_ERR", $sformatf("[%s::%s %s] %s", get_test_name(),
                     get_type_name(), a_sva_name, a_error_msg))
            end

         end

         add_check(assertion, "CHECK_SVA_FAILED", $time(), get_current_check_status());
      end
   endtask



   // ------------------ CHECK FINISHED-------------------------
   /* Verify if a given SVA finished - the test will fail if the assertion did not finish
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @param a_error_msg : user error message to be printed if the check fails
    * @param a_line : the line number where the check is exercised
    * @param a_filename : the file name where the check is exercised
    */
   virtual task check_sva_finished(string a_sva_name, string a_error_msg = "The SVA should have finished.",
         int unsigned a_line = 0, string a_filename = "");

      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         check_assertion_is_enabled(a_sva_name);

         CHECK_SVA_FINISHED : assert(check_expression(assertion.sva_finished()) == 1)
         else begin

            if((a_line != 0) && (a_filename != "")) begin
               `uvm_error("CHECK_SVA_FINISHED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename, a_line,
                     get_test_name(), get_type_name(), a_sva_name, a_error_msg))
            end else begin
               `uvm_error("CHECK_SVA_FINISHED_ERR", $sformatf("[%s::%s %s] %s", get_test_name(),
                     get_type_name(), a_sva_name, a_error_msg))
            end
         end

         add_check(assertion, "CHECK_SVA_FINISHED", $time(), get_current_check_status());
      end
   endtask


   // ------------------ CHECK NOT FINISHED -------------------------
   /* Verify if a given SVA didn't finish; fail if it finished
    * @param a_sva_name : assertion name or path to be found in SVA list
    * @param a_error_msg : user error message to be printed if the check fails
    * @param a_line : the line number where the check is exercised
    * @param a_filename : the file name where the check is exercised
    */
   virtual task check_sva_not_finished(string a_sva_name, string a_error_msg = "The SVA should not have finished.",
         int unsigned a_line = 0, string a_filename = "");

      // Get the SVA from the SVA list
      svaunit_concurrent_assertion_info assertion = get_assertion(a_sva_name);

      if(assertion != null) begin
         check_assertion_is_enabled(a_sva_name);

         CHECK_SVA_NOT_FINISHED : assert(check_expression(assertion.sva_not_finished()) == 1)
         else begin
            if((a_line != 0) && (a_filename != "")) begin
               `uvm_error("CHECK_SVA_NOT_FINISHED_ERR", $sformatf("%s (%0d) [%s::%s %s] %s", a_filename,
                     a_line, get_test_name(), get_type_name(), a_sva_name, a_error_msg))
            end else begin
               `uvm_error("CHECK_SVA_NOT_FINISHED_ERR", $sformatf("[%s::%s %s] %s", get_test_name(),
                     get_type_name(), a_sva_name, a_error_msg))
            end
         end

         add_check(assertion, "CHECK_SVA_NOT_FINISHED", $time(), get_current_check_status());
      end
   endtask



   // ------------------ CHECK THAT  -------------------------
   /* Verify if the expression is true; the check fails if the expression is false
    * @param a_expression : the expression to be checked
    * @param a_error_msg : user error message to be printed if the check fails
    * @param a_line : the line number where the check is exercised
    * @param a_filename : the file name where the check is exercised
    */
   virtual function void check_that(bit a_expression, string a_error_msg = "The expression should have passed.", int unsigned a_line = 0,
         string a_filename = "");

      svaunit_concurrent_assertion_info new_assertion = svaunit_concurrent_assertion_info::type_id::create(
         "new_assertion");
      string sva_name = "";
      string sva_path = "";
      string sva_type = "";

      new_assertion.create_new_sva(sva_name, sva_path, sva_type);

      CHECK_THAT : assert(check_expression(a_expression) == 1)
      else begin
         if((a_line != 0) && (a_filename != "")) begin
            `uvm_error("CHECK_THAT_ERR", $sformatf("%s (%0d) [%s::%s] %s", a_filename, a_line,
                  get_test_name(), get_type_name(), a_error_msg))
         end else begin
            `uvm_error("CHECK_THAT_ERR",  $sformatf("[%s::%s] %s", get_test_name(), get_type_name(), a_error_msg))
         end
      end

      add_check(new_assertion, "CHECK_THAT", $time(), get_current_check_status());
   endfunction


   // Automatic check verified at the end of test for all enabled SVAs, if there are not any checks in unit test
   virtual task pass_assertion();
      if(lof_checks.size() == 0) begin
         if(vpi_vif.sva_info.size() > 0) begin
            foreach(vpi_vif.sva_info[sva_index]) begin
               if(is_enable(vpi_vif.sva_info[sva_index].get_sva_name())) begin
                  check_sva_failed(vpi_vif.sva_info[sva_index].get_sva_name(), $sformatf(
                        "Assertion %s should have succeeded, found instead: %s",
                        vpi_vif.sva_info[sva_index].get_sva_name(), vpi_vif.sva_info[sva_index].get_sva_state()));
               end
            end
         end
      end
   endtask


   /* Verify if all SVAs succeeded - the test will fail if any SVA failed
    * @param a_error_msg : custom error message which will be printed when the check fails
    */
   virtual function void check_all_sva_passed(string a_error_msg);

      // Shows that all SVAs succeeded in this test
      bit all_succeeded = 1;

      foreach(vpi_vif.sva_info[sva_index]) begin
         if(vpi_vif.sva_info[sva_index].sva_enabled(get_test_name())) begin
            string sva_name = vpi_vif.sva_info[sva_index].get_sva_name();
            if((get_nof_times_assertion_failed(sva_name) != 0) ||
                  (get_nof_times_assertion_succeeded(sva_name) == 0)) begin
               all_succeeded = 0;
            end
         end
      end

      CHECK_ALL_SVA_PASSED : assert((check_expression(all_succeeded == 1)) == 1)
      else begin
         `uvm_error("CHECK_ALL_SVA_PASSED_ERR", $sformatf("[%s::%s] %s",
               get_test_name(), get_type_name(), a_error_msg))
      end

      foreach(vpi_vif.sva_info[sva_index]) begin
         if(vpi_vif.sva_info[sva_index].sva_enabled(get_test_name())) begin
            add_check(vpi_vif.sva_info[sva_index], "CHECK_ALL_SVA_PASSED", $time(),
               get_current_check_status());
         end
      end
   endfunction

   /* Form the status to be printed
    * @return a string represents the status to be printed
    */
   virtual function void print_status();
      string report = "";

      report = $sformatf("\n\n-------------------- %s : Status statistics --------------------", get_test_name());
      report = $sformatf("%s\n\t%s\n", report, get_status_as_string());

      `uvm_info(get_test_name(), report, UVM_LOW)
   endfunction

   /* Form the status to be printed as a string
    * @return a string represents the status to be printed
    */
   virtual function string get_status_as_string();
      string star = " ";

      // Stored how many times the immediate assertion which were exercised passed
      int unsigned nof_times_check_has_passed = 0;

      // Stored how many times the immediate assertion were exercised
      int unsigned nof_times_check_was_tested = 0;

      // Stored the name of immediate assertions that were used
      string checks_names[$];
      get_checks_names(lof_checks, checks_names);

      // Compute how many immediate assertion passed and how many were exercised
      foreach(checks_names[index]) begin
         foreach(lof_checks[check_index]) begin
            foreach(lof_checks[check_index].checks_details[details_index])begin
               if(lof_checks[check_index].checks_details[details_index].get_check_name() == checks_names[index]) begin
                  nof_times_check_was_tested = nof_times_check_was_tested +
                  get_nof_times_check_was_tested(checks_names[index], lof_checks);
                  nof_times_check_has_passed = nof_times_check_has_passed +
                  get_nof_times_check_has_passed(checks_names[index], lof_checks);
               end
            end
         end
      end

      if(nof_times_check_was_tested > nof_times_check_has_passed) begin
         star = "* FAILED";
      end else begin
         star = "PASSED";
      end

      return $sformatf("\n\t%s   (%0d/%0d assertions PASSED)", star, nof_times_check_was_tested -
         nof_times_check_has_passed, nof_times_check_was_tested);
   endfunction

   /* Print a report for all checks tested from a specific list with immediate assertions
    * @param a_lof_used_checks : list of immediate assertions from where the report is made
    * @param a_test_name : the name of the test used to print it's checks
    */
   virtual function void print_checks_from_specific_list(string a_test_name,
         ref svaunit_immediate_assertion_info a_lof_used_checks[$]);

      string report = "";
      string star = "";
      string extra = "";
      string lof_used_checks_names[$];
      string lof_not_used_checks_names[$];
      int unsigned nof_times_check_was_tested;
      int unsigned nof_times_check_has_passed;

      get_checks_names(a_lof_used_checks, lof_used_checks_names);
      get_checks_not_used_names(a_lof_used_checks, lof_not_used_checks_names);

      report = $sformatf("\n\n-------------------- %s: Checks status summary --------------------\n\n", a_test_name);

      foreach(lof_used_checks_names[index]) begin
         nof_times_check_was_tested = 0;
         nof_times_check_has_passed = 0;
         star = " ";
         extra = "";

         nof_times_check_was_tested = get_nof_times_check_was_tested(lof_used_checks_names[index], a_lof_used_checks);
         nof_times_check_has_passed = get_nof_times_check_has_passed(lof_used_checks_names[index], a_lof_used_checks);

         if(nof_times_check_has_passed < nof_times_check_was_tested) begin
            star = "*";
         end

         extra = $sformatf("%0d/%0d PASSED", nof_times_check_has_passed, nof_times_check_was_tested);

         report = $sformatf("%s\t   %s   %s %s \n", report, star, lof_used_checks_names[index], extra);
      end


      `uvm_info(a_test_name, $sformatf("%s\n", report), UVM_LOW)
   endfunction

   // Print a report for all checks tested for the current unit test
   virtual function void print_checks();
      print_checks_from_specific_list(get_test_name(), lof_checks);
   endfunction

   /* Print a report for all checks tested for the SVAs from a specific list with immediate assertions
    * @param a_test_name : the name of the test used to print it's checks
    * @param a_lof_used_checks : list of immediate assertions from where the report is made
    */
   virtual function void print_sva_and_checks_for_specific_list(ref string a_test_name,
         svaunit_immediate_assertion_info a_lof_used_checks[$]);

      string report = "";

      report = $sformatf("\n\n-------------------- %s: Checks for each SVA statistics --------------------\n", a_test_name);

      foreach(a_lof_used_checks[check_index]) begin
         report = $sformatf("%s\n\t%s", report, a_lof_used_checks[check_index].get_checks_for_sva());
      end

      report = $sformatf("%s", report);

      `uvm_info(a_test_name, $sformatf("%s\n", report), UVM_NONE)
   endfunction

   // Print a report for all checks tested for the SVAs
   virtual function void print_sva_and_checks();
      string a_test_name = get_test_name();

      print_sva_and_checks_for_specific_list(a_test_name, lof_checks);
   endfunction

   /* Print a report for all SVA which have failed
    * @param a_test_name : the name of the test used to print it's checks
    * @param a_lof_used_checks : list of immediate assertions from where the report is made
    */
   virtual function void print_failed_sva_for_specific_list(ref string a_test_name,
         ref svaunit_immediate_assertion_info a_lof_used_checks[$]);

      string report = "";
      string details = "";

      foreach(a_lof_used_checks[check_index]) begin
         details = a_lof_used_checks[check_index].get_sva_failed_details();
         if(details != "") begin
            report = $sformatf("\n\n-------------------- %s: Failed SVAs --------------------\n", a_test_name);
            report = $sformatf("%s\n\t%s", report, a_lof_used_checks[check_index].get_sva_failed_details());
         end else begin
            report = $sformatf("\n\n-------------------- %s: All SVAs passed --------------------\n", a_test_name);
         end
      end

      report = $sformatf("%s", report);

      `uvm_info(a_test_name, $sformatf("%s\n\n\n", report), UVM_NONE)
   endfunction

   // Print a report for all SVA which have failed
   virtual function void print_failed_sva();
      string crt_test_name = get_test_name();

      print_failed_sva_for_specific_list(crt_test_name, lof_checks);
   endfunction

   // Will print the report for the current immediate assertions
   virtual function void print_report();
      print_status();
      print_sva();
      print_checks();
      print_sva_and_checks();
      print_failed_sva();
   endfunction

   // Print a list with all SVAs and with its status
   virtual function void print_sva();
      `uvm_info(get_test_name(), $sformatf("%s\n", vpi_vif.report_for_sva(get_test_name(), get_type_name())), UVM_LOW)
   endfunction

   /* Will print assertion info for an SVA with a given name
    * @param a_sva_name : assertion name to be found in SVA list
    */
   virtual function void print_sva_info(ref string a_sva_name);
      svaunit_concurrent_assertion_info assertion = get_assertion_by_name(a_sva_name);

      vpi_vif.get_info_from_c(get_test_name());

      if(assertion != null) begin
         assertion.print_sva_info(get_test_name());
      end
   endfunction
endclass

`endif