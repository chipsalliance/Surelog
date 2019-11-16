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
 * MODULE:       svaunit_immediate_assertion_details.svh
 * PROJECT:      svaunit
 * Description:  Immediate assertion details class - it contains the name, the tested time and the status
 *******************************************************************************/

`ifndef SVAUNIT_IMMEDIATE_ASSERTION_DETAILS_SVH
`define SVAUNIT_IMMEDIATE_ASSERTION_DETAILS_SVH

// Immediate assertion details class - it contains the name, the tested time and the status
class svaunit_immediate_assertion_details extends uvm_object;
   `uvm_object_utils(svaunit_immediate_assertion_details)

   // Will store the name of the immediate assertion tested into current test
   string check_name;

   // Will store the time at which the immediate assertion is executed
   time attempt_time[$];

   // Will store the status of the immediate assertion
   svaunit_status_type check_states[$];

   // Will store the names of the tests where the current immediate assertion is executed
   string tests_names[$];

   /* Constructor for an svaunit_immediate_assertion_details
    * @param name : instance name for svaunit_immediate_assertion_details object
    */
   function new(input string name = "svaunit_immediate_assertion_details");
      super.new(name);
   endfunction

   /* Set immediate assertion name
    * @param a_check_name : current a_check_name name to be added
    */
   virtual function void set_check_name(ref string a_check_name);
      check_name = a_check_name;
   endfunction

   /* Get immediate assertion name
    * @return the immediate assertion name
    */
   virtual function string get_check_name();
      return check_name;
   endfunction

   /* Add test name for the immediate assertion
    * @param a_test_name : current test name when the immediate assertion was exercised
    */
   virtual function void add_test_name(ref string a_test_name);
      tests_names.push_back(a_test_name);
   endfunction

   /* Add test time for the immediate assertion
    * @param a_test_time : current time when the immediate assertion was tested
    */
   virtual function void add_test_time(time a_test_time);
      attempt_time.push_back(a_test_time);
   endfunction

   /* Add status for the immediate assertion
    * @param a_status : status of the current attempt of immediate assertion
    */
   virtual function void add_status(svaunit_status_type a_status);
      check_states.push_back(a_status);
   endfunction

   /* Create new details for the immediate assertion :
    * set name, the test time and the status for the current attempt of the immediate assertion
    * @param a_check_name : the name of immediate assertion which is tested
    * @param a_test_name : the name of the test where the immediate assertion is executed
    * @param a_test_time : the time at which the immediate assertion was tested
    * @param a_status : the current status of the immediate assertion
    */
   virtual function void create_new_check_detail(string a_check_name, string a_test_name, time a_test_time,
         svaunit_status_type a_status);
      set_check_name(a_check_name);
      add_test_name(a_test_name);
      add_test_time(a_test_time);
      add_status(a_status);
   endfunction

   /* Add new details for the immediate assertion :
    * set test time and status for the current attempt of the immediate assertion
    * @param a_test_name : the name of the test where the immediate assertion is executed
    * @param a_test_time : the time at which the immediate assertion was tested
    * @param a_status : the current status of the immediate assertion
    */
   virtual function void add_new_detail(string a_test_name, time a_test_time, svaunit_status_type a_status);
      add_test_name(a_test_name);
      add_test_time(a_test_time);
      add_status(a_status);
   endfunction

   /* Compute the number of times the immediate assertion passed during simulation
    * @return the number of times the immediate assertion passed during simulation
    */
   virtual function int unsigned get_nof_times_check_has_passed();
      // Variable used to store the number of times the immediate assertion passed during simulation
      int unsigned nof_tests_passed = 0;

      // Check for each immediate assertion if they passed and increase the counter
      foreach(check_states[status_index]) begin
         if(check_states[status_index] == SVAUNIT_PASS) begin
            nof_tests_passed = nof_tests_passed + 1;
         end
      end

      // Return the number of times the immediate assertion passed during simulation
      return nof_tests_passed;
   endfunction

   /* Compute the number of times the immediate assertion was tested during simulation
    * @return the number of times the immediate assertion was tested during simulation
    */
   virtual function int unsigned get_nof_times_check_was_tested();
      return check_states.size();
   endfunction

   /* Get details for a immediate assertion
    * @return a string with all immediate assertion details
    */
   virtual function string get_check_attempts();
      string star = " ";

      if(get_nof_times_check_has_passed() < get_nof_times_check_was_tested()) begin
         star = "*";
      end

      return $sformatf("%s   %s %0d/%0d PASSED", star, check_name, get_nof_times_check_has_passed(),
         get_nof_times_check_was_tested());
   endfunction

   // Function used to copy the current item into new item
   function svaunit_immediate_assertion_details copy();
      copy = svaunit_immediate_assertion_details::type_id::create("copy_svaunit_immediate_assertion_details");

      copy.check_name = check_name;

      foreach(tests_names[index]) begin
         copy.tests_names.push_back(tests_names[index]);
      end

      foreach(attempt_time[index]) begin
         copy.attempt_time.push_back(attempt_time[index]);
      end

      foreach(check_states[index]) begin
         copy.check_states.push_back(check_states[index]);
      end

      return copy;
   endfunction
endclass

`endif
