
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
 * MODULE:       svaunit_concurrent_assertion_info.svh
 * PROJECT:      svaunit
 * Description:  SVA info class - it contains the SVA name, the SVA path, the SVA type, if SVA was enabled during test,
 *                                if it was tested, a list of details and coverage counters
 *******************************************************************************/

`ifndef SVAUNIT_CONCURRENT_ASSERTION_INFO_SVH
`define SVAUNIT_CONCURRENT_ASSERTION_INFO_SVH

// SVA info class - it contains the SVA name, the SVA path, the SVA type
//                  if SVA was enabled during test,
//                  if it was tested, a list of details and coverage counters
class svaunit_concurrent_assertion_info extends uvm_object;
   `uvm_object_utils(svaunit_concurrent_assertion_info)

   // Shows that an SVA is enable or not during test
   local bit enable;

   // SVA name
   local string sva_name;

   // SVA path
   local string sva_path;

   // SVA type
   local string sva_type;

   // Shows that an SVA was tested or not during test
   local svaunit_sva_tested_type tested;

   // List of details for the SVA
   local svaunit_concurrent_assertion_details sva_details[$];

   // Counter used to store the number of failures for an SVA cover
   local int nof_cover_failures;

   // Counter used to store the number of successful attempts for an SVA cover
   local int nof_cover_successfull;

   // List of tests names where current SVA is enabled
   local string lof_tests_sva_enabled[$];

   // List of tests names where current SVA is tested
   local string lof_tests_sva_tested[$];

   /* Constructor for an svaunit_concurrent_assertion_info
    * @param name : instance name for svaunit_concurrent_assertion_info object
    */
   function new(string name = "svaunit_concurrent_assertion_info");
      super.new(name);

      // Initial the enable bit is 1
      enable = 1;
   endfunction

   /* Create new SVA - the first detail is IDLE (the start and end time are the current time)
    * @param a_sva_name : current name to initialize the new SVA
    * @param a_sva_path : the path to the SVA which need to be created
    * @param a_sva_type : current type to initialize the new SVA
    */
   virtual function void create_new_sva(ref string a_sva_name, string a_sva_path, string a_sva_type);
      // Initialize SVA : set name, type, IDLE state and end time
      string test_name = "";
      svaunit_concurrent_assertion_state_type idle_state = SVAUNIT_IDLE;
      time current_time = $time();

      sva_name = a_sva_name;
      sva_type = a_sva_type;
      sva_path = a_sva_path;

      // Initial the enable bit is 1
      enable = 1;
      add_new_detail_sva(test_name, idle_state, current_time);
   endfunction

   /* Add new SVA details
    * @param a_test_name : test name where this attempt was found
    * @param a_sva_state : SVA state to be added
    * @param a_sva_end_time : SVA end time to be added
    */
   virtual function void add_new_detail_sva(string a_test_name,
         svaunit_concurrent_assertion_state_type a_sva_state, time a_sva_end_time);

      svaunit_concurrent_assertion_details details;

      details = svaunit_concurrent_assertion_details::type_id::create(
         $sformatf("%s_detail_%s", sva_name, sva_details.size() - 1));
      // Increase the SVA details list size

      // Create a new detail using factory mechanism
      sva_details.push_back(details);

      // Create new detail using given arguments
      sva_details[sva_details.size() - 1].create_new_detail(a_test_name, a_sva_state, a_sva_end_time);
   endfunction

   /* Get the index of the last SVA detail which has finished
    * @return the index of the last SVA detail which has finished
    */
   virtual function int unsigned get_last_index_sva_finished();
      // Variable used to store the last index
      int unsigned last_index = 0;

      // Verify for all details if they finished and store the last index of finished detail
      foreach(sva_details[index])
         if(sva_details[index].sva_state == SVAUNIT_FAILURE || sva_details[index].sva_state == SVAUNIT_SUCCESS)
            last_index = index;

      // Return the last index
      return last_index;
   endfunction

   /* Get the state of the last SVA detail
    * @return the state of the last SVA detail
    */
   virtual function svaunit_concurrent_assertion_state_type get_sva_state();
      return sva_details[sva_details.size() - 1].get_sva_state();
   endfunction

   /* Verify if last SVA has finished
    * @return 1 if last SVA has finished, 0 otherwise
    */
   virtual function bit sva_finished();
      if(sva_details.size() > 0)
         return (sva_details[$].sva_state == SVAUNIT_FAILURE || sva_details[$].sva_state == SVAUNIT_SUCCESS);
      else
         return 0;
   endfunction

   /* Verify if last SVA has not finished
    * @return 1 if last SVA has not finished, 0 otherwise
    */
   virtual function bit sva_not_finished();
      return !sva_finished();
   endfunction

   /* Verify if the last SVA detail succeeded
    * @return 1 if the last SVA detail succeeded and 0 otherwise
    */
   virtual function bit sva_passed();
      if(sva_details.size() > 0)
         return (sva_details[$].sva_state == SVAUNIT_SUCCESS);
      else
         return 0;
   endfunction

   /* Verify if the last SVA detail failed
    * @return 1 if the last SVA detail failed and 0 otherwise
    */
   virtual function bit sva_failed();
      if(sva_details.size() > 0)
         return (sva_details[$].sva_state == SVAUNIT_FAILURE);
      else
         return 0;
   endfunction

   /* Print the array of states exercised to the SVA
    * @param a_test_name : test name where this attempt was found
    */
   virtual function void print_sva_array(string a_test_name);
      string text = "";
      for(int i = 0; i < sva_details.size(); i++)
         text = {text, $sformatf("%s ", sva_details[i].get_sva_details(a_test_name))};
      `uvm_info(get_name(), text, UVM_NONE);
   endfunction


   /* Compute the number of SVA details which contains FAILURE in it's state list
    * @return the number of SVA details which failed
    */
   virtual function int unsigned get_nof_times_sva_fails();
      // Variable used to store the number of details which contains FAILURE in it's state list
      int unsigned nof_times_sva_failed = 0;

      foreach(sva_details[index])
         if(sva_details[index].sva_state == SVAUNIT_FAILURE)
            nof_times_sva_failed = nof_times_sva_failed + 1;

      // Return the number of details which contains FAILURE in it's state list
      return nof_times_sva_failed;
   endfunction

   /* Compute the number of SVA details which contains SUCCESS in it's state list
    * @return the number of SVA details which succeeded
    */
   virtual function int unsigned get_nof_times_sva_succeeded();
      // Variable used to store the number of details which contains SUCCESS in it's state list
      int unsigned nof_times_sva_succeeded = 0;

      foreach(sva_details[index])
         if(sva_details[index].sva_state == SVAUNIT_SUCCESS)
            nof_times_sva_succeeded = nof_times_sva_succeeded + 1;

      // Return the number of details which contains SUCCESS in it's state list
      return nof_times_sva_succeeded;
   endfunction

   /* Get SVA name
    * @return SVA name
    */
   virtual function string get_sva_name();
      return sva_name;
   endfunction

   /* Get SVA path
    * @return SVA name
    */
   virtual function string get_sva_path();
      return sva_path;
   endfunction

   /* Get SVA type
    * @return SVA type
    */
   virtual function string get_sva_type();
      return sva_type;
   endfunction

   /* Set the enable bit with a given bit
    * @param a_test_name : the test name where the assertion have been tested
    * @param a_enable_bit : current enable bit to set
    */
   virtual function void set_enable(ref string a_test_name, bit a_enable_bit);
      enable = a_enable_bit;

      if(a_enable_bit) begin
         lof_tests_sva_enabled.push_back(a_test_name);
      end
   endfunction

   /* Get the enable bit - it shows that the SVA is enable during test
    * @param a_test_name : the test name where the assertion have been tested
    * @return SVA status - if it is enabled or not
    */
   virtual function bit sva_enabled(string a_test_name);
      print_sva_array(a_test_name);

      if(get_sva_type() != "vpiCover") begin
         foreach(lof_tests_sva_enabled[test_index]) begin
            if(lof_tests_sva_enabled[test_index] == a_test_name) begin
               return enable;
            end
         end
      end else begin
         return enable;
      end

      return 0;
   endfunction

   virtual function bit sva_disabled(string a_test_name);
      return !sva_enabled(a_test_name);
   endfunction

   /* Verify if the SVA was enabled during test
    * @param a_test_name : the test name where the assertion have been tested
    * @return 1 if the SVA was enabled in given test and 0 otherwise
    */
   virtual function bit was_enable(string a_test_name);
      foreach(lof_tests_sva_enabled[test_index]) begin
         if(lof_tests_sva_enabled[test_index] == a_test_name) begin
            return 1;
         end
      end

      return 0;
   endfunction

   /* Set the tested bit with 1
    * @param a_test_name : the test name where the assertion have been tested
    */
   virtual function void set_tested(string a_test_name);
      tested = SVAUNIT_WAS_TESTED;

      lof_tests_sva_tested.push_back(a_test_name);
   endfunction

   /* Get the tested bit - it shows that the SVA was tested during test
    * @param a_test_name : the test name where the assertion have been tested
    * @return SVA status - if it is tested or not
    */
   virtual function svaunit_sva_tested_type was_tested(string a_test_name);
      if(lof_tests_sva_tested.size() > 0) begin
         foreach(lof_tests_sva_tested[test_index]) begin
            if(lof_tests_sva_tested[test_index] == a_test_name) begin
               return tested;
            end
         end
      end

      return SVAUNIT_NOT_TESTED;
   endfunction

   /* Sets the nof_cover_failures counter with the given number
    * @param a_nof_attempts_failed : current number to set the counter
    */
   virtual function void set_nof_attempts_failed_covered(int a_nof_attempts_failed);
      // If a_nof_attempts_failed is (-1) the counter will be 0, otherwise it will have
      // a_nof_attempts_failed value
      if(a_nof_attempts_failed == (-1)) begin
         nof_cover_failures = 0;
      end else begin
         nof_cover_failures = a_nof_attempts_failed;
      end
   endfunction

   /* Get the number of failures for an SVA cover
    * @return the nof_cover_failures counter
    */
   virtual function int unsigned get_nof_attempts_failed_covered();
      return nof_cover_failures;
   endfunction

   /* Sets the nof_cover_successfull counter with the given number
    * @param a_nof_attempts_successfull : current number to set the counter
    */
   virtual function void set_nof_attempts_successfull_covered(int a_nof_attempts_successfull);
      // If a_nof_attempts_successfull is (-1) the counter will be 0, otherwise it will have
      // a_nof_attempts_successfull value
      if(a_nof_attempts_successfull == (-1)) begin
         nof_cover_successfull = 0;
      end else begin
         nof_cover_successfull = a_nof_attempts_successfull;
      end
   endfunction

   /* Get the number of successful attempts for an SVA cover
    * @return the nof_cover_successfull counter
    */
   virtual function int unsigned get_nof_attempts_successful_covered();
      return nof_cover_successfull;
   endfunction

   /* Print SVA info for a given test
    * @param a_test_name : test name from where the user wants to print SVA info
    */
   virtual function void print_sva_info(string a_test_name);
      // Variable used to store the details as a string
      string details;

      // Example:
      // UVM_INFO @ 25000 ns [svaunit_concurrent_assertion_info]: SVA name = AN_SVA
      // UVM_INFO @ 25000 ns [svaunit_concurrent_assertion_info]: SVA type = vpiAssert
      // UVM_INFO @ 25000 ns [svaunit_concurrent_assertion_info]: SVA details[0] =
      // states : IDLE,
      // end time: 0

      `uvm_info(get_name(), $sformatf("SVA name = %s", get_sva_name()), UVM_LOW)
      `uvm_info(get_name(), $sformatf("SVA type = %s", get_sva_type()), UVM_LOW)

      foreach(sva_details[index]) begin
         details = sva_details[index].get_sva_details(a_test_name);
         if(details != "") begin
            `uvm_info(get_name(), $sformatf("[%s] SVA details[%0d] = %s",
                  sva_details[index].get_name(), index, details), UVM_LOW)
         end
      end
   endfunction
endclass

`endif
