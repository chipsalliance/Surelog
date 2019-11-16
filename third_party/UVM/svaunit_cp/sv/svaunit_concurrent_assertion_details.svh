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
 * MODULE:       svaunit_concurrent_assertion_details.svh
 * PROJECT:      svaunit
 * Description:  SVA details class - it contains the states, the start time,
 *               the end time for the current attempt of SVA
 *               and the test name where the SVA was tested
 *******************************************************************************/

`ifndef SVAUNIT_CONCURRENT_ASSERTION_DETAILS_SVH
`define SVAUNIT_CONCURRENT_ASSERTION_DETAILS_SVH

// SVA details class - it contains SVA start time, SVA end time, the states and the test where the SVA was tested
class svaunit_concurrent_assertion_details extends uvm_object;
   `uvm_object_utils(svaunit_concurrent_assertion_details)

   // End time of the current SVA attempt
   local time sva_end_time;

   // SVA state
   svaunit_concurrent_assertion_state_type sva_state;

   // Test name where this attempt was found
   local string test_name;

   /* Constructor for an svaunit_concurrent_assertion_details
    * @param name   : instance name for svaunit_concurrent_assertion_details object
    */
   function new(string name = "svaunit_concurrent_assertion_details");
      super.new(name);
   endfunction

   /* Create new detail for an SVA
    * @param a_test_name : test name where this attempt was found
    * @param a_sva_state : SVA state to be added
    * @param a_sva_time_end : SVA end time to be added
    */
   virtual function void create_new_detail(ref string a_test_name, svaunit_concurrent_assertion_state_type a_sva_state,
         time a_sva_time_end);

      // Add new state inside list
      sva_state = a_sva_state;
      set_sva_test_name(a_test_name);
      set_sva_end_time(a_sva_time_end);
   endfunction

   /* Set test name for the current attempt of SVA
    * @param a_test_name : the current test name
    */
   virtual function void set_sva_test_name(ref string a_test_name);
      test_name = a_test_name;
   endfunction

   /* Set end time for the current attempt of SVA
    * @param a_sva_end_time : current end time
    */
   virtual function void set_sva_end_time(time a_sva_end_time);
      sva_end_time = a_sva_end_time;
   endfunction

   /* Get the end time of the current SVA attempt
    * @return the end time of the current SVA attempt
    */
   virtual function time get_sva_end_time();
      return sva_end_time;
   endfunction

   /* Get the first state of the current attempt of the SVA
    * @return the first state of the current attempt of the SVA
    */
   virtual function svaunit_concurrent_assertion_state_type get_sva_state();
      return sva_state;
   endfunction

   /* Verify if the current SVA is not finished
    * @return 1 if SVA has not finished and 0 otherwise
    */
   virtual function bit sva_is_not_finished();
      return !sva_is_finished();
   endfunction

   /* Verify if the current SVA attempt is finished
    * @return 1 if SVA has finished and 0 otherwise
    */
   virtual function bit sva_is_finished();
      if(sva_state == SVAUNIT_FAILURE || sva_state == SVAUNIT_SUCCESS)
         return 1;
      return 0;
   endfunction

   /* Verify if current SVA attempt has failed - one of it's state should be FAILURE
    * @return 1 if SVA attempt has failed or 0 otherwise
    */
   virtual function bit sva_failed();
      // Verify if SVA has finished and check if the last state is FAILURE
      if(sva_state == SVAUNIT_FAILURE)
         return 1;
      return 0;
   endfunction

   /* Verify if current SVA attempt has succeeded - one of it's state should be SUCCESS
    * @return 1 if SVA attempt has finished with success or 0 otherwise
    */
   virtual function bit sva_succeeded();
      if(sva_state == SVAUNIT_SUCCESS)
         return 1;
      return 0;
   endfunction


   /* Print the SVA details for a given test name
    * @param a_test_name : test name from where the user want's to print SVA info
    * @return a string with all SVA details
    */
   virtual function string get_sva_details(ref string a_test_name);
      // Stores the states names as a string
      string states;

      // Compute the string with states, start time and end time
      // Example:
      // state : SUCCESS
      // end time: 3
      if(a_test_name == test_name)
         return $sformatf("state: %s, end time: %0d\n", sva_state.name(), sva_end_time);
      else
         return "";
   endfunction
endclass

`endif
