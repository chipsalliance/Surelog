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
 * MODULE:       svaunit_immediate_assertion_info.svh
 * PROJECT:      svaunit
 * Description:  Immediate assertion class - it contains SVA tested name and a list of details
 *******************************************************************************/

`ifndef SVAUNIT_IMMEDIATE_ASSERTION_INFO_SVH
`define SVAUNIT_IMMEDIATE_ASSERTION_INFO_SVH

// Immediate assertion class - it contains SVA tested name and a list of details
class svaunit_immediate_assertion_info extends uvm_object;
   `uvm_object_utils(svaunit_immediate_assertion_info)

   // Pointer to the SVA which is tested
   svaunit_concurrent_assertion_info sva_tested;

   // Will store a list of details for immediate assertion
   svaunit_immediate_assertion_details checks_details[];

   /* Constructor for an svaunit_immediate_assertion_info
    * @param name : instance name for svaunit_immediate_assertion_info object
    */
   function new(input string name = "svaunit_immediate_assertion_info");
      super.new(name);
   endfunction

   /* Get the SVA which is tested
    * @return the SVA tested
    */
   virtual function svaunit_concurrent_assertion_info get_sva_tested();
      return sva_tested;
   endfunction

   /* Verify that a specific immediate assertion exists into the list
    * @param a_check_name : name of the immediate assertion to be found in list
    * @return 1 if the immediate assertion exists and 0 otherwise
    */
   virtual function bit check_exists(string a_check_name);
      // Variable used to store all the indexes of the elements which have the a_check_name
      // as the immediate_assertion name received
      int check_index[$];

      check_index = checks_details.find_index() with (item.get_check_name() == a_check_name);

      if(check_index.size() > 0) begin
         return 1;
      end else begin
         return 0;
      end
   endfunction

   /* Add new detail to a immediate assertion
    * @param a_check_name : name of the immediate assertion to be added
    * @param a_test_name : the name of the test where the immediate assertion is executed
    * @param a_time : current time at which the immediate assertion was tested
    * @param a_status : status of the current immediate assertion tested
    */
   virtual function void add_new_check_detail(string a_check_name, string a_test_name, time a_time,
         svaunit_status_type a_status);

      // Variable used to store all the indexes of the elements which have the immediate_assertion_name as the
      // immediate_assertion name received
      int check_index[$];

      check_index = checks_details.find_index() with (item.get_check_name() == a_check_name);
      
      if(check_index.size() > 0) begin
         foreach(check_index[index]) begin
            checks_details[check_index[index]].add_new_detail(a_test_name, a_time, a_status);
         end
      end else begin
         // Increase the size of details list, create new element and initialize properly
         checks_details = new[checks_details.size() + 1](checks_details);
         checks_details[checks_details.size() - 1] = svaunit_immediate_assertion_details::type_id::create(
            $sformatf("%s_detail_%s", a_check_name, checks_details.size() - 1));
         checks_details[checks_details.size() - 1].create_new_check_detail(a_check_name, a_test_name, a_time, a_status);
      end
   endfunction

   /* Set pointer to the SVA which needs to be checked
    * @param a_sva : new SVA to be checked
    */
   virtual function void set_sva(svaunit_concurrent_assertion_info a_sva);
      sva_tested = a_sva;
   endfunction

   /* Compute the number of times the immediate assertion was tested and it fails
    * @return the number of times the immediate assertion was tested and it fails
    */
   virtual function int unsigned get_nof_times_sva_has_failed();
      // Variable used to store the number of times the immediate assertion was tested and it fails
      int unsigned nof_times_assertion_failed = 0;

      // Increase the counter with the number of times the immediate assertion was tested and it fails for each details
      foreach(checks_details[details_index]) begin
         nof_times_assertion_failed = nof_times_assertion_failed +
         (checks_details[details_index].get_nof_times_check_was_tested()
            - checks_details[details_index].get_nof_times_check_has_passed());
      end

      // Return the number of times the immediate assertion was tested and it fails
      return nof_times_assertion_failed;
   endfunction

   /* Compute the number of times the immediate assertion was tested
    * @return the number of times the immediate assertion was tested
    */
   virtual function int unsigned get_nof_times_sva_was_tested();
      // Variable used to store the number of times the immediate assertion was tested and it fails
      int unsigned nof_times_assertion_tested = 0;

      // Increase the counter with the number of times the immediate assertion was tested and it fails for each details
      foreach(checks_details[details_index]) begin
         nof_times_assertion_tested = nof_times_assertion_tested +
         checks_details[details_index].get_nof_times_check_was_tested();
      end

      // Return the number of times the immediate assertion was tested and it fails
      return nof_times_assertion_tested;
   endfunction

   /* Form a string with immediate assertions details
    * @return the details of the immediate assertions tested during test
    */
   virtual function string get_checks_for_sva();
      // Variable used to store the string to be formed
      string details = "";
      string star = "";
      int unsigned nof_times_sva_tested = get_nof_times_sva_was_tested();
      int unsigned nof_times_sva_failed = get_nof_times_sva_has_failed();

      if(nof_times_sva_failed > 0) begin
         star = "*";
      end

      if(sva_tested != null) begin
         details = $sformatf("%s   %s   %0d/%0d checks PASSED", star, sva_tested.get_sva_name(), nof_times_sva_tested -
            nof_times_sva_failed, nof_times_sva_tested);
      end else begin
         details = $sformatf("%s   %0d/%0d checks PASSED", star, nof_times_sva_tested - nof_times_sva_failed,
            nof_times_sva_tested);
      end

      checks_details.rsort(item) with (item.get_nof_times_check_has_passed() < item.get_nof_times_check_was_tested());

      // Form string with each detail
      foreach(checks_details[details_index]) begin
         details = $sformatf("%s\n\t\t%s", details, checks_details[details_index].get_check_attempts());
      end

      details = $sformatf("%s\n", details);

      // Return the string
      return details;
   endfunction

   /* Form a string with SVAs which have failed
    * @return the names of the SVAs which have failed during test
    */
   virtual function string get_sva_failed_details();
      // Variable used to store the string to be formed
      string details = "";
      string star = "";
      int unsigned nof_times_sva_failed = get_nof_times_sva_has_failed();

      if(nof_times_sva_failed > 0) begin
         star = "*";
         details = $sformatf("%s\t%s   %s", details, star, sva_tested.get_sva_name());
      end

      // Return the string
      return details;
   endfunction

   /* Verify if an SVA assertion exists into SVA list
    * @param a_check_name : the SVAUnit check used to find inside the list of SVAUnit checks
    * @param a_lof_checks : a list with all SVAUnit checks names
    */
   virtual function bit details_exists(string a_check_name, ref string a_lof_checks[$]);
      // Variable used to store all the indexes of the elements which have the
      // immediate_assertion_name as the check_name name received
      int check_index[$];

      check_index = a_lof_checks.find_index() with (item == a_check_name);

      if(check_index.size() > 0) begin
         return 1;
      end else begin
         return 0;
      end
   endfunction

   /* Get a list with immediate assertion names which were used during test
    * @param a_lof_used_checks : the string list which contains the name of the checks used in this unit test
    */
   virtual function void get_checks_names(ref string a_lof_used_checks[$]);
      foreach(checks_details[details_index]) begin
         if(!details_exists(checks_details[details_index].get_check_name(), a_lof_used_checks)) begin
            a_lof_used_checks.push_back(checks_details[details_index].get_check_name());
         end
      end
   endfunction

   /* Get a copy with the current immediate assertion with only the details which belong to a given test
    * @param a_test_name : the test name where the immediate assertion was exercised
    * @return the copy of the current immediate assertion with only the details which belong to a given test
    */
   virtual function svaunit_immediate_assertion_info get_checks(string a_test_name);
      // Will store the index where the check already exists
      int check_index[$];

      // Will show the fact that the check already was tested
      bit was_tested = 0;

      get_checks = copy();
      get_checks.checks_details.delete();

      foreach(checks_details[details_index]) begin
         check_index = checks_details[details_index].tests_names.find_index() with (item == a_test_name);

         foreach(check_index[index]) begin
            was_tested = 1;
            get_checks.add_new_check_detail(
               checks_details[details_index].get_check_name(),
               a_test_name,
               checks_details[details_index].attempt_time[check_index[index]],
               checks_details[details_index].check_states[check_index[index]]);
         end
      end

      if(was_tested == 0) begin
         get_checks = null;
      end

      return get_checks;
   endfunction

   // Print immediate assertions tested in current test
   virtual function void print_checks();
      // Variable used to store the string for each detail
      string tested = "";

      `uvm_info(get_name(), $sformatf("Assertion %s was tested", sva_tested.get_sva_name()), UVM_LOW)

      foreach(checks_details[index]) begin
         tested = $sformatf("%s\n %s", tested, checks_details[index].get_check_attempts());
      end

      `uvm_info(get_name(), $sformatf("During test was tested: %s", tested), UVM_LOW)
   endfunction

   // Function used to copy the current item into new item
   function svaunit_immediate_assertion_info copy();
      copy = svaunit_immediate_assertion_info::type_id::create("copy_svaunit_immediate_assertion_info");
      
      copy.sva_tested = sva_tested;

      foreach(checks_details[index]) begin
         copy.checks_details = new[copy.checks_details.size() + 1](copy.checks_details);
         copy.checks_details[copy.checks_details.size() - 1] = svaunit_immediate_assertion_details::type_id::create(
            $sformatf("%s_copy_detail_%s", checks_details[index].get_check_name(), copy.checks_details.size() - 1));
         copy.checks_details[copy.checks_details.size() - 1] = checks_details[index].copy();
      end

      return copy;
   endfunction
endclass

`endif
