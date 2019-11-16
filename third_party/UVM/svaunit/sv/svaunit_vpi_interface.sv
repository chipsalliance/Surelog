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
 * NAME:        svaunit_vpi_interface.sv
 * PROJECT:     svaunit
 * Description: It contains communication API with VPI
 *******************************************************************************/

`ifndef SVAUNIT_VPI_INTERFACE_SV
`define SVAUNIT_VPI_INTERFACE_SV

// It contains communication API with VPI
interface svaunit_vpi_interface();
   import svaunit_pkg::*;
   import uvm_pkg::*;
`include  "uvm_macros.svh"
`include  "svaunit_defines.svh"
`include  "svaunit_version_defines.svh"

   // DPI-C API used to find SVAs using VPI API
   import "DPI-C" context function void register_assertions_dpi(input int print_flag);

   /* Control assertion using vpi_control function
    * @param a_sva_name : the assertion used to apply control action on
    * @param a_control_type : the control action
    * @param a_sys_time : attempt time
    */
   import "DPI-C" context function void control_assertion_dpi(input string a_sva_name, input int a_control_type,
      input int a_sys_time);

   /* DPI-C API used to get SVA cover statistics - how many times this cover was triggered and how many times it failed
    * @param a_cover_name : cover name to retrieve information about
    * @param a_nof_attempts_covered : number of attempts this cover was triggered and it failed
    * @param a_nof_attempts_succeeded_covered : number of attempts this cover was triggered and it succeeded
    */
   import "DPI-C" context function void get_cover_statistics_dpi(input string a_cover_name,
      output int unsigned a_nof_attempts_covered, output int unsigned a_nof_attempts_succeeded_covered);

   /* DPI-C API to retrieve information about all callbacks
    * @param a_test_name : the test name from which this function is called
    */
   import "DPI-C" context function void call_callback_dpi(input string a_test_name);

   /* Set the current test name
    * @param a_test_name : current test name to be updated
    */
   import "DPI-C" context function void set_test_name_to_vpi_dpi(input string a_test_name);

   // Check that the current clock cycle has finished
   import "DPI-C" function int dpi_check_flag();

   /* VPI API to update a given SVA
    * @param a_test_name : test name from where this function is called
    * @param a_sva_name : SVA name to be updated
    * @param a_sva_type : the type of the SVA to be updated
    * @param a_reason : callback reason
    * @param a_start_time : the start attempt for this SVA
    * @param a_callback_time : the callback time for this SVA attempt
    */
   export "DPI-C" function pass_info_to_sv_dpi;

   /* Create SVA with a name and a type given
    * @param a_sva_name : SVA name to be created
    * @param a_sva_type : SVA type to be created
    */
   export "DPI-C" function create_assertion_dpi;

   // Stores the test name to be simulated
   string test_name;

   // "End of time slot" flag (1 - reached; 0 - not reached);
   bit eots_flag = 0;

   // Will store the info for all assertions from an interface
   svaunit_concurrent_assertion_info sva_info[];

   // Will store the info for all cover assertions from an interface
   svaunit_concurrent_assertion_info cover_info[];

   // Will store the info for all property assertions from an interface
   svaunit_concurrent_assertion_info property_info[];

   initial begin
      automatic string svaunit_header = "\n----------------------------------------------------------------";
      svaunit_header = $sformatf("%s\n\t\t%s\n", svaunit_header, `SVAUNIT_VERSION_STRING);
      svaunit_header = $sformatf("%s----------------------------------------------------------------\n",
         svaunit_header);

      `uvm_info("SVAUNIT", $sformatf("%s", svaunit_header), UVM_NONE)
      // Register the assertions from the interface

      if(uvm_top.get_report_verbosity_level() >= UVM_MEDIUM)
         register_assertions_dpi(1);
      else
         register_assertions_dpi(0);
   end

   /* Set test name in VPI interface
    * @param a_test_name : the test name to be added inside VPI interface
    */
   function void set_test_name(string a_test_name);
      test_name = a_test_name;

      set_test_name_to_vpi_dpi(test_name);
   endfunction

   /* Retrieve info about SVAs
    * @param a_test_name : test name from where this function is called
    */
   function void get_info_from_c(string a_test_name);
      call_callback_dpi(a_test_name);
   endfunction

   /* Verify if an SVA assertion exists into SVA list
    * @param a_sva_name : the SVA to be found into list
    * @param a_sva_path : the path to the SVA which needs to be found into list
    * @param a_lof_sva : the list of SVAs
    * @return 1 if given SVA exists into list and 0 otherwise
    */
   function bit sva_exists(string a_sva_name, string a_sva_path, svaunit_concurrent_assertion_info a_lof_sva[]);
      int index[$];

      index = a_lof_sva.find_index() with ((item.get_sva_name() == a_sva_name) && (item.get_sva_path() == a_sva_path));

      if(index.size() > 0) begin
         return 1;
      end else begin
         return 0;
      end
   endfunction

   /* Get the state for an SVA according to a callback a_reason
    * @param a_reason : the integer to be transformed to a callback reason
    * @return a state of an SVA transformed from a callback reason
    */
   function svaunit_concurrent_assertion_state_type get_state_from_reason(int a_reason);
      if (a_reason inside {`SVAUNIT_VPI_CB_ASSERTION_START, `SVAUNIT_VPI_CB_ASSERTION_SUCCESS,
               `SVAUNIT_VPI_CB_ASSERTION_FAILURE, `SVAUNIT_VPI_CB_ASSERTION_STEP_SUCCESS,
               `SVAUNIT_VPI_CB_ASSERTION_STEP_FAILURE, `SVAUNIT_VPI_CB_ASSERTION_DISABLE,
               `SVAUNIT_VPI_CB_ASSERTION_ENABLE, `SVAUNIT_VPI_CB_ASSERTION_RESET,
               `SVAUNIT_VPI_CB_ASSERTION_KILL}) begin
         if(a_reason == `SVAUNIT_VPI_CB_ASSERTION_START) begin
            return SVAUNIT_START;
         end
         else if(a_reason == `SVAUNIT_VPI_CB_ASSERTION_SUCCESS) begin
            return SVAUNIT_SUCCESS;
         end
         else if(a_reason == `SVAUNIT_VPI_CB_ASSERTION_FAILURE) begin
            return SVAUNIT_FAILURE;
         end
         if(a_reason == `SVAUNIT_VPI_CB_ASSERTION_STEP_SUCCESS) begin
            return SVAUNIT_STEP_SUCCESS;
         end
         else if(a_reason == `SVAUNIT_VPI_CB_ASSERTION_STEP_FAILURE) begin
            return SVAUNIT_STEP_FAILURE;
         end
         else if(a_reason == `SVAUNIT_VPI_CB_ASSERTION_DISABLE) begin
            return SVAUNIT_DISABLE;
         end
         if(a_reason == `SVAUNIT_VPI_CB_ASSERTION_ENABLE) begin
            return SVAUNIT_ENABLE;
         end
         else if(a_reason == `SVAUNIT_VPI_CB_ASSERTION_RESET) begin
            return SVAUNIT_RESET;
         end
         else if(a_reason == `SVAUNIT_VPI_CB_ASSERTION_KILL) begin
            return SVAUNIT_KILL;
         end
      end else begin
         return SVAUNIT_IDLE;
      end
   endfunction

   /* Update SVA info according to a reason
    * @param a_test_name : test name from where this function is called
    * @param a_sva_name : SVA name to be updated
    * @param a_sva_path : the path to the SVA which need to be updated
    * @param a_sva_type : the type of the SVA to be updated
    * @param a_reason : callback reason
    * @param a_callback_time : the callback time for this SVA attempt
    * @param a_lof_sva : the list of SVAs which contains the SVA to be updated
    */
   function void update_sva_from_c(string a_test_name, string a_sva_name, string a_sva_path, string a_sva_type,
         int a_reason, int a_callback_time, svaunit_concurrent_assertion_info a_lof_sva[]);

      foreach(a_lof_sva[index]) begin
         if((a_lof_sva[index].get_sva_name() == a_sva_name) && (a_lof_sva[index].get_sva_type() == a_sva_type) &&
               (a_lof_sva[index].get_sva_path() == a_sva_path)) begin

            static svaunit_concurrent_assertion_state_type crt_state = get_state_from_reason(a_reason);

            crt_state = svaunit_concurrent_assertion_state_type'(a_reason);

            if(crt_state inside {SVAUNIT_SUCCESS, SVAUNIT_FAILURE, SVAUNIT_DISABLE, SVAUNIT_ENABLE, SVAUNIT_RESET, SVAUNIT_KILL}) begin
               a_lof_sva[index].add_new_detail_sva(a_test_name, crt_state, a_callback_time);
            end
         end
      end
   endfunction

   /* Create SVA with a name and a type given
    * @param a_sva_name : SVA name to be created
    * @param a_sva_path : the path to the SVA which needs to be created
    * @param a_sva_type : SVA type to be created
    */
   function void create_assertion_dpi(string a_sva_name, string a_sva_path, string a_sva_type);
      if(a_sva_type == "vpiCover") begin
         if(!(sva_exists(a_sva_name, a_sva_path, cover_info))) begin
            // Create and add an assertion info to assertion_info array
            cover_info = new[cover_info.size() + 1] (cover_info);
            cover_info[cover_info.size() - 1] =
            svaunit_concurrent_assertion_info::type_id::create($sformatf("sva_%s", a_sva_name), null);
            cover_info[cover_info.size() - 1].create_new_sva(a_sva_name, a_sva_path, a_sva_type);
         end
      end else if(a_sva_type == "vpiAssert") begin
         if(!(sva_exists(a_sva_name, a_sva_path, sva_info))) begin
            // Create and add an assertion info to assertion_info array
            sva_info = new[sva_info.size() + 1] (sva_info);
            sva_info[sva_info.size() - 1] = svaunit_concurrent_assertion_info::type_id::create($sformatf("sva_%s",
                  a_sva_name), null);
            sva_info[sva_info.size() - 1].create_new_sva(a_sva_name, a_sva_path, a_sva_type);
         end
      end else if((a_sva_type == "vpiPropertyInst") || (a_sva_type == "vpiPropertyDecl")) begin
         if(!(sva_exists(a_sva_name, a_sva_path, property_info))) begin
            // Create and add an assertion info to assertion_info array
            property_info = new[property_info.size() + 1] (property_info);
            property_info[property_info.size() - 1] = svaunit_concurrent_assertion_info::type_id::
            create($sformatf("property_%s", a_sva_name), null);
            property_info[property_info.size() - 1].create_new_sva(a_sva_name, a_sva_path, a_sva_type);
         end
      end
   endfunction

   /* VPI API to update a given SVA
    * @param a_test_name : test name from where this function is called
    * @param a_sva_name : SVA name to be updated
    * @param a_sva_path : path to the SVA
    * @param a_sva_type : the type of the SVA to be updated
    * @param a_reason : callback reason
    * @param a_callback_time : the callback time for this SVA attempt
    * @param a_start_time : the start attempt for this SVA
    */
   function void pass_info_to_sv_dpi(string a_test_name, string a_sva_name, string a_sva_path, string a_sva_type,
         int a_reason, int a_callback_time, int a_start_time);

      if(a_sva_type == "vpiCover") begin
         update_sva_from_c(a_test_name, a_sva_name, a_sva_path, a_sva_type, a_reason, a_callback_time,
            cover_info);
      end else if(a_sva_type == "vpiAssert") begin
         update_sva_from_c(a_test_name, a_sva_name, a_sva_path, a_sva_type, a_reason, a_callback_time,
            sva_info);
      end else if((a_sva_type == "vpiPropertyInst") || (a_sva_type == "vpiPropertyDecl")) begin
         update_sva_from_c(a_test_name, a_sva_name, a_sva_path, a_sva_type, a_reason, a_callback_time,
            property_info);
      end
   endfunction

   /* Get the SVA with the given path
    * @param a_sva_path : SVA path to be found
    * @return the SVA with the given path
    */
   function svaunit_concurrent_assertion_info get_assertion_from_path(string a_sva_path);
      foreach(sva_info[index]) begin
         if(sva_info[index].get_sva_path() == a_sva_path) begin
            return sva_info[index];
         end
      end

      return null;
   endfunction

   /* Get the SVA with the given name
    * @param a_sva_name : SVA name to be found
    * @return the SVA with the given name
    */
   function svaunit_concurrent_assertion_info get_assertion_by_name(string a_sva_name);
      foreach(sva_info[index]) begin
         if(sva_info[index].get_sva_name() == a_sva_name) begin
            return sva_info[index];
         end
      end

      return null;
   endfunction


   // {{{ Functions used to control SVA
   //------------------------------- RESET --------------------------------
   /* Will discard all current attempts in progress for an SVA with a given name
    * and resets the SVA to its initial state
    * @param a_test_name : the test name from which SVA were enabled and tested
    * @param a_sva : assertion which needs to be reseted
    */
   function void reset_assertion(string a_test_name, svaunit_concurrent_assertion_info a_sva);
      automatic bit enable_sva = 1;

      a_sva.set_enable(a_test_name, enable_sva);
      control_assertion_dpi(a_sva.get_sva_path(), `SVAUNIT_VPI_CONTROL_RESET_ASSERTION, $time());
   endfunction

   /* Will discard all current attempts in progress for all SVAs and resets the SVAs to initial state
    * @param a_test_name : the test name from which SVA were enabled and tested
    */
   function void reset_all_assertions(string a_test_name);
      foreach(sva_info[index]) begin
         reset_assertion(a_test_name, sva_info[index]);
      end
   endfunction

   //------------------------------- DISABLE --------------------------------
   /* Will disable the starting of any new attempt for a given SVA
    * (this will have no effect on any existing attempts or if SVA was already disable;
    * on default all SVAs are enable)
    * @param a_test_name : the test name from which SVA were enabled and tested
    * @param a_sva : assertion which needs to be disabled
    */
   function void disable_assertion(string a_test_name, svaunit_concurrent_assertion_info a_sva);

      automatic bit disable_sva = 0;

      a_sva.set_enable(a_test_name, disable_sva);
      control_assertion_dpi(a_sva.get_sva_path(), `SVAUNIT_VPI_CONTROL_DISABLE_ASSERTION, $time());
   endfunction

   /* Will disable the starting of any new attempt for all SVAs
    * (this will have no effect on any existing attempts or if SVA was already disable;
    * on default all SVAs are enable)
    * @param a_test_name : the test name from which SVA were enabled and tested
    */
   function void disable_all_assertions(string a_test_name);
      foreach(sva_info[index]) begin
         disable_assertion(a_test_name, sva_info[index]);
      end
   endfunction

   //------------------------------- ENABLE --------------------------------
   /* Will enable starting any new attempts for a given SVA
    * (this will have no effect id SVA was already enable or on any current attempt)
    * @param a_test_name : the test name from which SVA were enabled and tested
    * @param a_sva : assertion which  needs to be enabled
    */
   function void enable_assertion(string a_test_name, svaunit_concurrent_assertion_info a_sva);
      automatic bit enable_sva = 1;

      a_sva.set_enable(a_test_name, enable_sva);
      control_assertion_dpi(a_sva.get_sva_path(), `SVAUNIT_VPI_CONTROL_ENABLE_ASSERTION, $time());
   endfunction

   /* Will enable starting any new attempts for all SVAs
    * (this will have no effect id SVA was already enable or on any current attempt)
    * @param a_test_name : the test name from which SVA were enabled and tested
    */
   function void enable_all_assertions(string a_test_name);
      foreach(sva_info[index]) begin
         enable_assertion(a_test_name, sva_info[index]);
      end
   endfunction

   //------------------------------- KILL --------------------------------
   /* Will discard any attempts of a given SVA
    * (the SVA will remain enabled and does not reset any state used by this SVA)
    * @param a_test_name : the test name from which SVA were enabled and tested
    * @param a_sva : assertion which  needs to be killed
    * @param a_sim_time : the time from which any attempt of a given SVA will be discarded
    */
   function void kill_assertion(string a_test_name, svaunit_concurrent_assertion_info a_sva, time a_sim_time);

      automatic bit enable_sva = 1;

      a_sva.set_enable(a_test_name, enable_sva);
      control_assertion_dpi(a_sva.get_sva_path(), `SVAUNIT_VPI_CONTROL_KILL_ASSERTION, a_sim_time);
   endfunction

   /* Will discard any attempts of all SVAs
    * (the SVA will remain enabled and does not reset any state used by any SVA)
    * @param a_test_name : the test name from which SVA were enabled and tested
    * @param a_sim_time : the time from which any attempt of a given SVA will be discarded
    */
   function void kill_all_assertions(string a_test_name, time a_sim_time);
      foreach(sva_info[index]) begin
         kill_assertion(a_test_name, sva_info[index], a_sim_time);
      end
   endfunction

   //------------------------------- DISABLE STEP --------------------------------
   /* Will disable step callback for a given SVA
    * (this will have no effect if step callback is not enabled or it was already disabled)
    * @param a_test_name : the test name from which SVA were enabled and tested
    * @param a_sva : assertion which  needs to disable stepping for
    */
   function void disable_step_assertion(string a_test_name, svaunit_concurrent_assertion_info a_sva);

      automatic bit enable_sva = 1;

      a_sva.set_enable(a_test_name, enable_sva);
      control_assertion_dpi(a_sva.get_sva_path(), `SVAUNIT_VPI_CONTROL_DISABLE_STEP_ASSERTION, $time());
   endfunction

   /* Will disable step callback for all SVAs
    * (this will have no effect if step callback is not enabled or it was already disabled)
    * @param a_test_name : the test name from which SVA were enabled and tested
    */
   function void disable_step_all_assertions(string a_test_name);
      foreach(sva_info[index]) begin
         disable_step_assertion(a_test_name, sva_info[index]);
      end
   endfunction

   //------------------------------- ENABLE STEP --------------------------------

   /* Will enable step callback for a given SVA
    * (by default, stepping is disabled; this will have no effect if stepping was already enabled;
    * the stepping mode cannot be modified after the assertion attempt has started)
    * @param a_test_name : the test name from which SVA were enabled and tested
    * @param a_sva : assertion which  needs to enable stepping for
    */
   function void enable_step_assertion(string a_test_name, svaunit_concurrent_assertion_info a_sva);

      automatic bit enable_sva = 1;

      a_sva.set_enable(a_test_name, enable_sva);
      control_assertion_dpi(a_sva.get_sva_path(), `SVAUNIT_VPI_CONTROL_ENABLE_STEP_ASSERTION, $time());
   endfunction

   /* Will enable step callback for all SVAs
    * (by default, stepping is disabled; this will have no effect if stepping was already enabled;
    * the stepping mode cannot be modified after the assertion attempt has started)
    * @param a_test_name : the test name from which SVA were enabled and tested
    */
   function void enable_step_all_assertions(string a_test_name);
      foreach(sva_info[index]) begin
         enable_step_assertion(a_test_name, sva_info[index]);
      end
   endfunction

   //------------------------------- SYSTEM RESET --------------------------------
   /* Will discard all attempts in progress for all SVAs and restore the entire assertion system to its initial state.
    * (The vpiAssertionStepSuccess and vpiAssertionStepFailure callbacks will be removed)
    */
   function void system_reset_all_assertions();
      control_assertion_dpi("", `SVAUNIT_VPI_CONTROL_SYSTEM_RESET_ASSERTION, $time());
   endfunction


   //------------------------------- SYSTEM ON --------------------------------
   /* Will restart the SVAs after it was stopped
    * @param a_test_name : the test name from which SVA were enabled and tested
    */
   function void system_on_all_assertions(string a_test_name);
      control_assertion_dpi("", `SVAUNIT_VPI_CONTROL_SYSTEM_ON_ASSERTION, $time());

      foreach(sva_info[index]) begin
         automatic bit enable_sva = 1;

         sva_info[index].set_enable(a_test_name, enable_sva);
      end
   endfunction


   //------------------------------- SYSTEM OFF --------------------------------
   /* Will disable any SVA to being started and all current attempts will be considered as unterminated
    * @param a_test_name : the test name from which SVA were enabled and tested
    */
   function void system_off_all_assertions(string a_test_name);
      control_assertion_dpi("", `SVAUNIT_VPI_CONTROL_SYSTEM_OFF_ASSERTION, $time());

      foreach(sva_info[index]) begin
         automatic bit disable_sva = 0;

         sva_info[index].set_enable(a_test_name, disable_sva);
      end
   endfunction


   //------------------------------- SYSTEM END --------------------------------
   /* Will discard any attempt in progress and disable any SVA to be started
    * (all callbacks will be removed)
    * @param a_test_name : the test name from which SVA were enabled and tested
    */
   function void system_end_all_assertions(string a_test_name);
      control_assertion_dpi("", `SVAUNIT_VPI_CONTROL_SYSTEM_END_ASSERTION, $time());

      foreach(sva_info[index]) begin
         automatic bit disable_sva = 0;

         sva_info[index].set_enable(a_test_name, disable_sva);
      end
   endfunction
   // }}}

   /* Update SVA cover
    * @param a_test_name : the test name from which SVA were enabled and tested
    */
   function void update_coverage(string a_test_name);
      automatic int nof_attempts_failed_covered;
      automatic int nof_attempts_successful_covered;

      foreach(cover_info[index]) begin
         if(cover_info[index].sva_enabled(a_test_name)) begin
            get_cover_statistics_dpi(cover_info[index].get_sva_name(), nof_attempts_failed_covered,
               nof_attempts_successful_covered);
            cover_info[index].set_nof_attempts_failed_covered(nof_attempts_failed_covered);
            cover_info[index].set_nof_attempts_successfull_covered(nof_attempts_successful_covered);
         end
      end
   endfunction

   /* Computes how many SVAs are enabled during simulation
    * @param a_test_name : the test name from which SVA were enabled and tested
    * @return number of SVA which are enabled during simulation
    */
   function int unsigned get_nof_enabled_sva(string a_test_name);
      // It stores the number of SVA enabled during simulation
      automatic int unsigned nof_sva_enabled = 0;

      //For each SVA verify if it is enabled and increase the counter
      foreach(sva_info[index]) begin
         if(sva_info[index].was_enable(a_test_name)) begin
            nof_sva_enabled = nof_sva_enabled + 1;
         end
      end

      return nof_sva_enabled;
   endfunction

   /* Computes how many SVAs were tested during simulation
    * @param a_test_name : the test name from which SVA were enabled and tested
    * @return number of SVA which were tested during simulation
    */
   function int unsigned get_nof_tested_sva(string a_test_name);
      // It stores the number of SVA tested during simulation
      automatic int unsigned nof_sva_tested = 0;

      //For each SVA verify if it was tested and increase the counter
      foreach(sva_info[index]) begin
         if(sva_info[index].was_tested(a_test_name)) begin
            nof_sva_tested = nof_sva_tested + 1;
         end
      end

      return nof_sva_tested;
   endfunction

   /* Get the total number of SVAs
    * @return total number of SVAs
    */
   function int unsigned get_nof_sva();
      return sva_info.size();
   endfunction

   /* Form the report status of SVA
    * @param a_test_name : the test name from which SVA were enabled and tested
    * @return the report status for all SVAs
    */
   function string report_for_sva(string a_test_name, string test_type);
      // Stores the report
      static string report = "";

      // Stores extra report
      static string extra = "";

      // Stores how many SVAs were enabled during simulation
      int unsigned nof_enabled_sva;

      // Stores how many SVAs were tested during simulation
      int unsigned nof_tested_sva;

      // Initialize counters
      nof_enabled_sva = get_nof_enabled_sva(a_test_name);
      nof_tested_sva = get_nof_tested_sva(a_test_name);

      // Header for SVAs
      report = $sformatf("\n\n-------------------- %s::%s : SVAs run statistics --------------------\n\n",
         a_test_name, test_type);

      // Print how many enabled SVA are from a total number of SVA
      report = $sformatf("%s\t%0d/%0d SVA were enabled: \n", report, nof_enabled_sva, get_nof_sva());

      // Form the SVAs enabled
      foreach(sva_info[index]) begin
         if(sva_info[index].was_enable(a_test_name)) begin
            report = $sformatf("%s\t\t%s\n", report, sva_info[index].get_sva_name());
         end
      end

      // Print how many tested SVA are from a total number of enabled SVA
      report = $sformatf("%s\n\n\t%0d/%0d SVA were exercised: \n\n", report, nof_tested_sva, sva_info.size());

      // Form the SVAs tested
      foreach(sva_info[index]) begin
         if(sva_info[index].was_tested(a_test_name)) begin
            report = $sformatf("%s\t\t%s\n", report, sva_info[index].get_sva_name());
         end
      end

      // Print how many not tested SVA are from a total number of enabled SVA
      report = $sformatf("%s\n\n\t%0d/%0d SVA were not exercised: \n\n",
         report, sva_info.size() - nof_tested_sva, sva_info.size());

      // Form the SVAs not tested
      foreach(sva_info[index]) begin
         if(!sva_info[index].was_tested(a_test_name)) begin
            report = $sformatf("%s\t\t%s\n", report, sva_info[index].get_sva_name());
         end
      end

      // Header for cover SVAs
      report = $sformatf("%s\n\n-------------------- %s::%s: Cover statistics --------------------\n\n", report,
         a_test_name, test_type);

      // Form the cover SVA
      foreach(cover_info[index]) begin
         if(cover_info[index].sva_enabled(a_test_name)) begin
            extra = $sformatf("%0d SUCCEEDED, %0d FAILED", cover_info[index]
               .get_nof_attempts_successful_covered(), cover_info[index].get_nof_attempts_failed_covered());

            report = $sformatf("%s\t%s %s\n", report, cover_info[index].get_sva_name(), extra);
         end
      end

      return report;
   endfunction

   // Polls the until the "End of time slot" is set (i.e. time slot ended)
   task wait_for_eots();
      do begin
         eots_flag = dpi_check_flag();
         // We need a wait here. Beware #0 goes into an infinite loop. As specified in LRM, #0 sends you to NB region.
         #1;
      end while (eots_flag == 0);

      // Clear the flag for next time slot
      eots_flag = 0;
   endtask
endinterface

`endif
