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
 * NAME:        svaunit_defines.svh
 * PROJECT:     svaunit
 * Description: Macros used in project
 *******************************************************************************/

`ifndef SVAUNIT_DEFINES_SVH
`define SVAUNIT_DEFINES_SVH

// Define the VPI interface and set it to uvm_config_db
`define SVAUNIT_UTILS \
`include "uvm_macros.svh" \
   import uvm_pkg::*; \
   import svaunit_pkg::*; \
   svaunit_vpi_interface vpi_if(); \
   svaunit_vpi_wrapper vpiw; \
   initial begin \
      uvm_config_db#(virtual svaunit_vpi_interface)::set(uvm_root::get(), "*", "VPI_VIF", vpi_if); \
      vpiw = svaunit_vpi_wrapper::type_id::create("VPIW"); \
      uvm_config_db#(svaunit_vpi_wrapper)::set(uvm_root::get(), "*", "VPIW", vpiw); \
   end

// Overwrite get_type_name for a parameterizable test
`define SVAUNIT_TEST_WITH_PARAM_UTILS \
   virtual function void set_test_name();\
      int start_index = 0;\
      int end_index = 0;\
      string first_del = "::";\
      string second_del = ")";\
      string new_test_type;\
\
      set_test_type($sformatf("%s@", $typename(this)));\
\
      start_index = vpiw.find(get_test_type(), first_del);\
      end_index = vpiw.find(get_test_type(), second_del);\
      new_test_type = get_test_type();\
\
      set_test_type(new_test_type.substr(start_index + 2, end_index));\
   endfunction\
   virtual function string get_type_name();\
      return get_test_type();\
   endfunction

// Add test for a test suite - a test suite must instantiate, create and start tests or sequences
`define add_test(test_or_seq_type) \
   begin\
      test_or_seq_type object = test_or_seq_type::type_id::create(create_test_name(`"test_or_seq_type`"), this);\
      add_test(object);\
   end


// --------------------------- SVAUnit checks ---------------------------------------
/* Verify if a given SVA is enabled - the test will fail if SVA is disabled
 * @param a_sva_name : assertion name or path to be found in SVA list
 * @param a_error_msg : user error message to be printed if the check fails
 */
`define check_sva_enabled(a_sva_name, a_error_msg) \
   vpiw.check_sva_enabled(a_sva_name, a_error_msg, `uvm_line, `uvm_file);

/* Verify if a given SVA is disabled - the test will fail if SVA is enabled
 * @param a_sva_name : assertion name or path to be found in SVA list
 * @param a_error_msg : user error message to be printed if the check fails
 */
`define check_sva_disabled(a_sva_name, a_error_msg) \
   vpiw.check_sva_disabled(a_sva_name, a_error_msg, `uvm_line, `uvm_file);

/* Verify if a given SVA exists - the test will fail if SVA does not exists
 * @param a_sva_name : assertion name or path to be found in SVA list
 * @param a_error_msg : user error message to be printed if the check fails
 */
`define check_sva_exists(a_sva_name, a_error_msg) \
   vpiw.check_sva_exists(a_sva_name, a_error_msg, `uvm_line, `uvm_file);


/* Verify if a given SVA passed - the test will fail if SVA failed
 * @param a_sva_name : assertion name or path to be found in SVA list
 * @param a_error_msg : user error message to be printed if the check fails
 */
`define check_sva_passed(a_sva_name, a_error_msg) \
   vpiw.check_sva_passed(a_sva_name, a_error_msg, `uvm_line, `uvm_file);

/* Verify if a given SVA failed - the test will fail if SVA passed
 * @param a_sva_name : assertion name to be found in SVA list
 * @param a_error_msg : user error message to be printed if the check fails
 */
`define check_sva_failed(a_sva_name, a_error_msg) \
   vpiw.check_sva_failed(a_sva_name, a_error_msg, `uvm_line, `uvm_file);


/* Verify if a given SVA finished - the test will fail if the assertion didn't finished
 * @param a_sva_name : assertion name or path to be found in SVA list
 * @param a_error_msg : user error message to be printed if the check fails
 */
`define check_sva_finished(a_sva_name, a_error_msg) \
   vpiw.check_sva_finished(a_sva_name, a_error_msg, `uvm_line, `uvm_file);

/* Verify if a given SVA did not finished - the test will fail if the assertion finished
 * @param a_sva_name : assertion name or path to be found in SVA list
 * @param a_error_msg : user error message to be printed if the check fails
 */
`define check_sva_not_finished(a_sva_name, a_error_msg) \
   vpiw.check_sva_not_finished(a_sva_name, a_error_msg, `uvm_line, `uvm_file);


/* Verify if the expression is FALSE - the test will fail if the expression is FALSE
 * @param a_expression : the expression to be checked
 * @param a_error_msg : user error message to be printed if the check fails
 */
`define check_that(a_expression, a_error_msg) \
   vpiw.check_that(a_expression, a_error_msg, `uvm_line, `uvm_file);


// ---------------------------- Assertion callback types ---------------------------------
// Define the assertion callback for START. The index value is specified by VPI.
`define SVAUNIT_VPI_CB_ASSERTION_START 606

// Define the assertion callback for SUCCESS. The index value is specified by VPI.
`define SVAUNIT_VPI_CB_ASSERTION_SUCCESS 607

// Define the assertion callback for FAILURE. The index value is specified by VPI.
`define SVAUNIT_VPI_CB_ASSERTION_FAILURE 608

// Define the assertion callback for STEP SUCCESS. The index value is specified by VPI.
`define SVAUNIT_VPI_CB_ASSERTION_STEP_SUCCESS 609

// Define the assertion callback for STEP FAILURE. The index value is specified by VPI.
`define SVAUNIT_VPI_CB_ASSERTION_STEP_FAILURE 610

// Define the assertion callback for DISABLE. The index value is specified by VPI.
`define SVAUNIT_VPI_CB_ASSERTION_DISABLE 611

// Define the assertion callback for ENABLE. The index value is specified by VPI.
`define SVAUNIT_VPI_CB_ASSERTION_ENABLE 612

// Define the assertion callback for RESET. The index value is specified by VPI.
`define SVAUNIT_VPI_CB_ASSERTION_RESET 613

// Define the assertion callback for KILL. The index value is specified by VPI.
`define SVAUNIT_VPI_CB_ASSERTION_KILL 614

//------------------------------- Assertion control --------------------------------
// Define assertion control constant for RESET. The index value is specified by VPI.
`define SVAUNIT_VPI_CONTROL_RESET_ASSERTION 622

// Define assertion control constant for DIASBLE. The index value is specified by VPI.
`define SVAUNIT_VPI_CONTROL_DISABLE_ASSERTION 620

// Define assertion control constant for ENABLE. The index value is specified by VPI.
`define SVAUNIT_VPI_CONTROL_ENABLE_ASSERTION 621

// Define assertion control constant for KILL. The index value is specified by VPI.
`define SVAUNIT_VPI_CONTROL_KILL_ASSERTION 623

// Define assertion control constant for DIASBLE STEP. The index value is specified by VPI.
`define SVAUNIT_VPI_CONTROL_DISABLE_STEP_ASSERTION 625

// Define assertion control constant for ENABLE STEP. The index value is specified by VPI.
`define SVAUNIT_VPI_CONTROL_ENABLE_STEP_ASSERTION 624

//------------------------------- Assertion system control --------------------------------
// Define assertion control constant for SYSTEM RESET. The index value is specified by VPI.
`define SVAUNIT_VPI_CONTROL_SYSTEM_RESET_ASSERTION 630

// Define assertion control constant for SYSTEM ON. The index value is specified by VPI.
`define SVAUNIT_VPI_CONTROL_SYSTEM_ON_ASSERTION 627

// Define assertion control constant for SYSTEM OFF. The index value is specified by VPI.
`define SVAUNIT_VPI_CONTROL_SYSTEM_OFF_ASSERTION 628

// Define assertion control constant for SYSTEM END. The index value is specified by VPI.
`define SVAUNIT_VPI_CONTROL_SYSTEM_END_ASSERTION 629

`endif
