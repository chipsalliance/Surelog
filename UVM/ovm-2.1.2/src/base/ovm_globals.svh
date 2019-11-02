// $Id: ovm_globals.svh,v 1.5 2009/10/30 15:29:21 jlrose Exp $
//------------------------------------------------------------------------------
//   Copyright 2007-2008 Mentor Graphics Corporation
//   Copyright 2007-2008 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//------------------------------------------------------------------------------


// Title: Globals

//------------------------------------------------------------------------------
//
// Group: Simulation Control
//
//------------------------------------------------------------------------------

// Task: run_test
//
// Convenience function for ovm_top.run_test(). See ovm_root for more
// information.

task run_test (string test_name="");
  ovm_root top;
  top = ovm_root::get();
  top.run_test(test_name);
endtask


// Variable: ovm_test_done
//
// An instance of the <ovm_test_done_objection> class, this object is
// used by components to coordinate when to end the currently running
// task-based phase. When all participating components have dropped their
// raised objections, an implicit call to <global_stop_request> is issued
// to end the run phase (or any other task-based phase).

ovm_test_done_objection ovm_test_done = ovm_test_done_objection::get();



// Method: global_stop_request 
//
// Convenience function for ovm_top.stop_request(). See ovm_root for more
// information.

function void global_stop_request();
  ovm_root top;
  top = ovm_root::get();
  top.stop_request();
endfunction


// Method: set_global_timeout 
//
// Convenience function for ovm_top.phase_timeout = timeout. See ovm_root
// for more information.

function void set_global_timeout(time timeout);
  ovm_root top;
  top = ovm_root::get();
  top.phase_timeout = timeout;
endfunction


// Function: set_global_stop_timeout
//
// Convenience function for ovm_top.stop_timeout = timeout.
// See ovm_root for more information.

function void set_global_stop_timeout(time timeout);
  ovm_root top;
  top = ovm_root::get();
  top.stop_timeout = timeout;
endfunction


// ovm_find_component (deprecated)
// ------------------

function ovm_component ovm_find_component (string comp_name);
  ovm_root top;
  static bit issued=0;
  if (!issued) begin
    issued=1;
    ovm_report_warning("deprecated",
      {"ovm_find_component() is deprecated and replaced by ",
      "ovm_top.find(comp_name)"}, OVM_NONE);
  end
  top = ovm_root::get();
  return top.find(comp_name);
endfunction


// ovm_print_topology (deprecated)
// ------------------

function void ovm_print_topology(ovm_printer printer=null);
  static bit issued=0;
  if (!issued) begin
    issued=1;
    ovm_report_warning("deprecated",
      {"ovm_print_topology() is deprecated and replaced by ",
      "ovm_top.print_topology()"}, OVM_NONE);
  end
  ovm_top.print_topology(printer);
endfunction



//----------------------------------------------------------------------------
//
// Group: Reporting
//
//----------------------------------------------------------------------------

// Function: ovm_report_enabled
//
// Returns 1 if the configured verbosity in <ovm_top> is greater than 
// ~verbosity~ and the action associated with the given ~severity~ and ~id~
// is not OVM_NO_ACTION, else returns 0.
// 
// See also <ovm_report_object::ovm_report_enabled>.
//
//
// Static methods of an extension of ovm_report_object, e.g. ovm_compoent-based
// objects, can not call ~ovm_report_enabled~ because the call will resolve to
// the <ovm_report_object::ovm_report_enabled>, which is non-static.
// Static methods can not call non-static methods of the same class. 

function bit ovm_report_enabled (int verbosity,
                                 ovm_severity severity=OVM_INFO, string id="");
  return ovm_top.ovm_report_enabled(verbosity,severity,id);
endfunction


// Function: ovm_report_info

function void ovm_report_info(string id,
			      string message,
                              int verbosity = OVM_MEDIUM,
			      string filename = "",
			      int line = 0);
  ovm_top.ovm_report_info(id, message, verbosity, filename, line);
endfunction


// Function: ovm_report_warning

function void ovm_report_warning(string id,
                                 string message,
                                 int verbosity = OVM_MEDIUM,
				 string filename = "",
				 int line = 0);
  ovm_top.ovm_report_warning(id, message, verbosity, filename, line);
endfunction


// Function: ovm_report_error

function void ovm_report_error(string id,
                               string message,
                               int verbosity = OVM_LOW,
			       string filename = "",
			       int line = 0);
  ovm_top.ovm_report_error(id, message, verbosity, filename, line);
endfunction


// Function: ovm_report_fatal
//
// These methods, defined in package scope, are convenience functions that
// delegate to the corresponding component methods in ~ovm_top~. They can be
// used in module-based code to use the same reporting mechanism as class-based
// components. See <ovm_report_object> for details on the reporting mechanism. 
//
// Note: Verbosity is ignored for warnings, errors, and fatals to ensure users
// do not inadvertently filter them out. It remains in the methods for backward
// compatibility.

function void ovm_report_fatal(string id,
	                       string message,
                               int verbosity = OVM_NONE,
			       string filename = "",
			       int line = 0);
  ovm_top.ovm_report_fatal(id, message, verbosity, filename, line);
endfunction

  
//------------------------------------------------------------------------------
//
// Group: Configuration
//
//------------------------------------------------------------------------------

// Function: set_config_int
//
// This is the global version of set_config_int in <ovm_component>. This
// function places the configuration setting for an integral field in a
// global override table, which has highest precedence over any
// component-level setting.  See <ovm_component::set_config_int> for
// details on setting configuration.

function void  set_config_int  (string inst_name,
                                string field_name,
                                ovm_bitstream_t value);
  ovm_root top;
  top = ovm_root::get();
  top.set_config_int(inst_name, field_name, value);
endfunction


// Function: set_config_object
//
// This is the global version of set_config_object in <ovm_component>. This
// function places the configuration setting for an object field in a
// global override table, which has highest precedence over any
// component-level setting.  See <ovm_component::set_config_object> for
// details on setting configuration.

function void set_config_object (string inst_name,
                                 string field_name,
                                 ovm_object value,
                                 bit clone=1);
  ovm_root top;
  top = ovm_root::get();
  top.set_config_object(inst_name, field_name, value, clone);
endfunction


// Function: set_config_string
//
// This is the global version of set_config_string in <ovm_component>. This
// function places the configuration setting for an string field in a
// global override table, which has highest precedence over any
// component-level setting.  See <ovm_component::set_config_string> for
// details on setting configuration.

function void set_config_string (string inst_name,  
                                 string field_name,
                                 string value);
  ovm_root top;
  top = ovm_root::get();
  top.set_config_string(inst_name, field_name, value);
endfunction



//----------------------------------------------------------------------------
//
// Group: Miscellaneous
//
//----------------------------------------------------------------------------


// Function: ovm_is_match
//
// Returns 1 if the two strings match, 0 otherwise.
//
// The first string, ~expr~, is a string that may contain '*' and '?'
// characters. A * matches zero or more characters, and ? matches any single
// character. The 2nd argument, ~str~, is the string begin matched against.
// It must not contain any wildcards.
//
//----------------------------------------------------------------------------

`ifdef OVM_DPI
import "DPI" function bit ovm_is_match (string expr, string str);
`else
function bit ovm_is_match (string expr, string str);

  int e, es, s, ss;
  string tmp;
  e  = 0; s  = 0;
  es = 0; ss = 0;

  if(expr.len() == 0)
    return 1;

  // The ^ used to be used to remove the implicit wildcard, but now we don't
  // use implicit wildcard so this character is just stripped.
  if(expr[0] == "^")
    expr = expr.substr(1, expr.len()-1);

  //This loop is only needed when the first character of the expr may not
  //be a *. 
  while (s != str.len() && expr.getc(e) != "*") begin
    if ((expr.getc(e) != str.getc(s)) && (expr.getc(e) != "?"))
      return 0;
    e++; s++;
  end

  while (s != str.len()) begin
    if (expr.getc(e) == "*") begin
      e++;
      if (e == expr.len()) begin
        return 1;
      end
      es = e;
      ss = s+1;
    end
    else if (expr.getc(e) == str.getc(s) || expr.getc(e) == "?") begin
      e++;
      s++;
    end
    else begin
      e = es;
      s = ss++;
    end
  end
  while (expr.getc(e) == "*")
    e++;
  if(e == expr.len()) begin
    return 1;
  end
  else begin
    return 0;
  end
endfunction
`endif


`ifndef OVM_LINE_WIDTH
  `define OVM_LINE_WIDTH 120
`endif 
parameter OVM_LINE_WIDTH = `OVM_LINE_WIDTH;

`ifndef OVM_NUM_LINES
  `define OVM_NUM_LINES 120
`endif
parameter OVM_NUM_LINES = `OVM_NUM_LINES;

parameter OVM_SMALL_STRING = OVM_LINE_WIDTH*8-1;
parameter OVM_LARGE_STRING = OVM_LINE_WIDTH*OVM_NUM_LINES*8-1;


//----------------------------------------------------------------------------
//
// Function: ovm_string_to_bits
//
// Converts an input string to its bit-vector equivalent. Max bit-vector
// length is approximately 14000 characters.
//----------------------------------------------------------------------------

function logic[OVM_LARGE_STRING:0] ovm_string_to_bits(string str);
  $swrite(ovm_string_to_bits, "%0s", str);
endfunction


//----------------------------------------------------------------------------
//
// Function: ovm_bits_to_string
//
// Converts an input bit-vector to its string equivalent. Max bit-vector
// length is approximately 14000 characters.
//----------------------------------------------------------------------------

function string ovm_bits_to_string(logic [OVM_LARGE_STRING:0] str);
  $swrite(ovm_bits_to_string, "%0s", str);
endfunction


//----------------------------------------------------------------------------
//
// Task: ovm_wait_for_nba_region
//
// Call this task to wait for a delta cycle. Program blocks don't have an nba
// so just delay for a #0 in a program block.
//----------------------------------------------------------------------------

task ovm_wait_for_nba_region;

  string s;

  bit nba;
  bit nba_scheduled;

  //If `included directly in a program block, can't use a non-blocking assign,
  //but it isn't needed since program blocks are in a seperate region.
`ifndef OVM_PROGRAM_BLOCK
  if (nba_scheduled == 0) begin
    nba_scheduled = 1;
    nba = 0;
    nba <= 1;
    @(posedge nba) nba_scheduled = 0;
  end
  else begin
    @(posedge nba);
  end
`else
  #0;
`endif


endtask


