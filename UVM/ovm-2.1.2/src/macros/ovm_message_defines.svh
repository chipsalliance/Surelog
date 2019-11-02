//----------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
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
//----------------------------------------------------------------------

`ifndef OVM_MESSAGE_DEFINES_SVH
`define OVM_MESSAGE_DEFINES_SVH

`ifndef OVM_LINE_WIDTH
  `define OVM_LINE_WIDTH 120
`endif 

`ifndef OVM_NUM_LINES
  `define OVM_NUM_LINES 120
`endif

`ifdef INCA
`define OVM_REPORT_DISABLE_FILE_LINE
`endif

`ifdef OVM_REPORT_DISABLE_FILE_LINE
`define OVM_REPORT_DISABLE_FILE
`define OVM_REPORT_DISABLE_LINE
`endif

`ifdef OVM_REPORT_DISABLE_FILE
`define ovm_file ""
`else
`define ovm_file `__FILE__
`endif

`ifdef OVM_REPORT_DISABLE_LINE
`define ovm_line 0
`else
`define ovm_line `__LINE__
`endif


//------------------------------------------------------------------------------
//
// Title: Report Macros 
//
// This set of macros provides wrappers around the ovm_report_* <Reporting> 
// functions. The macros serve two essential purposes:
//
// - To reduce the processing overhead associated with filtered out messages,
//   a check is made against the report's verbosity setting and the action
//   for the id/severity pair before any string formatting is performed. This 
//   affects only `ovm_info reports.
//
// - The `__FILE__ and `__LINE__ information is automatically provided to the
//   underlying ovm_report_* call. Having the file and line number from where
//   a report was issued aides in debug. You can disable display of file and
//   line information in reports by defining OVM_DISABLE_REPORT_FILE_LINE on
//   the command line.
//
// The macros also enforce a verbosity setting of OVM_NONE for warnings, errors
// and fatals so that they cannot be mistakingly turned off by setting the
// verbosity level too low (warning and errors can still be turned off by 
// setting the actions appropriately).
//
// To use the macros, replace the previous call to ovm_report_* with the
// corresponding macro.
//
//| //Previous calls to ovm_report_*
//| ovm_report_info("MYINFO1", $sformatf("val: %0d", val), OVM_LOW);
//| ovm_report_warning("MYWARN1", "This is a warning");
//| ovm_report_error("MYERR", "This is an error");
//| ovm_report_fatal("MYFATAL", "A fatal error has occurred");
//
// The above code is replaced by
//
//| //New calls to `ovm_*
//| `ovm_info("MYINFO1", $sformatf("val: %0d", val), OVM_LOW)
//| `ovm_warning("MYWARN1", "This is a warning")
//| `ovm_error("MYERR", "This is an error")
//| `ovm_fatal("MYFATAL", "A fatal error has occurred")
//
// Macros represent text substitutions, not statements, so they should not be
// terminated with semi-colons.


// MACRO: `ovm_info
//
// Calls ovm_report_info if ~VERBOSITY~ is lower than the configured verbosity of
// the associated reporter. ~ID~ is given as the message tag and ~MSG~ is given as
// the message text. The file and line are also sent to the ovm_report_info call.
//

`define ovm_info(ID, MSG, VERBOSITY) \
   begin \
     if (ovm_report_enabled(VERBOSITY,OVM_INFO,ID)) \
       ovm_report_info (ID, MSG, VERBOSITY, `ovm_file, `ovm_line); \
   end

// MACRO: `ovm_warning
//
// Calls ovm_report_warning with a verbosity of OVM_NONE. The message can not
// be turned off using the reporter's verbosity setting, but can be turned off
// by setting the action for the message.  ~ID~ is given as the message tag and 
// ~MSG~ is given as the message text. The file and line are also sent to the 
// ovm_report_warning call.

`define ovm_warning(ID,MSG) \
   begin \
     if (ovm_report_enabled(OVM_NONE,OVM_WARNING,ID)) \
       ovm_report_warning (ID, MSG, OVM_NONE, `ovm_file, `ovm_line); \
   end

// MACRO: `ovm_error
//
// Calls ovm_report_error with a verbosity of OVM_NONE. The message can not
// be turned off using the reporter's verbosity setting, but can be turned off
// by setting the action for the message.  ~ID~ is given as the message tag and 
// ~MSG~ is given as the message text. The file and line are also sent to the 
// ovm_report_error call.

`define ovm_error(ID,MSG) \
   begin \
     if (ovm_report_enabled(OVM_NONE,OVM_ERROR,ID)) \
       ovm_report_error (ID, MSG, OVM_NONE, `ovm_file, `ovm_line); \
   end

// MACRO: `ovm_fatal
//
// Calls ovm_report_fatal with a verbosity of OVM_NONE. The message can not
// be turned off using the reporter's verbosity setting, but can be turned off
// by setting the action for the message.  ~ID~ is given as the message tag and 
// ~MSG~ is given as the message text. The file and line are also sent to the 
// ovm_report_fatal call.

`define ovm_fatal(ID,MSG) \
   begin \
     if (ovm_report_enabled(OVM_NONE,OVM_FATAL,ID)) \
       ovm_report_fatal (ID, MSG, OVM_NONE, `ovm_file, `ovm_line); \
   end




// DEPRECATED - The following macros are deprecated in favor of the `ovm_info,
// `ovm_warning, `ovm_error, and `ovm_fatal.

`define OVM_REPORT_INFO(ID,MSG) \
  ovm_report_info(ID,MSG,OVM_MEDIUM,`ovm_file,`ovm_line)

`define OVM_REPORT_WARNING(ID,MSG) \
  ovm_report_warning(ID,MSG,OVM_MEDIUM,`ovm_file,`ovm_line)

`define OVM_REPORT_ERROR(ID,MSG) \
  ovm_report_error(ID,MSG,OVM_LOW,`ovm_file,`ovm_line)

`define OVM_REPORT_FATAL(ID,MSG) \
  ovm_report_fatal(ID,MSG,OVM_NONE,`ovm_file,`ovm_line)

`endif //OVM_MESSAGE_DEFINES_SVH
