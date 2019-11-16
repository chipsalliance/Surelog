// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_object_globals.svh#12 $
//------------------------------------------------------------------------------
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
//------------------------------------------------------------------------------

//This bit marks where filtering should occur to remove ovm stuff from a
//scope
bit ovm_start_ovm_declarations = 1;

//------------------------------------------------------------------------------
//
// Section: Types and Enumerations
//
//------------------------------------------------------------------------------

`ifndef OVM_MAX_STREAMBITS
`define OVM_MAX_STREAMBITS 4096
`endif


// Current problem with large vector inout decls.

parameter OVM_STREAMBITS = `OVM_MAX_STREAMBITS; 


// Type: ovm_bitstream_t
//
// The bitstream type is used as a argument type for passing integral values
// in such methods as set_int_local, get_int_local, get_config_int, report,
// pack and unpack.

typedef logic signed [OVM_STREAMBITS-1:0] ovm_bitstream_t;



// Enum: ovm_radix_enum
//
// OVM_BIN       - Selects binary (%b) format
// OVM_DEC       - Selects decimal (%d) format
// OVM_UNSIGNED  - Selects unsigned decimal (%u) format
// OVM_OCT       - Selects octal (%o) format
// OVM_HEX       - Selects hexidecimal (%h) format
// OVM_STRING    - Selects string (%s) format
// OVM_TIME      - Selects time (%t) format
// OVM_ENUM      - Selects enumeration value (name) format

typedef enum {
   OVM_BIN       = 'h1000000,
   OVM_DEC       = 'h2000000,
   OVM_UNSIGNED  = 'h3000000,
   OVM_OCT       = 'h4000000,
   OVM_HEX       = 'h5000000,
   OVM_STRING    = 'h6000000,
   OVM_TIME      = 'h7000000,
   OVM_ENUM      = 'h8000000,
   OVM_NORADIX   = 0
} ovm_radix_enum;

parameter OVM_RADIX = 'hf000000; //4 bits setting the radix


// Function- ovm_radix_to_string

function string ovm_radix_to_string(ovm_radix_enum radix);
  case(radix)
    OVM_BIN:     return "'b";
    OVM_OCT:     return "'o";
    OVM_DEC:     return "'s";
    OVM_TIME:    return "'u";
    OVM_STRING:  return "'a";
    default: return "'x";
  endcase
endfunction

// Enum: ovm_recursion_policy_enum
//
// OVM_DEEP      - Objects are deep copied (object must implement copy method)
// OVM_SHALLOW   - Objects are shallow copied using default SV copy.
// OVM_REFERENCE - Only object handles are copied.

typedef enum { 
  OVM_DEFAULT_POLICY = 0, 
  OVM_DEEP           = 'h400, 
  OVM_SHALLOW        = 'h800, 
  OVM_REFERENCE      = 'h1000
 } ovm_recursion_policy_enum;



// Parameters

parameter OVM_MACRO_NUMFLAGS    = 17;
//A=ABSTRACT Y=PHYSICAL
//F=REFERENCE, S=SHALLOW, D=DEEP
//K=PACK, R=RECORD, P=PRINT, M=COMPARE, C=COPY
//--------------------------- AYFSD K R P M C
parameter OVM_DEFAULT     = 'b000010101010101;
parameter OVM_ALL_ON      = 'b000000101010101;
parameter OVM_FLAGS_ON    = 'b000000101010101;
parameter OVM_FLAGS_OFF   = 0;

//Values are or'ed into a 32 bit value
//and externally
parameter OVM_COPY         = (1<<0);
parameter OVM_NOCOPY       = (1<<1);
parameter OVM_COMPARE      = (1<<2);
parameter OVM_NOCOMPARE    = (1<<3);
parameter OVM_PRINT        = (1<<4);
parameter OVM_NOPRINT      = (1<<5);
parameter OVM_RECORD       = (1<<6);
parameter OVM_NORECORD     = (1<<7);
parameter OVM_PACK         = (1<<8);
parameter OVM_NOPACK       = (1<<9);
//parameter OVM_DEEP         = (1<<10);
//parameter OVM_SHALLOW      = (1<<11);
//parameter OVM_REFERENCE    = (1<<12);
parameter OVM_PHYSICAL     = (1<<13);
parameter OVM_ABSTRACT     = (1<<14);
parameter OVM_READONLY     = (1<<15);
parameter OVM_NODEFPRINT   = (1<<16);

//Extra values that are used for extra methods
parameter OVM_MACRO_EXTRAS  = (1<<OVM_MACRO_NUMFLAGS);
parameter OVM_FLAGS        = OVM_MACRO_EXTRAS+1;
parameter OVM_UNPACK       = OVM_MACRO_EXTRAS+2;
parameter OVM_CHECK_FIELDS = OVM_MACRO_EXTRAS+3;
parameter OVM_END_DATA_EXTRA = OVM_MACRO_EXTRAS+4;


//Get and set methods (in ovm_object). Used by the set/get* functions
//to tell the object what operation to perform on the fields.
parameter OVM_START_FUNCS  = OVM_END_DATA_EXTRA+1;
parameter OVM_SET           = OVM_START_FUNCS+1;
parameter OVM_SETINT        = OVM_SET;
parameter OVM_SETOBJ        = OVM_START_FUNCS+2;
parameter OVM_SETSTR        = OVM_START_FUNCS+3;
parameter OVM_END_FUNCS     = OVM_SETSTR;

//Global string variables
string ovm_aa_string_key;



// Group: Reporting


// Enum: ovm_severity
//
// Defines all possible values for report severity.
//
//   OVM_INFO    - Informative messsage.
//   OVM_WARNING - Indicates a potential problem.
//   OVM_ERROR   - Indicates a real problem. Simulation continues subject
//                 to the configured message action.
//   OVM_FATAL   - Indicates a problem from which simulation can not
//                 recover. Simulation exits via $finish after a #0 delay.

typedef bit [1:0] ovm_severity;

typedef enum ovm_severity
{
  OVM_INFO,
  OVM_WARNING,
  OVM_ERROR,
  OVM_FATAL
} ovm_severity_type;


// Enum: ovm_action
//
// Defines all possible values for report actions. Each report is configured
// to execute one or more actions, determined by the bitwise OR of any or all
// of the following enumeration constants.
//
//   OVM_NO_ACTION - No action is taken
//   OVM_DISPLAY   - Sends the report to the standard output
//   OVM_LOG       - Sends the report to the file(s) for this (severity,id) pair
//   OVM_COUNT     - Counts the number of reports with the COUNT attribute.
//                   When this value reaches max_quit_count, the simulation terminates
//   OVM_EXIT      - Terminates the simulation immediately.
//   OVM_CALL_HOOK - Callback the report hook methods 


`ifndef IUS_SVPP_LIMIT

typedef bit [5:0] ovm_action;

typedef enum ovm_action
{
  OVM_NO_ACTION = 6'b000000,
  OVM_DISPLAY   = 6'b000001,
  OVM_LOG       = 6'b000010,
  OVM_COUNT     = 6'b000100,
  OVM_EXIT      = 6'b001000,
  OVM_CALL_HOOK = 6'b010000,
  OVM_STOP      = 6'b100000
} ovm_action_type;

`else

typedef int ovm_action;

typedef enum
{
  OVM_NO_ACTION = 'b000000,
  OVM_DISPLAY   = 'b000001,
  OVM_LOG       = 'b000010,
  OVM_COUNT     = 'b000100,
  OVM_EXIT      = 'b001000,
  OVM_CALL_HOOK = 'b010000,
  OVM_STOP      = 'b100000
} ovm_action_type;

`endif


// Enum: ovm_verbosity
//
// Defines standard verbosity levels for reports.
//
//  OVM_NONE   - Report is always printed. Verbosity level setting can not
//               disable it.
//  OVM_LOW    - Report is issued if configured verbosity is set to OVM_LOW
//               or above.
//  OVM_MEDIUM - Report is issued if configured verbosity is set to OVM_MEDIUM
//               or above.
//  OVM_HIGH   - Report is issued if configured verbosity is set to OVM_HIGH
//               or above.
//  OVM_FULL   - Report is issued if configured verbosity is set to OVM_FULL
//               or above.

typedef enum {
  OVM_NONE   = 0,
  OVM_LOW    = 100,
  OVM_MEDIUM = 200,
  OVM_HIGH   = 300,
  OVM_FULL   = 400,
  OVM_DEBUG  = 500
} ovm_verbosity;

typedef int OVM_FILE;
typedef ovm_action id_actions_array[string];
typedef OVM_FILE id_file_array[string];

ovm_action s_default_action_array[string]; // default is already NO_ACTION
OVM_FILE s_default_file_array[string]; // default is already 0


// Group: Port Type

// Enum: ovm_port_type_e
//
// OVM_PORT           - The port requires the interface that is its type
//                      parameter.
// OVM_EXPORT         - The port provides the interface that is its type
//                      parameter via a connection to some other export or
//                      implementation.
// OVM_IMPLEMENTATION - The port provides the interface that is its type
//                      parameter, and it is bound to the component that
//                      implements the interface.

typedef enum {
  OVM_PORT ,
  OVM_EXPORT ,
  OVM_IMPLEMENTATION
} ovm_port_type_e;


// Group: Sequences

// Enum: ovm_sequence_state_enum
//
// CREATED            - The sequence has been allocated.
// PRE_BODY           - The sequence is started and the pre_body task is
//                      being executed.
// BODY               - The sequence is started and the body task is being
//                      executed.
// POST_BODY          - The sequence is started and the post_body task is
//                      being executed.
// ENDED              - The sequence has ended by the completion of the body
//                      task.
// STOPPED            - The sequence has been forcibly ended by issuing a
//                      kill() on the sequence.
// FINISHED           - The sequence is completely finished executing.

typedef enum { CREATED   = 1,
               PRE_BODY  = 2,
               BODY      = 4,
               POST_BODY = 8,
               ENDED     = 16,
               STOPPED   = 32,
               FINISHED  = 64} ovm_sequence_state_enum;



//------------------------------------------------------------------------------
//
// Group: Default Policy Classes
//
// Policy classes for <ovm_object> basic functions, <ovm_object::copy>,
// <ovm_object::compare>, <ovm_object::pack>, <ovm_object::unpack>, and
// <ovm_object::record>.
//
//------------------------------------------------------------------------------

typedef class ovm_printer;
typedef class ovm_table_printer;
typedef class ovm_tree_printer;
typedef class ovm_line_printer;
typedef class ovm_comparer;
typedef class ovm_packer;
typedef class ovm_recorder;

// Variable: ovm_default_table_printer
//
// The table printer is a global object that can be used with
// <ovm_object::do_print> to get tabular style printing.

ovm_table_printer ovm_default_table_printer = new();


// Variable: ovm_default_tree_printer
//
// The tree printer is a global object that can be used with
// <ovm_object::do_print> to get multi-line tree style printing.

ovm_tree_printer ovm_default_tree_printer  = new();


// Variable: ovm_default_line_printer
//
// The line printer is a global object that can be used with
// <ovm_object::do_print> to get single-line style printing.

ovm_line_printer ovm_default_line_printer  = new();


// Variable: ovm_default_printer
//
// The default printer is a global object that is used by <ovm_object::print>
// or <ovm_object::sprint> when no specific printer is set. 
//
// The default printer may be set to any legal <ovm_printer> derived type,
// including the global line, tree, and table printers described above.

ovm_printer ovm_default_printer = ovm_default_table_printer;


// Variable: ovm_default_packer
//
// The default packer policy. If a specific packer instance is not supplied in
// calls to <ovm_object::pack> and <ovm_object::unpack>, this instance is
// selected.

ovm_packer ovm_default_packer = new();


// Variable: ovm_default_comparer
//
//
// The default compare policy. If a specific comparer instance is not supplied
// in calls to <ovm_object::compare>, this instance is selected.

ovm_comparer ovm_default_comparer = new(); // ovm_comparer::init();


// Variable: ovm_default_recorder
//
// The default recording policy. If a specific recorder instance is not
// supplied in calls to <ovm_object::record>.

ovm_recorder ovm_default_recorder = new();





