// $Id: //dvt/vtech/dev/main/ovm/src/compatibility/urm_message.svh#24 $
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

`ifndef OVM_URM_MESSAGE_SVH
`define OVM_URM_MESSAGE_SVH

`include "base/ovm_object.svh"
`include "compatibility/urm_message_defines.svh"

typedef class ovm_printer;

/* Message related types and globals */

typedef enum {
  OVM_URM_STYLE_NONE         = 0,
  OVM_URM_STYLE_FILE         = 'b0000000001,
  OVM_URM_STYLE_HIERARCHY    = 'b0000000010,
  OVM_URM_STYLE_LINE         = 'b0000000100,
  OVM_URM_STYLE_MESSAGE_TEXT = 'b0000001000,
  OVM_URM_STYLE_SCOPE        = 'b0000010000,
  OVM_URM_STYLE_SEVERITY     = 'b0000100000,
  OVM_URM_STYLE_TAG          = 'b0001000000,
  OVM_URM_STYLE_TIME         = 'b0010000000,
  OVM_URM_STYLE_UNIT         = 'b0100000000,
  OVM_URM_STYLE_VERBOSITY    = 'b1000000000
} urm_msg_style_flags_enum;

typedef enum {
  OVM_URM_SHORT = 'b0010001010,
  OVM_URM_LONG  = 'b1110011111,
  OVM_URM_RAW   = 'b0000001000
} urm_msg_style_enum;

typedef enum {
  OVM_URM_MSG_DEBUG,
  OVM_URM_MSG_DUT,
  OVM_URM_MSG_TOOL,
  OVM_URM_MSG_OVM
} urm_msg_type;

string urm_global_tmp_str="";

// global variables
// ----------------

string urm_global_msg_detail_str;

typedef class urm_command_line_processor_c;


`ifdef INCA
urm_command_line_processor_c urm_command_line_processor = new;
`endif

typedef class ovm_urm_report_server;
ovm_urm_report_server ovm_global_urm_report_server;

string ovm_urm_tmp_str="";

parameter OVM_UNDEF = -1;


//------------------------------------------------------------------------------
//
// MESSAGE Control 
//
// interim message handling
//
//------------------------------------------------------------------------------


// urm_continue (global)
// ------------

function void urm_continue();
endfunction


// urm_stop_run (global)
// ------------

typedef class ovm_component;
function void urm_stop_run();
  fork
    ovm_top.stop_request();
  join_none
endfunction


// urm_finish (global)
// ----------

function void urm_finish();
  fork
    $finish();
  join_none
endfunction


// urm_stop (global)
// --------

function void urm_stop();
  fork
    $stop();
  join_none
endfunction



//------------------------------------------------------------------------------
//
// CLASS- ovm_urm_message_format -- INTERIM SOLUTION: SUBJECT TO CHANGE
//
// simple container of user-settable parameters for governing
// message header output. 
//------------------------------------------------------------------------------


class ovm_urm_message_format;

  static string info_prefix     = `ANSI_FG_BLACK;
  static string warning_prefix  = `ANSI_FG_GREEN;
  static string error_prefix    = {`ANSI_FG_RED,`ANSI_BOLD};
  static string fatal_prefix    = {`ANSI_FG_RED,`ANSI_BOLD};
  static string time1_prefix    = {"[",`ANSI_FG_BLACK,`ANSI_BRIGHT};
  static string time2_prefix    = {"[",`ANSI_FG_BLACK};

  static string info_postfix    = `ANSI_RESET;
  static string warning_postfix = `ANSI_RESET;
  static string error_postfix   = `ANSI_RESET;
  static string fatal_postfix   = `ANSI_RESET;
  static string time1_postfix   = {`ANSI_RESET,"]"};
  static string time2_postfix   = {`ANSI_RESET,"]"};

  static string short_text      = "SHORT";
  static string long_text       = "LONG";
  static string raw_text        = "RAW";

  static string info0_text      = "";
  static string info1_text      = "OVM_LOW";
  static string info2_text      = "OVM_MEDIUM";
  static string info3_text      = "OVM_HIGH";
  static string info4_text      = "OVM_FULL";

  static string info_text       = "INFO";
  static string warning_text    = "WARNING";
  static string error_text      = "ERROR";
  static string fatal_text      = "FATAL";

  static string none_text       = "NONE";
  static string low_text        = "LOW";
  static string medium_text     = "MEDIUM";
  static string high_text       = "HIGH";
  static string full_text       = "FULL";

  static string separator       = " -- ";

  static bit    enable_ansi_colors     = 0;

endclass


//----------------------------------------------------------------------
// CLASS ovm_urm_message
//----------------------------------------------------------------------
class ovm_urm_message;

  string m_id;
  string m_text;
  int m_type;
  ovm_severity m_severity;
  int m_verbosity;
  int m_max_verbosity;
  int m_style;
  ovm_report_object m_client;
  string m_file;
  int m_line;
  int m_action;
  int m_destination;
  string m_scope;
  string m_hierarchy;
  string m_name;

  extern function new(
    string id, string text, int typ, ovm_severity sev, int verbosity, string hier,
    ovm_report_object client, string file, int line, string scope
  );

endclass



//----------------------------------------------------------------------------
//
// CLASS- ovm_urm_override_request
//
//----------------------------------------------------------------------------

typedef class ovm_urm_override_operator;

class ovm_urm_override_request extends ovm_object;
   string                match_hierarchy;
   string                match_scope;
   string                match_name;
   string                match_file;
   int                   match_line;
   string                match_text;
   string                match_tag;
   ovm_urm_override_operator operator;

   extern function bit    is_applicable_to_message(ovm_urm_message msg);
   extern function void   apply_override(ovm_urm_message msg);
   extern function string dump_request_details();

   // type functions
   function bit is_style_override();       
                         return operator.is_style_override();       endfunction

   function bit is_verbosity_override();   
                         return operator.is_verbosity_override();   endfunction

   function bit is_destination_override(); 
                         return operator.is_destination_override(); endfunction

   function bit is_severity_override();    
                         return operator.is_severity_override();    endfunction

   function bit is_action_override();      
                         return operator.is_action_override();      endfunction

   // Constructor
   extern function new ( string hierarchy="", 
			 string scope="", 
			 string name="", 
			 string file="",
			 int    line=-1,
			 string text="",
			 string tag="",
			 ovm_urm_override_operator op=null);

  function string get_type_name();
    return "ovm_urm_override_request";
  endfunction
 
  function ovm_object create(string name="");
    ovm_urm_override_request mh; mh = new;
    mh.set_name(name);
    return mh;
  endfunction

  function void do_print(ovm_printer printer);
    printer.print_string("match_hierarchy", match_hierarchy);
    printer.print_string("match_scope", match_scope);
    printer.print_string("match_name", match_name);
    printer.print_string("match_file", match_file);
    printer.print_field("match_line", match_line, $bits(match_line));
    printer.print_string("match_text", match_text);
    printer.print_string("match_tag", match_tag);
    printer.print_object("operator", operator);
  endfunction 

  function bit do_compare(ovm_object rhs, ovm_comparer comparer);
    ovm_urm_override_request rhs_;
    if ( rhs == this ) return 1;
    if ( rhs == null ) return 0;
    if(!$cast(rhs_, rhs)) return 0;

    if ( match_hierarchy != rhs_.match_hierarchy ) return 0;
    if ( match_scope != rhs_.match_scope ) return 0;
    if ( match_name != rhs_.match_name ) return 0;
    if ( match_file != rhs_.match_file ) return 0;
    if ( match_line != rhs_.match_line ) return 0;
    if ( match_text != rhs_.match_text ) return 0;
    if ( match_tag != rhs_.match_tag ) return 0;

    return operator.do_compare(rhs_.operator,comparer);
  endfunction
endclass



//----------------------------------------------------------------------------
//
// CLASS- ovm_urm_override_operator
//
//----------------------------------------------------------------------------


class ovm_urm_override_operator extends ovm_object;

   // attributes
   protected int        m_style;
   protected int        m_verbosity;
   protected int        m_destination;
   protected ovm_severity   m_severity;
   protected int        m_action;
   protected ovm_severity   m_severity_for_action;

   // enable flags, hold 1 for attributes to apply
   protected bit 	m_enable_style; 
   protected bit 	m_enable_verbosity;
   protected bit 	m_enable_destination;
   protected bit 	m_enable_severity;
   protected bit 	m_enable_action;

   extern function void   apply_overrides(ovm_urm_message msg);
   extern function string dump_override_details();

   // type functions
   function bit is_style_override();       return m_enable_style;       endfunction
   function bit is_verbosity_override();   return m_enable_verbosity;   endfunction
   function bit is_destination_override(); return m_enable_destination; endfunction
   function bit is_severity_override();    return m_enable_severity;    endfunction
   function bit is_action_override();      return m_enable_action;      endfunction

   // get_* functions
   function int       get_style();               return m_style;               endfunction
   function int       get_verbosity();           return m_verbosity;           endfunction
   function int       get_destination();         return m_destination;         endfunction
   function ovm_severity  get_severity();            return m_severity;            endfunction
   function int       get_action();              return m_action;              endfunction
   function ovm_severity  get_severity_for_action(); return m_severity_for_action; endfunction

   // set_* functions
   function bit set_style(int s);
      m_style = s;
      m_enable_style = 1;
      return(1);
   endfunction

   function bit set_verbosity(int v);
      m_verbosity = v;
      m_enable_verbosity = 1;
      return(1);
   endfunction

   function bit set_destination(int d);
      m_destination = d;
      m_enable_destination = 1;
      return(1);
   endfunction

   function bit set_severity(ovm_severity s);
      m_severity = s;
      m_enable_severity = 1;      
      return(1);
   endfunction

   function bit set_action(ovm_severity s, int action);
      if ((ovm_severity_type'(s) == OVM_FATAL) && ((ovm_action_type'(action) & OVM_EXIT) == 0)) begin
         $display("Error: cannot remove EXIT from the action set of messages with FATAL severity. Ignoring.");
         //## how to print the above?
         return(0);
      end
      else begin 
         m_action = action;
         m_severity_for_action = s;
         m_enable_action = 1;
         return(1);
      end
   endfunction

   function string get_type_name();
     return "ovm_urm_override_operator";
   endfunction
   function ovm_object create(string name="");
      ovm_urm_override_operator o;
      o = new;
      o.set_name(name);
      return o;
   endfunction
   function void do_print(ovm_printer printer);
     printer.print_field("m_style", m_style, $bits(m_style));
     printer.print_field("m_verbosity", m_verbosity, $bits(m_verbosity));
     printer.print_field("m_destination", m_destination, $bits(m_destination));
     printer.print_field("m_severity", m_severity, $bits(m_severity));
     printer.print_field("m_action", m_action, $bits(m_action));
     printer.print_field("m_severity_for_action", m_severity_for_action, $bits(m_severity_for_action));
     printer.print_field("m_enable_style", m_enable_style, $bits(m_enable_style));
     printer.print_field("m_enable_verbosity", m_enable_verbosity, $bits(m_enable_verbosity));
     printer.print_field("m_enable_destination", m_enable_destination, $bits(m_enable_destination));
     printer.print_field("m_enable_severity", m_enable_severity, $bits(m_enable_severity));
     printer.print_field("m_enable_action", m_enable_action, $bits(m_enable_action));
   endfunction

   function void do_copy(ovm_object rhs);
     ovm_urm_override_operator rhs_;
     if((rhs == null) || (rhs==this)) return;
     if(!$cast(rhs_, rhs)) return;

     m_style = rhs_.m_style;
     m_verbosity = rhs_.m_verbosity;
     m_destination = rhs_.m_destination;
     m_severity = rhs_.m_severity;
     m_action = rhs_.m_action;
     m_severity_for_action = rhs_.m_severity_for_action;
     m_enable_style = rhs_.m_enable_style;
     m_enable_verbosity = rhs_.m_enable_verbosity;
     m_enable_destination = rhs_.m_enable_destination;
     m_enable_severity = rhs_.m_enable_severity;
     m_enable_action = rhs_.m_enable_action;
   endfunction

   function bit do_compare(ovm_object rhs, ovm_comparer comparer);
     ovm_urm_override_operator rhs_;
     if ( rhs == this ) return 1;
     if ( rhs == null ) return 0;
     if(!$cast(rhs_, rhs)) return 0;

     if ( m_style != rhs_.m_style ) return 0;
     if ( m_verbosity != rhs_.m_verbosity ) return 0;
     if ( m_destination != rhs_.m_destination ) return 0;
     if ( m_severity != rhs_.m_severity ) return 0;
     if ( m_action != rhs_.m_action ) return 0;
     if ( m_severity_for_action != rhs_.m_severity_for_action ) return 0;
     if ( m_enable_style != rhs_.m_enable_style ) return 0;
     if ( m_enable_verbosity != rhs_.m_enable_verbosity ) return 0;
     if ( m_enable_destination != rhs_.m_enable_destination ) return 0;
     if ( m_enable_severity != rhs_.m_enable_severity ) return 0;

     return ( m_enable_action == rhs_.m_enable_action );
   endfunction
endclass



//----------------------------------------------------------------------
// CLASS ovm_urm_report_server
//
// Replacement server which preserves normal OVM API while
// including some API available in URM
//----------------------------------------------------------------------

class ovm_urm_report_server extends ovm_report_server;

  static bit m_initialized;
  static int m_global_debug_style;
  static string m_global_hier;
  static string m_global_scope;
  static ovm_severity m_global_severity;
  static int m_global_default_type;
  static int m_global_type;

  protected static ovm_urm_override_request m_override_requests[$];

  extern function new();

  extern virtual function void report(
    ovm_severity severity,
    string name,
    string id,
    string message,
    int verbosity_level,
    string filename,
    int line,
    ovm_report_object client
  );

  /* max_quit_count */
  extern static function int get_global_max_quit_count();
  extern static function void set_global_max_quit_count(int value);

  /* style */
  extern static function int get_global_debug_style();
  extern static function void set_global_debug_style(int value);
  extern static function void set_message_debug_style(
    string hierarchy,    // wildcard for message hierarchy, default "*"
    string scope,        // wildcard for message scope, default "*"
    string name,         // wildcard for message name, default "*"
    string file,         // wildcard for file name, default "*"
    int line,            // wildcard for line number, default -1 (matches all)
    string text,         // wildcard for message text, default "*"
    string tag,          // wildcard for message tag, default "*"
    bit remove,          // FALSE --> add rule, TRUE --> remove it
    int value
  );

  /* verbosity */
  extern static function int get_global_verbosity();
  extern static function void set_global_verbosity(int value);
  extern static function void set_message_verbosity(
    string hierarchy,    // wildcard for message hierarchy, default "*"
    string scope,        // wildcard for message scope, default "*"
    string name,         // wildcard for message name, default "*"
    string file,         // wildcard for file name, default "*"
    int line,            // wildcard for line number, default -1 (matches all)
    string text,         // wildcard for message text, default "*"
    string tag,          // wildcard for message tag, default "*"
    bit remove,          // FALSE --> add rule, TRUE --> remove it
    int value
  );

  /* destination */
  extern static function int get_global_destination();
  extern static function void set_global_destination(int value);
  extern static function void set_message_destination(
    string hierarchy,    // wildcard for message hierarchy, default "*"
    string scope,        // wildcard for message scope, default "*"
    string name,         // wildcard for message name, default "*"
    string file,         // wildcard for file name, default "*"
    int line,            // wildcard for line number, default -1 (matches all)
    string text,         // wildcard for message text, default "*"
    string tag,          // wildcard for message tag, default "*"
    bit remove,          // FALSE --> add rule, TRUE --> remove it
    int value
  );

  /* severity */
  extern static function ovm_severity get_global_severity();
  extern static function void set_global_severity(ovm_severity value);
  extern static function void set_message_severity(
    string hierarchy,    // wildcard for message hierarchy, default "*"
    string scope,        // wildcard for message scope, default "*"
    string name,         // wildcard for message name, default "*"
    string file,         // wildcard for file name, default "*"
    int line,            // wildcard for line number, default -1 (matches all)
    string text,         // wildcard for message text, default "*"
    string tag,          // wildcard for message tag, default "*"
    bit remove,          // FALSE --> add rule, TRUE --> remove it
    ovm_severity value
  );

  /* action */
  extern static function int get_global_actions(ovm_severity sev);
  extern static function void set_global_actions(ovm_severity sev, int value);
  extern static function void set_message_actions(
    string hierarchy,    // wildcard for message hierarchy, default "*"
    string scope,        // wildcard for message scope, default "*"
    string name,         // wildcard for message name, default "*"
    string file,         // wildcard for file name, default "*"
    int line,            // wildcard for line number, default -1 (matches all)
    string text,         // wildcard for message text, default "*"
    string tag,          // wildcard for message tag, default "*"
    bit remove,          // FALSE --> add rule, TRUE --> remove it
    ovm_severity severity_val,
    int value
  );

  /* activate URM message server */
  extern static function void init_urm_report_server();

  /* set type used in direct ovm_report_* calls */
  extern static function void set_default_report_type(int value);

  /* internal API */
  extern static function bit m_message_header(ovm_urm_message message);
  extern static function bit m_message_subheader(ovm_urm_message message);
  extern static function void m_message_footer(ovm_urm_message message);
  extern static function void m_set_report_hier(string hier);
  extern static function void m_set_report_scope(string scope);
  extern static function void m_set_report_type(int typ);
  extern static function void m_reset_report_flags();

  extern static function string m_dump_global_debug_style();
  extern static function string m_dump_rules_debug_style();
  extern static function string m_dump_global_verbosity();
  extern static function string m_dump_rules_verbosity();
  extern static function string m_dump_global_destination();
  extern static function string m_dump_rules_destination();
  extern static function string m_dump_global_severity();
  extern static function string m_dump_rules_severity();
  extern static function string m_dump_global_actions();
  extern static function string m_dump_rules_actions();

  extern static protected function void m_handle_new_request(
    ovm_urm_override_request new_req, bit remove
  );
  extern static protected function int m_find_last_matching_request_loc(
    ovm_urm_override_request req
  );
  extern static protected function void m_apply_override_requests(ovm_urm_message msg);

endclass

function ovm_report_object m_get_report_object();
  return _global_reporter;
endfunction

function string get_full_name();
  return "";
endfunction

function void set_checks(int verbosity);
  ovm_urm_report_server::set_global_verbosity(verbosity);
endfunction


//----------------------------------------------------------------------------
//
// CLASS- urm_command_line_processor
//
//----------------------------------------------------------------------------

class urm_command_line_processor_c;

  ovm_root top;
  int verbosity_val;
  ovm_severity severity_val;
  bit use_severity, use_verbosity, use_urm;

  function new;

    int int_val;
    string severity_str;

    use_severity = 0;
    use_verbosity = 0;
    use_urm = 0;

    verbosity_val = OVM_LOW;
    ovm_top.enable_print_topology = 0;

    severity_val = OVM_ERROR;

    if (!ovm_top.enable_print_topology && 
         (ovm_verbosity'(verbosity_val) >= OVM_FULL || $test$plusargs("OVM_VERBOSE")))
      ovm_top.enable_print_topology = 1;

    if ($test$plusargs("USE_URM_MSG"))
      use_urm = 1;

    if ($value$plusargs("MSG_DETAIL=%s",urm_global_msg_detail_str) ||
        $value$plusargs("msg_detail=%s",urm_global_msg_detail_str) ||
        $value$plusargs("OVM_MSG_DETAIL=%s",urm_global_msg_detail_str) ||
        $value$plusargs("ovm_msg_detail=%s",urm_global_msg_detail_str))
    begin
      case (urm_global_msg_detail_str)
        "NONE"   : verbosity_val = OVM_NONE;
        "LOW"    : verbosity_val = OVM_LOW;
        "MEDIUM" : verbosity_val = OVM_MEDIUM;
        "HIGH"   : verbosity_val = OVM_HIGH;
        "FULL"   : verbosity_val = OVM_FULL;
        "DEBUG"  : verbosity_val = OVM_DEBUG;
        "OVM_NONE"   : verbosity_val = OVM_NONE;
        "OVM_LOW"    : verbosity_val = OVM_LOW;
        "OVM_MEDIUM" : verbosity_val = OVM_MEDIUM;
        "OVM_HIGH"   : verbosity_val = OVM_HIGH;
        "OVM_FULL"   : verbosity_val = OVM_FULL;
        "OVM_DEBUG"  : verbosity_val = OVM_DEBUG;
        default  : begin // check for number
          int_val = urm_global_msg_detail_str.atoi();
          if (int_val)
            verbosity_val = int_val;
        end
      endcase
      use_verbosity = 1;
      use_urm = 1;
    end

    if ($value$plusargs("SEVERITY=%s",severity_str) ||
        $value$plusargs("severity=%s",severity_str) ||
        $value$plusargs("OVM_SEVERITY=%s",severity_str) ||
        $value$plusargs("ovm_severity=%s",severity_str) ||
        $value$plusargs("OVM_URM_SEVERITY=%s",severity_str) ||
        $value$plusargs("urm_severity=%s",severity_str)) begin
      case (severity_str)
        "INFO"    : severity_val = OVM_INFO;
        "WARNING" : severity_val = OVM_WARNING;
        "ERROR"   : severity_val = OVM_ERROR;
        "FATAL"   : severity_val = OVM_FATAL;
      endcase
      use_severity = 1;
      use_urm = 1;
    end

    if ( use_urm == 1 ) ovm_urm_report_server::init_urm_report_server();
    if ( use_severity == 1 ) ovm_urm_report_server::set_global_severity(severity_val);
    if ( use_verbosity == 1 ) ovm_urm_report_server::set_global_verbosity(verbosity_val);

    if(use_verbosity)
    begin
      top = ovm_root::get();
      top.set_report_verbosity_level_hier(verbosity_val);
    end
  endfunction

endclass


`endif // OVM_URM_MESSAGE_SVH
