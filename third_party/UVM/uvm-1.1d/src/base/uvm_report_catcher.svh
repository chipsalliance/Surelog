// $Id: uvm_report_catcher.svh,v 1.1.2.10 2010/04/09 15:03:25 janick Exp $
//------------------------------------------------------------------------------
//   Copyright 2007-2010 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
//   Copyright 2010 Synopsys, Inc.
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

`ifndef UVM_REPORT_CATCHER_SVH
`define UVM_REPORT_CATCHER_SVH

typedef class uvm_report_object;
typedef class uvm_report_handler;
typedef class uvm_report_server;
typedef class uvm_report_catcher;

typedef uvm_callbacks    #(uvm_report_object, uvm_report_catcher) uvm_report_cb;
typedef uvm_callback_iter#(uvm_report_object, uvm_report_catcher) uvm_report_cb_iter;

class sev_id_struct;
  bit sev_specified ;
  bit id_specified ;
  uvm_severity sev ;
  string  id ;
  bit is_on ;
endclass

//------------------------------------------------------------------------------
//
// CLASS: uvm_report_catcher
//
// The uvm_report_catcher is used to catch messages issued by the uvm report
// server. Catchers are
// uvm_callbacks#(<uvm_report_object>,uvm_report_catcher) objects,
// so all factilities in the <uvm_callback> and <uvm_callbacks#(T,CB)>
// classes are available for registering catchers and controlling catcher
// state.
// The uvm_callbacks#(<uvm_report_object>,uvm_report_catcher) class is
// aliased to ~uvm_report_cb~ to make it easier to use.
// Multiple report catchers can be 
// registered with a report object. The catchers can be registered as default 
// catchers which catch all reports on all <uvm_report_object> reporters,
// or catchers can be attached to specific report objects (i.e. components). 
//
// User extensions of <uvm_report_catcher> must implement the <catch> method in 
// which the action to be taken on catching the report is specified. The catch 
// method can return ~CAUGHT~, in which case further processing of the report is 
// immediately stopped, or return ~THROW~ in which case the (possibly modified) report 
// is passed on to other registered catchers. The catchers are processed in the order 
// in which they are registered.
//
// On catching a report, the <catch> method can modify the severity, id, action,
// verbosity or the report string itself before the report is finally issued by
// the report server. The report can be immediately issued from within the catcher 
// class by calling the <issue> method.
//
// The catcher maintains a count of all reports with FATAL,ERROR or WARNING severity
// and a count of all reports with FATAL, ERROR or WARNING severity whose severity
// was lowered. These statistics are reported in the summary of the <uvm_report_server>.
//
// This example shows the basic concept of creating a report catching
// callback and attaching it to all messages that get emitted:
//
//| class my_error_demoter extends uvm_report_catcher;
//|   function new(string name="my_error_demoter");
//|     super.new(name);
//|   endfunction
//|   //This example demotes "MY_ID" errors to an info message
//|   function action_e catch();
//|     if(get_severity() == UVM_ERROR && get_id() == "MY_ID")
//|       set_severity(UVM_INFO);
//|     return THROW;
//|   endfunction
//| endclass
//|
//| my_error_demoter demoter = new;
//| initial begin
//|  // Catchers are callbacks on report objects (components are report 
//|  // objects, so catchers can be attached to components).
//|
//|  // To affect all reporters, use null for the object
//|  uvm_report_cb::add(null, demoter); 
//|
//|  // To affect some specific object use the specific reporter
//|  uvm_report_cb::add(mytest.myenv.myagent.mydriver, demoter);
//|
//|  // To affect some set of components using the component name
//|  uvm_report_cb::add_by_name("*.*driver", demoter);
//| end
//
//
//------------------------------------------------------------------------------

virtual class uvm_report_catcher extends uvm_callback;

  `uvm_register_cb(uvm_report_object,uvm_report_catcher)

  typedef enum { UNKNOWN_ACTION, THROW, CAUGHT} action_e;

  local static uvm_severity m_modified_severity;
  local static int m_modified_verbosity;
  local static string m_modified_id;
  local static string m_modified_message;
  local static string m_file_name;
  local static int m_line_number;
  local static uvm_report_object m_client;
  local static uvm_action m_modified_action;
  local static bit m_set_action_called;
  local static uvm_report_server m_server;
  local static string m_name;
  
  local static int m_demoted_fatal;
  local static int m_demoted_error;
  local static int m_demoted_warning;
  local static int m_caught_fatal;
  local static int m_caught_error;
  local static int m_caught_warning;

  const static int DO_NOT_CATCH      = 1; 
  const static int DO_NOT_MODIFY     = 2; 
  local static int m_debug_flags;

  local static  uvm_severity  m_orig_severity;
  local static  uvm_action    m_orig_action;
  local static  string        m_orig_id;
  local static  int           m_orig_verbosity;
  local static  string        m_orig_message;

  local static  bit do_report;
  
  // Function: new
  //
  // Create a new report catcher. The name argument is optional, but
  // should generally be provided to aid in debugging.

  function new(string name = "uvm_report_catcher");
    super.new(name);
    do_report = 1;
  endfunction    

  // Group: Current Message State

  // Function: get_client
  //
  // Returns the <uvm_report_object> that has generated the message that
  // is currently being processes.

  function uvm_report_object get_client();
    return this.m_client; 
  endfunction

  // Function: get_severity
  //
  // Returns the <uvm_severity> of the message that is currently being
  // processed. If the severity was modified by a previously executed
  // catcher object (which re-threw the message), then the returned 
  // severity is the modified value.

  function uvm_severity get_severity();
    return this.m_modified_severity;
  endfunction
  
  // Function: get_context
  //
  // Returns the context (source) of the message that is currently being
  // processed. This is typically the full hierarchical name of the component
  // that issued the message. However, when the message comes via a report
  // handler that is not associated with a component, the context is
  // user-defined.

  function string get_context();
    return this.m_name;
  endfunction
  
  // Function: get_verbosity
  //
  // Returns the verbosity of the message that is currently being
  // processed. If the verbosity was modified by a previously executed
  // catcher (which re-threw the message), then the returned 
  // verbosity is the modified value.
  
  function int get_verbosity();
    return this.m_modified_verbosity;
  endfunction
  
  // Function: get_id
  //
  // Returns the string id of the message that is currently being
  // processed. If the id was modified by a previously executed
  // catcher (which re-threw the message), then the returned 
  // id is the modified value.
  
  function string get_id();
    return this.m_modified_id;
  endfunction
  
  // Function: get_message
  //
  // Returns the string message of the message that is currently being
  // processed. If the message was modified by a previously executed
  // catcher (which re-threw the message), then the returned 
  // message is the modified value.
  
  function string get_message();
     return this.m_modified_message;
  endfunction
  
  // Function: get_action
  //
  // Returns the <uvm_action> of the message that is currently being
  // processed. If the action was modified by a previously executed
  // catcher (which re-threw the message), then the returned 
  // action is the modified value.
  
  function uvm_action get_action();
    return this.m_modified_action;
  endfunction
  
  // Function: get_fname
  //
  // Returns the file name of the message.
  
  function string get_fname();
    return this.m_file_name;
  endfunction             

  // Function: get_line
  //
  // Returns the line number of the message.

  function int get_line();
    return this.m_line_number;
  endfunction
  
  // Group: Change Message State

  // Function: set_severity
  //
  // Change the severity of the message to ~severity~. Any other
  // report catchers will see the modified value.
  
  protected function void set_severity(uvm_severity severity);
    this.m_modified_severity = severity;
  endfunction
  
  // Function: set_verbosity
  //
  // Change the verbosity of the message to ~verbosity~. Any other
  // report catchers will see the modified value.

  protected function void set_verbosity(int verbosity);
    this.m_modified_verbosity = verbosity;
  endfunction      

  // Function: set_id
  //
  // Change the id of the message to ~id~. Any other
  // report catchers will see the modified value.

  protected function void set_id(string id);
    this.m_modified_id = id;
  endfunction
  
  // Function: set_message
  //
  // Change the text of the message to ~message~. Any other
  // report catchers will see the modified value.

  protected function void set_message(string message);
    this.m_modified_message = message;
  endfunction
  
  // Function: set_action
  //
  // Change the action of the message to ~action~. Any other
  // report catchers will see the modified value.
  
  protected function void set_action(uvm_action action);
    this.m_modified_action = action;
    this.m_set_action_called = 1;
  endfunction
  
  // Group: Debug
     
  // Function: get_report_catcher
  //
  // Returns the first report catcher that has ~name~. 
  
  static function uvm_report_catcher get_report_catcher(string name);
    static uvm_report_cb_iter iter = new(null);
    get_report_catcher = iter.first();
    while(get_report_catcher != null) begin
      if(get_report_catcher.get_name() == name)
        return get_report_catcher;
      get_report_catcher = iter.next();
    end
    return null;
  endfunction


  // Function: print_catcher
  //
  // Prints information about all of the report catchers that are 
  // registered. For finer grained detail, the <uvm_callbacks #(T,CB)::display>
  // method can be used by calling uvm_report_cb::display(<uvm_report_object>).

  static function void print_catcher(UVM_FILE file=0);
    string msg;
    string enabled;
    uvm_report_catcher catcher;
    static uvm_report_cb_iter iter = new(null);

    f_display(file, "-------------UVM REPORT CATCHERS----------------------------");

    catcher = iter.first();
    while(catcher != null) begin
       if(catcher.callback_mode())
        enabled = "ON";        
       else
        enabled = "OFF";        
      
      $swrite(msg, "%20s : %s", catcher.get_name(),
              enabled);
      f_display(file, msg);
      catcher = iter.next();
    end
    f_display(file, "--------------------------------------------------------------");
  endfunction
  
  // Funciton: debug_report_catcher
  //
  // Turn on report catching debug information. ~what~ is a bitwise and of
  // * DO_NOT_CATCH  -- forces catch to be ignored so that all catchers see the
  //   the reports.
  // * DO_NOT_MODIFY -- forces the message to remain unchanged

  static function void debug_report_catcher(int what= 0);
    m_debug_flags = what;
  endfunction        
  
  // Group: Callback Interface
 
  // Function: catch
  //
  // This is the method that is called for each registered report catcher.
  // There are no arguments to this function. The <Current Message State>
  // interface methods can be used to access information about the 
  // current message being processed.

  pure virtual function action_e catch();
     

  // Group: Reporting

   // Function: uvm_report_fatal
   //
   // Issues a fatal message using the current message's report object.
   // This message will bypass any message catching callbacks.
   
   protected function void uvm_report_fatal(string id, string message, int verbosity, string fname = "", int line = 0 );
     string m;
     uvm_action a;
     UVM_FILE f;
     uvm_report_handler rh;
     
     rh   = this.m_client.get_report_handler();
     a    = rh.get_action(UVM_FATAL,id);
     f    = rh.get_file_handle(UVM_FATAL,id);
     
     m    = this.m_server.compose_message(UVM_FATAL,this.m_name, id, message, fname, line);
     this.m_server.process_report(UVM_FATAL, this.m_name, id, message, a, f, fname, line,
                                  m, verbosity, this.m_client);
   endfunction  


   // Function: uvm_report_error
   //
   // Issues a error message using the current message's report object.
   // This message will bypass any message catching callbacks.
   
   
   protected function void uvm_report_error(string id, string message, int verbosity, string fname = "", int line = 0 );
     string m;
     uvm_action a;
     UVM_FILE f;
     uvm_report_handler rh;
     
     rh   = this.m_client.get_report_handler();
     a    = rh.get_action(UVM_ERROR,id);
     f    = rh.get_file_handle(UVM_ERROR,id);
     
     m    = this.m_server.compose_message(UVM_ERROR,this.m_name, id, message, fname, line);
     this.m_server.process_report(UVM_ERROR, this.m_name, id, message, a, f, fname, line,
                                  m, verbosity, this.m_client);
   endfunction  


   // Function: uvm_report_warning
   //
   // Issues a warning message using the current message's report object.
   // This message will bypass any message catching callbacks.
   
   protected function void uvm_report_warning(string id, string message, int verbosity, string fname = "", int line = 0 );
     string m;
     uvm_action a;
     UVM_FILE f;
     uvm_report_handler rh;
     
     rh   = this.m_client.get_report_handler();
     a    = rh.get_action(UVM_WARNING,id);
     f    = rh.get_file_handle(UVM_WARNING,id);
     
     m    = this.m_server.compose_message(UVM_WARNING,this.m_name, id, message, fname, line);
     this.m_server.process_report(UVM_WARNING, this.m_name, id, message, a, f, fname, line,
                                  m, verbosity, this.m_client);
   endfunction  


   // Function: uvm_report_info
   //
   // Issues a info message using the current message's report object.
   // This message will bypass any message catching callbacks.
   
   protected function void uvm_report_info(string id, string message, int verbosity, string fname = "", int line = 0 );
     string m;
     uvm_action a;
     UVM_FILE f;
     uvm_report_handler rh;
     rh    = this.m_client.get_report_handler();
     a    = rh.get_action(UVM_INFO,id);
     f     = rh.get_file_handle(UVM_INFO,id);
     
     m     = this.m_server.compose_message(UVM_INFO,this.m_name, id, message, fname, line);
     this.m_server.process_report(UVM_INFO, this.m_name, id, message, a, f, fname, line,
                                  m, verbosity, this.m_client);
   endfunction // uvm_report_info

    // Function: uvm_report
    //
    // Issues a message using the current message's report object.
    // This message will bypass any message catching callbacks.

    protected function void uvm_report(uvm_severity severity, string id, string message, int verbosity, string fname="", int line = 0);
        string m;
        uvm_action a;
        UVM_FILE f;
        uvm_report_handler rh;
        rh = this.m_client.get_report_handler();
        a = rh.get_action(severity, id);
        f = rh.get_file_handle(severity, id);

        m = this.m_server.compose_message(severity, this.m_name, id, message, fname, line);
        this.m_server.process_report(severity, this.m_name, id, message, a , f, fname, line,
                                     m, verbosity, this.m_client);
    endfunction // uvm_report

  // Function: issue
  // Immediately issues the message which is currently being processed. This
  // is useful if the message is being ~CAUGHT~ but should still be emitted.
  //
  // Issuing a message will update the report_server stats, possibly multiple 
  // times if the message is not ~CAUGHT~.

  protected function void issue();
     string m;
     uvm_action a;
     UVM_FILE f;
     uvm_report_handler rh;
     
     rh = this.m_client.get_report_handler();
     a  =  this.m_modified_action;
     f  = rh.get_file_handle(this.m_modified_severity,this.m_modified_id);
     
     m  = this.m_server.compose_message(this.m_modified_severity, this.m_name,
                                        this.m_modified_id,
                                        this.m_modified_message,
                                        this.m_file_name, this.m_line_number);
     this.m_server.process_report(this.m_modified_severity, this.m_name,
                                  this.m_modified_id, this.m_modified_message,
                                  a, f, this.m_file_name, this.m_line_number,
                                  m, this.m_modified_verbosity,this.m_client);
  endfunction


  //process_all_report_catchers
  //method called by report_server.report to process catchers
  //

  static function int process_all_report_catchers( 
    input uvm_report_server server,
    input uvm_report_object client,
    ref uvm_severity severity, 
    input string name, 
    ref string id,
    ref string message,
    ref int verbosity_level,
    ref uvm_action action,
    input string filename,
    input int line 
  );
    int iter;
    uvm_report_catcher catcher;
    int thrown = 1;
    uvm_severity orig_severity;
    static bit in_catcher;

    if(in_catcher == 1) begin
        return 1;
    end
    in_catcher = 1;    
    uvm_callbacks_base::m_tracing = 0;  //turn off cb tracing so catcher stuff doesn't print

    m_server             = server;
    m_client             = client;
    orig_severity        = severity;
    m_name               = name;
    m_file_name          = filename;
    m_line_number        = line;
    m_modified_id        = id;
    m_modified_severity  = severity;
    m_modified_message   = message;
    m_modified_verbosity = verbosity_level;
    m_modified_action    = action;

    m_orig_severity  = severity;
    m_orig_id        = id;
    m_orig_verbosity = verbosity_level;
    m_orig_action    = action;
    m_orig_message   = message;      

    catcher = uvm_report_cb::get_first(iter,client);
    while(catcher != null) begin
      uvm_severity prev_sev;

      if (!catcher.callback_mode()) begin
        catcher = uvm_report_cb::get_next(iter,client);
        continue;
      end

      prev_sev = m_modified_severity;
      m_set_action_called = 0;
      thrown = catcher.process_report_catcher();

      // Set the action to the default action for the new severity
      // if it is still at the default for the previous severity,
      // unless it was explicitly set.
      if (!m_set_action_called &&
          m_modified_severity != prev_sev &&
          m_modified_action == m_client.get_report_action(prev_sev, "*@&*^*^*#")) begin
         m_modified_action = m_client.get_report_action(m_modified_severity, "*@&*^*^*#");
      end

      if(thrown == 0) begin 
        case(orig_severity)
          UVM_FATAL:   m_caught_fatal++;
          UVM_ERROR:   m_caught_error++;
          UVM_WARNING: m_caught_warning++;
         endcase   
         break;
      end 
      catcher = uvm_report_cb::get_next(iter,client);
    end //while

    //update counters if message was returned with demoted severity
    case(orig_severity)
      UVM_FATAL:    
        if(m_modified_severity < orig_severity)
          m_demoted_fatal++;
      UVM_ERROR:
        if(m_modified_severity < orig_severity)
          m_demoted_error++;
      UVM_WARNING:
        if(m_modified_severity < orig_severity)
          m_demoted_warning++;
    endcase
   
    in_catcher = 0;
    uvm_callbacks_base::m_tracing = 1;  //turn tracing stuff back on

    severity        = m_modified_severity;
    id              = m_modified_id;
    message         = m_modified_message;
    verbosity_level = m_modified_verbosity;
    action          = m_modified_action;

    return thrown; 
  endfunction


  //process_report_catcher
  //internal method to call user catch() method
  //

  local function int process_report_catcher();

    action_e act;

    act = this.catch();

    if(act == UNKNOWN_ACTION)
      this.uvm_report_error("RPTCTHR", {"uvm_report_this.catch() in catcher instance ", this.get_name(), " must return THROW or CAUGHT"}, UVM_NONE, `uvm_file, `uvm_line);

    if(m_debug_flags & DO_NOT_MODIFY) begin
      m_modified_severity    = m_orig_severity;
      m_modified_id          = m_orig_id;
      m_modified_verbosity   = m_orig_verbosity;
      m_modified_action      = m_orig_action;
      m_modified_message     = m_orig_message;
    end     

    if(act == CAUGHT  && !(m_debug_flags & DO_NOT_CATCH)) begin
      return 0;
    end  

    return 1;

  endfunction

  //f_display
  //internal method to check if file is open
  //
  
  local static function void f_display(UVM_FILE file, string str);
    if (file == 0)
      $display("%s", str);
    else
      $fdisplay(file, "%s", str);
  endfunction

  // Function: summarize_report_catcher
  //
  // This function is called automatically by <uvm_report_server::summarize()>.
  // It prints the statistics for the active catchers.

  static function void summarize_report_catcher(UVM_FILE file);
    string s;
    if(do_report) begin
      f_display(file, "");   
      f_display(file, "--- UVM Report catcher Summary ---");
      f_display(file, "");   
      f_display(file, "");
  
      $sformat(s, "Number of demoted UVM_FATAL reports  :%5d", m_demoted_fatal);
      f_display(file,s);
  
      $sformat(s, "Number of demoted UVM_ERROR reports  :%5d", m_demoted_error);
      f_display(file,s);
  
      $sformat(s, "Number of demoted UVM_WARNING reports:%5d", m_demoted_warning);
      f_display(file,s);

      $sformat(s, "Number of caught UVM_FATAL reports   :%5d", m_caught_fatal);
      f_display(file,s);
  
      $sformat(s, "Number of caught UVM_ERROR reports   :%5d", m_caught_error);
      f_display(file,s);
  
      $sformat(s, "Number of caught UVM_WARNING reports :%5d", m_caught_warning);
      f_display(file,s);
    end
  endfunction

endclass

`endif // UVM_REPORT_CATCHER_SVH
