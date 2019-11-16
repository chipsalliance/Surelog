//
//------------------------------------------------------------------------------
//   Copyright 2007-2011 Mentor Graphics Corporation
//   Copyright 2007-2011 Cadence Design Systems, Inc. 
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

`ifndef UVM_REPORT_HANDLER_SVH
`define UVM_REPORT_HANDLER_SVH

typedef class uvm_report_object;
typedef class uvm_report_server;

//------------------------------------------------------------------------------
//
// CLASS: uvm_report_handler
//
// The uvm_report_handler is the class to which most methods in
// <uvm_report_object> delegate. It stores the maximum verbosity, actions,
// and files that affect the way reports are handled. 
//
// The report handler is not intended for direct use. See <uvm_report_object>
// for information on the UVM reporting mechanism.
//
// The relationship between <uvm_report_object> (a base class for uvm_component)
// and uvm_report_handler is typically one to one, but it can be many to one
// if several uvm_report_objects are configured to use the same
// uvm_report_handler_object. See <uvm_report_object::set_report_handler>.
//
// The relationship between uvm_report_handler and <uvm_report_server> is many
// to one. 
//
//------------------------------------------------------------------------------

typedef uvm_pool#(string, uvm_action) uvm_id_actions_array;
typedef uvm_pool#(string, UVM_FILE) uvm_id_file_array;
typedef uvm_pool#(string, int) uvm_id_verbosities_array;
typedef uvm_pool#(uvm_severity, uvm_severity) uvm_sev_override_array;

class uvm_report_handler;

  int m_max_verbosity_level;

  // internal variables

  uvm_action severity_actions[uvm_severity];

  uvm_id_actions_array id_actions;
  uvm_id_actions_array severity_id_actions[uvm_severity];

  // id verbosity settings : default and severity
  uvm_id_verbosities_array id_verbosities;
  uvm_id_verbosities_array severity_id_verbosities[uvm_severity];

  // severity overrides
  uvm_sev_override_array sev_overrides;
  uvm_sev_override_array sev_id_overrides [string];


  // file handles : default, severity, action, (severity,id)
  UVM_FILE default_file_handle;
  UVM_FILE severity_file_handles[uvm_severity];
  uvm_id_file_array id_file_handles=new;
  uvm_id_file_array severity_id_file_handles[uvm_severity];


  // Function: new
  // 
  // Creates and initializes a new uvm_report_handler object.

  function new();
    id_actions=new();
    id_verbosities=new();
    sev_overrides=new();
    initialize;
  endfunction


  // Function- get_server
  //
  // Internal method called by <uvm_report_object::get_report_server>.

  function uvm_report_server get_server();
    return uvm_report_server::get_server();
  endfunction


  // Function- set_max_quit_count
  //
  // Internal method called by <uvm_report_object::set_report_max_quit_count>.

  function void set_max_quit_count(int max_count);
    uvm_report_server srvr;
    srvr = uvm_report_server::get_server();
    srvr.set_max_quit_count(max_count);
  endfunction


  // Function- summarize
  //
  // Internal method called by <uvm_report_object::report_summarize>.

  function void summarize(UVM_FILE file = 0);
    uvm_report_server srvr;
    srvr = uvm_report_server::get_server();
    srvr.summarize(file);
  endfunction


  // Function- report_relnotes_banner
  //
  // Internal method called by <uvm_report_object::report_header>.

  static local bit m_relnotes_done;
  function void report_relnotes_banner(UVM_FILE file = 0);
     uvm_report_server srvr;

     if (m_relnotes_done) return;
     
     srvr = uvm_report_server::get_server();
     
     srvr.f_display(file,
                    "\n  ***********       IMPORTANT RELEASE NOTES         ************");
     
     m_relnotes_done = 1;
  endfunction

   
  // Function- report_header
  //
  // Internal method called by <uvm_report_object::report_header>

  function void report_header(UVM_FILE file = 0);

    uvm_report_server srvr;

    srvr = uvm_report_server::get_server();
    srvr.f_display(file,
      "----------------------------------------------------------------");
    srvr.f_display(file, uvm_revision_string());
    srvr.f_display(file, uvm_mgc_copyright);
    srvr.f_display(file, uvm_cdn_copyright);
    srvr.f_display(file, uvm_snps_copyright);
    srvr.f_display(file, uvm_cy_copyright);
    srvr.f_display(file,
      "----------------------------------------------------------------");

    begin
       uvm_cmdline_processor clp;
       string args[$];
     
       clp = uvm_cmdline_processor::get_inst();

       if (clp.get_arg_matches("+UVM_NO_RELNOTES", args)) return;

`ifndef UVM_NO_DEPRECATED
       report_relnotes_banner(file);
       srvr.f_display(file, "\n  You are using a version of the UVM library that has been compiled");
       srvr.f_display(file, "  with `UVM_NO_DEPRECATED undefined.");
       srvr.f_display(file, "  See http://www.eda.org/svdb/view.php?id=3313 for more details.");
`endif

`ifndef UVM_OBJECT_MUST_HAVE_CONSTRUCTOR
       report_relnotes_banner(file);
       srvr.f_display(file, "\n  You are using a version of the UVM library that has been compiled");
       srvr.f_display(file, "  with `UVM_OBJECT_MUST_HAVE_CONSTRUCTOR undefined.");
       srvr.f_display(file, "  See http://www.eda.org/svdb/view.php?id=3770 for more details.");
`endif

       if (m_relnotes_done)
          srvr.f_display(file, "\n      (Specify +UVM_NO_RELNOTES to turn off this notice)\n");

    end
  endfunction


  // Function- initialize
  // 
  // This method is called by the constructor to initialize the arrays and
  // other variables described above to their default values.

  function void initialize();
    set_default_file(0);
    m_max_verbosity_level = UVM_MEDIUM;
    set_defaults();
  endfunction


  // Function: run_hooks
  //
  // The run_hooks method is called if the <UVM_CALL_HOOK> action is set for a
  // report. It first calls the client's <uvm_report_object::report_hook> method, 
  // followed by the appropriate severity-specific hook method. If either 
  // returns 0, then the report is not processed.

  virtual function bit run_hooks(uvm_report_object client,
                                 uvm_severity severity,
                                 string id,
                                 string message,
                                 int verbosity,
                                 string filename,
                                 int line);

    bit ok;

    ok = client.report_hook(id, message, verbosity, filename, line);

    case(severity)
      UVM_INFO:
       ok &= client.report_info_hook   (id, message, verbosity, filename, line);
      UVM_WARNING:
       ok &= client.report_warning_hook(id, message, verbosity, filename, line);
      UVM_ERROR:
       ok &= client.report_error_hook  (id, message, verbosity, filename, line);
      UVM_FATAL:
       ok &= client.report_fatal_hook  (id, message, verbosity, filename, line);
    endcase

    return ok;

  endfunction

  
  // Function- get_severity_id_file
  //
  // Return the file id based on the severity and the id

  local function UVM_FILE get_severity_id_file(uvm_severity severity, string id);

    uvm_id_file_array array;

    if(severity_id_file_handles.exists(severity)) begin
      array = severity_id_file_handles[severity];      
      if(array.exists(id))
        return array.get(id);
    end


    if(id_file_handles.exists(id))
      return id_file_handles.get(id);

    if(severity_file_handles.exists(severity))
      return severity_file_handles[severity];

    return default_file_handle;

  endfunction


  // Function- set_verbosity_level
  //
  // Internal method called by uvm_report_object.

  function void set_verbosity_level(int verbosity_level);
    m_max_verbosity_level = verbosity_level;
  endfunction


  // Function: get_verbosity_level
  //
  // Returns the verbosity associated with the given ~severity~ and ~id~.
  // 
  // First, if there is a verbosity associated with the ~(severity,id)~ pair,
  // return that.  Else, if there is an verbosity associated with the ~id~, return
  // that.  Else, return the max verbosity setting.

  function int get_verbosity_level(uvm_severity severity=UVM_INFO, string id="" );

    uvm_id_verbosities_array array;
    if(severity_id_verbosities.exists(severity)) begin
      array = severity_id_verbosities[severity];
      if(array.exists(id)) begin
        return array.get(id);
      end
    end

    if(id_verbosities.exists(id)) begin
      return id_verbosities.get(id);
    end

    return m_max_verbosity_level;

  endfunction


  // Function: get_action
  //
  // Returns the action associated with the given ~severity~ and ~id~.
  // 
  // First, if there is an action associated with the ~(severity,id)~ pair,
  // return that.  Else, if there is an action associated with the ~id~, return
  // that.  Else, if there is an action associated with the ~severity~, return
  // that. Else, return the default action associated with the ~severity~.

  function uvm_action get_action(uvm_severity severity, string id);

    uvm_id_actions_array array;
    if(severity_id_actions.exists(severity)) begin
      array = severity_id_actions[severity];
      if(array.exists(id))
        return array.get(id);
    end

    if(id_actions.exists(id))
      return id_actions.get(id);

    return severity_actions[severity];

  endfunction


  // Function: get_file_handle
  //
  // Returns the file descriptor associated with the given ~severity~ and ~id~.
  //
  // First, if there is a file handle associated with the ~(severity,id)~ pair,
  // return that. Else, if there is a file handle associated with the ~id~, return
  // that. Else, if there is an file handle associated with the ~severity~, return
  // that. Else, return the default file handle.

  function UVM_FILE get_file_handle(uvm_severity severity, string id);
    UVM_FILE file;
  
    file = get_severity_id_file(severity, id);
    if (file != 0)
      return file;
  
    if (id_file_handles.exists(id)) begin
      file = id_file_handles.get(id);
      if (file != 0)
        return file;
    end

    if (severity_file_handles.exists(severity)) begin
      file = severity_file_handles[severity];
      if(file != 0)
        return file;
    end

    return default_file_handle;
  endfunction


  // Function: report
  //
  // This is the common handler method used by the four core reporting methods
  // (e.g., uvm_report_error) in <uvm_report_object>.

  virtual function void report(
      uvm_severity severity,
      string name,
      string id,
      string message,
      int verbosity_level=UVM_MEDIUM,
      string filename="",
      int line=0,
      uvm_report_object client=null
      );

    uvm_report_server srvr;
    srvr = uvm_report_server::get_server();

    if (client==null)
      client = uvm_root::get();

    // Check for severity overrides and apply them before calling the server.
    // An id specific override has precedence over a generic severity override.
    if(sev_id_overrides.exists(id)) begin
      if(sev_id_overrides[id].exists(severity)) begin
        severity = sev_id_overrides[id].get(severity);
      end
    end
    else begin
      if(sev_overrides.exists(severity)) begin
         severity = sev_overrides.get(severity);
      end
    end

    srvr.report(severity,name,id,message,verbosity_level,filename,line,client);
    
  endfunction


  // Function: format_action
  //
  // Returns a string representation of the ~action~, e.g., "DISPLAY".

  function string format_action(uvm_action action);
    string s;

    if(uvm_action_type'(action) == UVM_NO_ACTION) begin
      s = "NO ACTION";
    end
    else begin
      s = "";
      if(action & UVM_DISPLAY)   s = {s, "DISPLAY "};
      if(action & UVM_LOG)       s = {s, "LOG "};
      if(action & UVM_COUNT)     s = {s, "COUNT "};
      if(action & UVM_EXIT)      s = {s, "EXIT "};
      if(action & UVM_CALL_HOOK) s = {s, "CALL_HOOK "};
      if(action & UVM_STOP)      s = {s, "STOP "};
    end

    return s;
  endfunction


  // Function- set_default
  //
  // Internal method for initializing report handler.

  function void set_defaults();
    set_severity_action(UVM_INFO,    UVM_DISPLAY);
    set_severity_action(UVM_WARNING, UVM_DISPLAY);
    set_severity_action(UVM_ERROR,   UVM_DISPLAY | UVM_COUNT);
    set_severity_action(UVM_FATAL,   UVM_DISPLAY | UVM_EXIT);

    set_severity_file(UVM_INFO, default_file_handle);
    set_severity_file(UVM_WARNING, default_file_handle);
    set_severity_file(UVM_ERROR,   default_file_handle);
    set_severity_file(UVM_FATAL,   default_file_handle);
  endfunction


  // Function- set_severity_action
  // Function- set_id_action
  // Function- set_severity_id_action
  // Function- set_id_verbosity
  // Function- set_severity_id_verbosity
  //
  // Internal methods called by uvm_report_object.

  function void set_severity_action(input uvm_severity severity,
                                    input uvm_action action);
    severity_actions[severity] = action;
  endfunction

  function void set_id_action(input string id, input uvm_action action);
    id_actions.add(id, action);
  endfunction

  function void set_severity_id_action(uvm_severity severity,
                                       string id,
                                       uvm_action action);
    if(!severity_id_actions.exists(severity))
      severity_id_actions[severity] = new;
    severity_id_actions[severity].add(id,action);
  endfunction
  
  function void set_id_verbosity(input string id, input int verbosity);
    id_verbosities.add(id, verbosity);
  endfunction

  function void set_severity_id_verbosity(uvm_severity severity,
                                       string id,
                                       int verbosity);
    if(!severity_id_verbosities.exists(severity))
      severity_id_verbosities[severity] = new;
    severity_id_verbosities[severity].add(id,verbosity);
  endfunction

  // Function- set_default_file
  // Function- set_severity_file
  // Function- set_id_file
  // Function- set_severity_id_file
  //
  // Internal methods called by uvm_report_object.

  function void set_default_file (UVM_FILE file);
    default_file_handle = file;
  endfunction

  function void set_severity_file (uvm_severity severity, UVM_FILE file);
    severity_file_handles[severity] = file;
  endfunction

  function void set_id_file (string id, UVM_FILE file);
    id_file_handles.add(id, file);
  endfunction

  function void set_severity_id_file(uvm_severity severity,
                                     string id, UVM_FILE file);
    if(!severity_id_file_handles.exists(severity))
      severity_id_file_handles[severity] = new;
    severity_id_file_handles[severity].add(id, file);
  endfunction

  function void set_severity_override(uvm_severity cur_severity,
                                      uvm_severity new_severity);
    sev_overrides.add(cur_severity, new_severity);
  endfunction

  function void set_severity_id_override(uvm_severity cur_severity,
                                         string id,
                                         uvm_severity new_severity);
    // has precedence over set_severity_override
    // silently override previous setting
    uvm_sev_override_array arr;
    if(!sev_id_overrides.exists(id))
      sev_id_overrides[id] = new;
 
    sev_id_overrides[id].add(cur_severity, new_severity);
  endfunction

  
  // Function- dump_state
  //
  // Internal method for debug.

  function void dump_state();

    string s;
    uvm_action a;
    string idx;
    UVM_FILE file;
    uvm_report_server srvr;
 
    uvm_id_actions_array id_a_ary;
    uvm_id_verbosities_array id_v_ary;
    uvm_id_file_array id_f_ary;

    srvr = uvm_report_server::get_server();

    srvr.f_display(0,
      "----------------------------------------------------------------------");
    srvr.f_display(0, "report handler state dump");
    srvr.f_display(0, "");

    // verbosities

    srvr.f_display(0, "");   
    srvr.f_display(0, "+-----------------+");
    srvr.f_display(0, "|   Verbosities   |");
    srvr.f_display(0, "+-----------------+");
    srvr.f_display(0, "");   

    $sformat(s, "max verbosity level = %d", m_max_verbosity_level);
    srvr.f_display(0, s);

    srvr.f_display(0, "*** verbosities by id");

    if(id_verbosities.first(idx))
    do begin
      uvm_verbosity v = uvm_verbosity'(id_verbosities.get(idx));
      $sformat(s, "[%s] --> %s", idx, v.name());
      srvr.f_display(0, s);
    end while(id_verbosities.next(idx));

    // verbosities by id

    srvr.f_display(0, "");
    srvr.f_display(0, "*** verbosities by id and severity");

    foreach( severity_id_verbosities[severity] ) begin
      uvm_severity_type sev = uvm_severity_type'(severity);
      id_v_ary = severity_id_verbosities[severity];
      if(id_v_ary.first(idx))
      do begin
        uvm_verbosity v = uvm_verbosity'(id_v_ary.get(idx));
        $sformat(s, "%s:%s --> %s",
           sev.name(), idx, v.name());
        srvr.f_display(0, s);        
      end while(id_v_ary.next(idx));
    end

    // actions

    srvr.f_display(0, "");   
    srvr.f_display(0, "+-------------+");
    srvr.f_display(0, "|   actions   |");
    srvr.f_display(0, "+-------------+");
    srvr.f_display(0, "");   

    srvr.f_display(0, "*** actions by severity");
    foreach( severity_actions[severity] ) begin
      uvm_severity_type sev = uvm_severity_type'(severity);
      $sformat(s, "%s = %s",
       sev.name(), format_action(severity_actions[severity]));
      srvr.f_display(0, s);
    end

    srvr.f_display(0, "");
    srvr.f_display(0, "*** actions by id");

    if(id_actions.first(idx))
    do begin
      $sformat(s, "[%s] --> %s", idx, format_action(id_actions.get(idx)));
      srvr.f_display(0, s);
    end while(id_actions.next(idx));

    // actions by id

    srvr.f_display(0, "");
    srvr.f_display(0, "*** actions by id and severity");

    foreach( severity_id_actions[severity] ) begin
      uvm_severity_type sev = uvm_severity_type'(severity);
      id_a_ary = severity_id_actions[severity];
      if(id_a_ary.first(idx))
      do begin
        $sformat(s, "%s:%s --> %s",
           sev.name(), idx, format_action(id_a_ary.get(idx)));
        srvr.f_display(0, s);        
      end while(id_a_ary.next(idx));
    end

    // Files

    srvr.f_display(0, "");
    srvr.f_display(0, "+-------------+");
    srvr.f_display(0, "|    files    |");
    srvr.f_display(0, "+-------------+");
    srvr.f_display(0, "");   

    $sformat(s, "default file handle = %d", default_file_handle);
    srvr.f_display(0, s);

    srvr.f_display(0, "");
    srvr.f_display(0, "*** files by severity");
    foreach( severity_file_handles[severity] ) begin
      uvm_severity_type sev = uvm_severity_type'(severity);
      file = severity_file_handles[severity];
      $sformat(s, "%s = %d", sev.name(), file);
      srvr.f_display(0, s);
    end

    srvr.f_display(0, "");
    srvr.f_display(0, "*** files by id");

    if(id_file_handles.first(idx))
    do begin
      file = id_file_handles.get(idx);
      $sformat(s, "id %s --> %d", idx, file);
      srvr.f_display(0, s);
    end while (id_file_handles.next(idx));

    srvr.f_display(0, "");
    srvr.f_display(0, "*** files by id and severity");

    foreach( severity_id_file_handles[severity] ) begin
      uvm_severity_type sev = uvm_severity_type'(severity);
      id_f_ary = severity_id_file_handles[severity];
      if(id_f_ary.first(idx))
      do begin
        $sformat(s, "%s:%s --> %d", sev.name(), idx, id_f_ary.get(idx));
        srvr.f_display(0, s);
      end while(id_f_ary.next(idx));
    end

    srvr.dump_server_state();
    
    srvr.f_display(0,
      "----------------------------------------------------------------------");
  endfunction

endclass : uvm_report_handler

`endif // UVM_REPORT_HANDLER_SVH

