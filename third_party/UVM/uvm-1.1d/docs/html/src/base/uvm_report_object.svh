//
//------------------------------------------------------------------------------
//   Copyright 2007-2010 Mentor Graphics Corporation
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

`ifndef UVM_REPORT_CLIENT_SVH
`define UVM_REPORT_CLIENT_SVH

typedef class uvm_component;
typedef class uvm_env;
typedef class uvm_root;

//------------------------------------------------------------------------------
//
// CLASS: uvm_report_object
//
//------------------------------------------------------------------------------
//
// The uvm_report_object provides an interface to the UVM reporting facility.
// Through this interface, components issue the various messages that occur
// during simulation. Users can configure what actions are taken and what
// file(s) are output for individual messages from a particular component
// or for all messages from all components in the environment. Defaults are
// applied where there is no explicit configuration.
//
// Most methods in uvm_report_object are delegated to an internal instance of an
// <uvm_report_handler>, which stores the reporting configuration and determines
// whether an issued message should be displayed based on that configuration.
// Then, to display a message, the report handler delegates the actual
// formatting and production of messages to a central <uvm_report_server>.
//
// A report consists of an id string, severity, verbosity level, and the textual
// message itself. They may optionally include the filename and line number from
// which the message came. If the verbosity level of a report is greater than the
// configured maximum verbosity level of its report object, it is ignored.
// If a report passes the verbosity filter in effect, the report's action is
// determined. If the action includes output to a file, the configured file
// descriptor(s) are determined. 
//
// Actions - can be set for (in increasing priority) severity, id, and
// (severity,id) pair. They include output to the screen <UVM_DISPLAY>,
// whether the message counters should be incremented <UVM_COUNT>, and
// whether a $finish should occur <UVM_EXIT>.
//
// Default Actions - The following provides the default actions assigned to
// each severity. These can be overridden by any of the set_*_action methods. 
//|    UVM_INFO -       UVM_DISPLAY
//|    UVM_WARNING -    UVM_DISPLAY
//|    UVM_ERROR -      UVM_DISPLAY | UVM_COUNT
//|    UVM_FATAL -      UVM_DISPLAY | UVM_EXIT
//
// File descriptors - These can be set by (in increasing priority) default,
// severity level, an id, or (severity,id) pair.  File descriptors are
// standard verilog file descriptors; they may refer to more than one file.
// It is the user's responsibility to open and close them.
//
// Default file handle - The default file handle is 0, which means that reports
// are not sent to a file even if an UVM_LOG attribute is set in the action
// associated with the report. This can be overridden by any of the set_*_file
// methods.
//
//------------------------------------------------------------------------------

class uvm_report_object extends uvm_object;

  uvm_report_handler m_rh;

  // Function: new
  //
  // Creates a new report object with the given name. This method also creates
  // a new <uvm_report_handler> object to which most tasks are delegated.

  function new(string name = "");
    super.new(name);
    m_rh = new();
  endfunction


  //----------------------------------------------------------------------------
  // Group: Reporting
  //----------------------------------------------------------------------------

  // Function: uvm_report

  virtual function void uvm_report( uvm_severity severity,
                                    string id,
                                    string message,
                                    int verbosity = (severity == uvm_severity'(UVM_ERROR)) ? UVM_LOW :
                                                    (severity == uvm_severity'(UVM_FATAL)) ? UVM_NONE : UVM_MEDIUM,
                                    string filename = "",
                                    int line = 0);
    m_rh.report(severity, get_full_name(), id, message, verbosity,
                filename, line, this);
  endfunction 

      

  // Function: uvm_report_info

  virtual function void uvm_report_info( string id,
                                         string message,
                                         int verbosity = UVM_MEDIUM,
                                         string filename = "",
                                         int line = 0);
    m_rh.report(UVM_INFO, get_full_name(), id, message, verbosity,
                filename, line, this);
  endfunction

  // Function: uvm_report_warning

  virtual function void uvm_report_warning( string id,
                                            string message,
                                            int verbosity = UVM_MEDIUM,
                                            string filename = "",
                                            int line = 0);
    m_rh.report(UVM_WARNING, get_full_name(), id, message, verbosity, 
               filename, line, this);
  endfunction

  // Function: uvm_report_error

  virtual function void uvm_report_error( string id,
                                          string message,
                                          int verbosity = UVM_LOW,
                                          string filename = "",
                                          int line = 0);
    m_rh.report(UVM_ERROR, get_full_name(), id, message, verbosity, 
               filename, line, this);
  endfunction

  // Function: uvm_report_fatal
  //
  // These are the primary reporting methods in the UVM. Using these instead
  // of ~$display~ and other ad hoc approaches ensures consistent output and
  // central control over where output is directed and any actions that
  // result. All reporting methods have the same arguments, although each has
  // a different default verbosity:
  //
  //   id        - a unique id for the report or report group that can be used
  //               for identification and therefore targeted filtering. You can
  //               configure an individual report's actions and output file(s)
  //               using this id string.
  //
  //   message   - the message body, preformatted if necessary to a single
  //               string.
  //
  //   verbosity - the verbosity of the message, indicating its relative
  //               importance. If this number is less than or equal to the
  //               effective verbosity level, see <set_report_verbosity_level>,
  //               then the report is issued, subject to the configured action
  //               and file descriptor settings.  Verbosity is ignored for 
  //               warnings, errors, and fatals. However, if a warning, error
  //               or fatal is demoted to an info message using the
  //               <uvm_report_catcher>, then the verbosity is taken into
  //               account.
  //
  //   filename/line - (Optional) The location from which the report was issued.
  //               Use the predefined macros, `__FILE__ and `__LINE__.
  //               If specified, it is displayed in the output.

  virtual function void uvm_report_fatal( string id,
                                          string message,
                                          int verbosity = UVM_NONE,
                                          string filename = "",
                                          int line = 0);
    m_rh.report(UVM_FATAL, get_full_name(), id, message, verbosity, 
               filename, line, this);
  endfunction


  //----------------------------------------------------------------------------
  // Group: Callbacks
  //----------------------------------------------------------------------------

  // Function: report_info_hook
  //
  //

  virtual function bit report_info_hook(
           string id, string message, int verbosity, string filename, int line);
    return 1;
  endfunction


  // Function: report_error_hook
  //
  //

  virtual function bit report_error_hook(
           string id, string message, int verbosity, string filename, int line);
    return 1;
  endfunction


  // Function: report_warning_hook
  //
  //

  virtual function bit report_warning_hook(
           string id, string message, int verbosity, string filename, int line);
    return 1;
  endfunction


  // Function: report_fatal_hook
  //
  //

  virtual function bit report_fatal_hook(
           string id, string message, int verbosity, string filename, int line);
    return 1;
  endfunction


  // Function: report_hook
  // 
  // These hook methods can be defined in derived classes to perform additional
  // actions when reports are issued. They are called only if the <UVM_CALL_HOOK>
  // bit is specified in the action associated with the report. The default
  // implementations return 1, which allows the report to be processed. If an
  // override returns 0, then the report is not processed.
  //
  // First, the report_hook method is called, followed by the severity 
  // severity specific hook (report_info_hook, etc.). If either hook method
  // returns 0 then the report is not processed further.

  virtual function bit report_hook(
           string id, string message, int verbosity, string filename, int line);
    return 1;
  endfunction


  // Function: report_header
  //
  // Prints version and copyright information. This information is sent to the
  // command line if ~file~ is 0, or to the file descriptor ~file~ if it is not 0. 
  // The <uvm_root::run_test> task calls this method just before it component
  // phasing begins.

  virtual function void report_header(UVM_FILE file = 0);
    m_rh.report_header(file);
  endfunction


  // Function: report_summarize
  //
  // Outputs statistical information on the reports issued by the central report
  // server. This information will be sent to the command line if ~file~ is 0, or
  // to the file descriptor ~file~ if it is not 0.
  //
  // The run_test method in uvm_top calls this method.

  virtual function void report_summarize(UVM_FILE file = 0);
    m_rh.summarize(file);
  endfunction


  // Function: die
  //
  // This method is called by the report server if a report reaches the maximum
  // quit count or has an UVM_EXIT action associated with it, e.g., as with
  // fatal errors.
  //
  // Calls the <uvm_component::pre_abort()> method
  // on the entire <uvm_component> hierarchy in a bottom-up fashion.
  // It then call calls <report_summarize> and terminates the simulation
  // with ~$finish~.

  virtual function void die();
    // make the pre_abort callbacks
    uvm_root top = uvm_root::get();
    top.m_do_pre_abort();

    report_summarize();
    $finish;
  endfunction

  //----------------------------------------------------------------------------
  // Group: Configuration
  //----------------------------------------------------------------------------

  // Function: set_report_verbosity_level
  //
  // This method sets the maximum verbosity level for reports for this component.
  // Any report from this component whose verbosity exceeds this maximum will
  // be ignored.

  function void set_report_verbosity_level (int verbosity_level);
    m_rh.set_verbosity_level(verbosity_level);
  endfunction

  // Function: set_report_id_verbosity
  //
  function void set_report_id_verbosity (string id, int verbosity);
    m_rh.set_id_verbosity(id, verbosity);
  endfunction

  // Function: set_report_severity_id_verbosity
  //
  // These methods associate the specified verbosity with reports of the
  // given ~severity~, ~id~, or ~severity-id~ pair. An verbosity associated with a
  // particular ~severity-id~ pair takes precedence over an verbosity associated with
  // ~id~, which take precedence over an an verbosity associated with a ~severity~.
  //
  // The ~verbosity~ argument can be any integer, but is most commonaly a
  // predefined <uvm_verbosity> value, <UVM_NONE>, <UVM_LOW>, <UVM_MEDIUM>,
  // <UVM_HIGH>, <UVM_FULL>.

  function void set_report_severity_id_verbosity (uvm_severity severity,
                                               string id, int verbosity);
    m_rh.set_severity_id_verbosity(severity, id, verbosity);
  endfunction


  // Function: set_report_severity_action
  //
  function void set_report_severity_action (uvm_severity severity,
                                            uvm_action action);
    m_rh.set_severity_action(severity, action);
  endfunction

  // Function: set_report_id_action
  //
  function void set_report_id_action (string id, uvm_action action);
    m_rh.set_id_action(id, action);
  endfunction

  // Function: set_report_severity_id_action
  //
  // These methods associate the specified action or actions with reports of the
  // given ~severity~, ~id~, or ~severity-id~ pair. An action associated with a
  // particular ~severity-id~ pair takes precedence over an action associated with
  // ~id~, which takes precedence over an an action associated with a ~severity~.
  //
  // The ~action~ argument can take the value <UVM_NO_ACTION>, or it can be a
  // bitwise OR of any combination of <UVM_DISPLAY>, <UVM_LOG>, <UVM_COUNT>,
  // <UVM_STOP>, <UVM_EXIT>, and <UVM_CALL_HOOK>.

  function void set_report_severity_id_action (uvm_severity severity,
                                               string id, uvm_action action);
    m_rh.set_severity_id_action(severity, id, action);
  endfunction

  // Function: set_report_severity_override
  //
  function void set_report_severity_override(uvm_severity cur_severity,
                                             uvm_severity new_severity);
    m_rh.set_severity_override(cur_severity, new_severity);
  endfunction

  // Function: set_report_severity_id_override
  //
  // These methods provide the ability to upgrade or downgrade a message in
  // terms of severity given ~severity~ and ~id~.  An upgrade or downgrade for
  // a specific ~id~ takes precedence over an upgrade or downgrade associated 
  // with a ~severity~.
  function void set_report_severity_id_override(uvm_severity cur_severity,
                                                string id, 
                                                uvm_severity new_severity);
    m_rh.set_severity_id_override(cur_severity, id, new_severity);
  endfunction


  // Function: set_report_default_file
  //
  function void set_report_default_file ( UVM_FILE file);
    m_rh.set_default_file(file);
  endfunction

  // Function: set_report_severity_file
  //
  function void set_report_severity_file (uvm_severity severity, UVM_FILE file);
    m_rh.set_severity_file(severity, file);
  endfunction

  // Function: set_report_id_file
  //
  function void set_report_id_file (string id, UVM_FILE file);
    m_rh.set_id_file(id, file);
  endfunction

  // Function: set_report_severity_id_file
  //
  // These methods configure the report handler to direct some or all of its
  // output to the given file descriptor. The ~file~ argument must be a
  // multi-channel descriptor (mcd) or file id compatible with $fdisplay.
  //
  // A FILE descriptor can be associated with with reports of
  // the given ~severity~, ~id~, or ~severity-id~ pair.  A FILE associated with
  // a particular ~severity-id~ pair takes precedence over a FILE associated
  // with ~id~, which take precedence over an a FILE associated with a 
  // ~severity~, which takes precedence over the default FILE descriptor.
  //
  // When a report is issued and its associated action has the UVM_LOG bit
  // set, the report will be sent to its associated FILE descriptor.
  // The user is responsible for opening and closing these files.

  function void set_report_severity_id_file (uvm_severity severity, string id,
                                             UVM_FILE file);
    m_rh.set_severity_id_file(severity, id, file);
  endfunction


  // Function: get_report_verbosity_level
  //
  // Gets the verbosity level in effect for this object. Reports issued
  // with verbosity greater than this will be filtered out. The severity
  // and tag arguments check if the verbosity level has been modified for
  // specific severity/tag combinations.

  function int get_report_verbosity_level(uvm_severity severity=UVM_INFO, string id="");
    return m_rh.get_verbosity_level(severity, id);
  endfunction


  // Function: get_report_action
  //
  // Gets the action associated with reports having the given ~severity~
  // and ~id~.

  function int get_report_action(uvm_severity severity, string id);
    return m_rh.get_action(severity,id);
  endfunction


  // Function: get_report_file_handle
  //
  // Gets the file descriptor associated with reports having the given
  // ~severity~ and ~id~.

  function int get_report_file_handle(uvm_severity severity, string id);
    return m_rh.get_file_handle(severity,id);
  endfunction


  // Function: uvm_report_enabled
  //
  // Returns 1 if the configured verbosity for this severity/id is greater than 
  // ~verbosity~ and the action associated with the given ~severity~ and ~id~
  // is not UVM_NO_ACTION, else returns 0.
  // 
  // See also <get_report_verbosity_level> and <get_report_action>, and the
  // global version of <uvm_report_enabled>.

  function int uvm_report_enabled(int verbosity, 
                          uvm_severity severity=UVM_INFO, string id="");
    if (get_report_verbosity_level(severity, id) < verbosity ||
        get_report_action(severity,id) == uvm_action'(UVM_NO_ACTION)) 
      return 0;
    else 
      return 1;
  endfunction


  // Function: set_report_max_quit_count
  //
  // Sets the maximum quit count in the report handler to ~max_count~. When the
  // number of UVM_COUNT actions reaches ~max_count~, the <die> method is called. 
  //
  // The default value of 0 indicates that there is no upper limit to the number
  // of UVM_COUNT reports.

  function void set_report_max_quit_count(int max_count);
    m_rh.set_max_quit_count(max_count);
  endfunction


  //----------------------------------------------------------------------------
  // Group: Setup
  //----------------------------------------------------------------------------

  // Function: set_report_handler
  //
  // Sets the report handler, overwriting the default instance. This allows
  // more than one component to share the same report handler.

  function void set_report_handler(uvm_report_handler handler);
    m_rh = handler;
  endfunction


  // Function: get_report_handler
  //
  // Returns the underlying report handler to which most reporting tasks
  // are delegated.

  function uvm_report_handler get_report_handler();
    return m_rh;
  endfunction


  // Function: reset_report_handler
  //
  // Resets the underlying report handler to its default settings. This clears
  // any settings made with the set_report_* methods (see below).

  function void reset_report_handler;
    m_rh.initialize;
  endfunction


  // Function: get_report_server
  //
  // Returns the <uvm_report_server> instance associated with this report object.

  function uvm_report_server get_report_server();
    return m_rh.get_server();
  endfunction


  // Function: dump_report_state
  //
  // This method dumps the internal state of the report handler. This includes
  // information about the maximum quit count, the maximum verbosity, and the
  // action and files associated with severities, ids, and (severity, id) pairs.

  function void dump_report_state();
    m_rh.dump_state();
  endfunction


  function int uvm_get_max_verbosity();
    return m_rh.m_max_verbosity_level;
  endfunction


  //----------------------------------------------------------------------------
  //                     PRIVATE or PSUEDO-PRIVATE members
  //                      *** Do not call directly ***
  //         Implementation and even existence are subject to change. 
  //----------------------------------------------------------------------------

  protected virtual function uvm_report_object m_get_report_object();
    return this;
  endfunction

endclass

`endif // UVM_REPORT_CLIENT_SVH
