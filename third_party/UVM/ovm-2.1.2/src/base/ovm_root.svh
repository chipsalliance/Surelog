//
//------------------------------------------------------------------------------
//   Copyright 2007-2011 Mentor Graphics Corporation
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

`ifndef OVM_ROOT_SVH
`define OVM_ROOT_SVH

`define OVM_DEFAULT_TIMEOUT 9200s

//------------------------------------------------------------------------------
//
// CLASS: ovm_root
//
// The ~ovm_root~ class serves as the implicit top-level and phase controller for
// all OVM components. Users do not directly instantiate ~ovm_root~. The OVM 
// automatically creates a single instance of <ovm_root> that users can
// access via the global (ovm_pkg-scope) variable, ~ovm_top~. 
// 
// (see ovm_ref_root.gif)
// 
// The ~ovm_top~ instance of ~ovm_root~ plays several key roles in the OVM.
// 
// Implicit top-level - The ~ovm_top~ serves as an implicit top-level component.
// Any component whose parent is specified as NULL becomes a child of ~ovm_top~. 
// Thus, all OVM components in simulation are descendants of ~ovm_top~.
//
// Phase control - ~ovm_top~ manages the phasing for all components.
// There are eight phases predefined in every component: build, connect,
// end_of_elaboration, start_of_simulation, run, extract, check, and
// report. Of these, only the run phase is a task. All others are
// functions. OVM's flexible phasing mechanism allows users to insert
// any number of custom function and task-based phases.
// See <run_test>, <insert_phase>, and <stop_request>, and others.
//
// Search - Use ~ovm_top~ to search for components based on their
// hierarchical name. See <find> and <find_all>.
//
// Report configuration - Use ~ovm_top~ to globally configure
// report verbosity, log files, and actions. For example,
// ~ovm_top.set_report_verbosity_level_hier(OVM_FULL)~ would set
// full verbosity for all components in simulation.
//
// Global reporter - Because ~ovm_top~ is globally accessible (in ovm_pkg
// scope), OVM's reporting mechanism is accessible from anywhere
// outside ~ovm_component~, such as in modules and sequences.
// See <ovm_report_error>, <ovm_report_warning>, and other global
// methods.
//
//------------------------------------------------------------------------------

class ovm_root extends ovm_component;

  extern static function ovm_root get();

  // Task: run_test
  //
  // Phases all components through all registered phases. If the optional
  // test_name argument is provided, or if a command-line plusarg,
  // +OVM_TESTNAME=TEST_NAME, is found, then the specified component is created
  // just prior to phasing. The test may contain new verification components or
  // the entire testbench, in which case the test and testbench can be chosen from
  // the command line without forcing recompilation. If the global (package)
  // variable, finish_on_completion, is set, then $finish is called after
  // phasing completes.

  extern virtual task run_test (string test_name="");


  // Function- run_global_phase
  //
  // Note: all phasing should be started via run_test. This method is used to
  // run through (~upto~=0) or up to (~upto~=1) the given ~phase~. If null, then
  // all remaining phases will be run, effectively completing simulation.

  extern task run_global_phase (ovm_phase phase=null, bit upto=0);


  // Function- run_global_func_phase
  //
  // Note: all phasing should be started via run_test. This method is used to
  // run through (~upto~=0) or up to (~upto~=1) the given ~phase~. If null, then
  // all remaining phases will be run, effectively completing simulation.

  extern function void run_global_func_phase (ovm_phase phase=null, bit upto=0);


  // Function: stop_request
  //
  // Calling this function triggers the process of shutting down the currently
  // running task-based phase. This process involves calling all components'
  // stop tasks for those components whose enable_stop_interrupt bit is set.
  // Once all stop tasks return, or once the optional global_stop_timeout
  // expires, all components' kill method is called, effectively ending the
  // current phase. The ovm_top will then begin execution of the next phase,
  // if any.

  extern function void stop_request();

  
  // Function: in_stop_request
  //
  // This function returns 1 if a stop request is currently active, and 0
  // otherwise.

  extern function bit in_stop_request();


  // Function: insert_phase
  //
  // Inserts a new phase given by new_phase _after_ the existing phase given by
  // exist_phase. The ovm_top maintains a queue of phases executed in
  // consecutive order. If exist_phase is null, then new_phase is inserted at
  // the head of the queue, i.e., it becomes the first phase.

  extern function void  insert_phase (ovm_phase new_phase,
                                      ovm_phase exist_phase);


  // Function: find

  extern function ovm_component find (string comp_match);

  // Function: find_all
  //
  // Returns the component handle (find) or list of components handles
  // (find_all) matching a given string. The string may contain the wildcards,
  // * and ?. Strings beginning with '.' are absolute path names. If optional
  // comp arg is provided, then search begins from that component down
  // (default=all components).

  extern function void find_all (string comp_match,
                                 ref ovm_component comps[$],
                                 input ovm_component comp=null);

  // Function: get_current_phase
  //
  // Returns the handle of the currently executing phase.

  extern function ovm_phase get_current_phase ();


  // Function: get_phase_by_name
  //
  // Returns the handle of the phase having the given ~name~.

  extern function ovm_phase get_phase_by_name (string name);


  virtual function string get_type_name(); return "ovm_root"; endfunction


  // Variable: phase_timeout

  time phase_timeout = `OVM_DEFAULT_TIMEOUT;


  // Variable: stop_timeout
  //
  // These set watchdog timers for task-based phases and stop tasks.
  // The timeout is specified in absolute time.
  // The default timeout is set by the OVM_DEFAULT_TIMEOUT define.
  // A timeout at this value usually indicates a problem with your
  // testbench, or failure to call <global_stop_request>.
  // When set to 0, the timeout is disabled.

  time stop_timeout = `OVM_DEFAULT_TIMEOUT;


  // Variable: enable_print_topology
  //
  // If set, then the entire testbench topology is printed just after completion
  // of the end_of_elaboration phase.

  bit  enable_print_topology = 0;


  // Variable: finish_on_completion
  //
  // If set, then run_test will call $finish after all phases are executed. 


  bit  finish_on_completion = 1;


  // PRIVATE members

  extern `_protected function new ();
  extern function void check_verbosity();
  extern local function void m_do_phase (ovm_component comp, ovm_phase phase);
  extern local task m_stop_process ();
  extern local task m_stop_request (time timeout=0);
  extern local task m_do_stop_all  (ovm_component comp);
  extern local function void m_reset_phase(ovm_component comp,
                                           ovm_phase phase=null);
  extern local function ovm_phase m_get_phase_master(ovm_phase phase, bit set=0);

  local  ovm_phase  m_phase_master[ovm_phase];
  local  ovm_phase  m_phase_q[ovm_phase];
  local  ovm_phase  m_first_phase = null;
  local  ovm_phase  m_last_phase = null;
  local  event      m_stop_request_e;


  ovm_phase m_curr_phase = null;
  static local ovm_root m_inst;

  // For communicating all objections dropped.
  bit m_objections_outstanding = 0;
  bit m_in_stop_request = 0;
  bit m_executing_stop_processes = 0;

  extern virtual task all_dropped (ovm_objection objection, 
           ovm_object source_obj, int count);
  extern virtual function void raised (ovm_objection objection, 
           ovm_object source_obj, int count);

  /*** DEPRECATED - Do not use in new code.  Convert code when appropriate ***/
  extern function void print_unit_list (ovm_component comp=null);
  extern function void print_unit      (string name, ovm_printer printer=null);
  extern function void print_units     (ovm_printer printer=null);
  extern function void print_topology  (ovm_printer printer=null);

endclass


// Class- ovm_root_report_handler
//

class ovm_root_report_handler extends ovm_report_handler;

  virtual function void report(
      ovm_severity severity,
      string name,
      string id,
      string message,
      int verbosity_level,
      string filename,
      int line,
      ovm_report_object client
      );

    if(name == "")
      name = "reporter";

    super.report(severity, name, id, message, verbosity_level, filename, line, client);

  endfunction 

endclass

//------------------------------------------------------------------------------
// 
// Class - ovm_*_phase (predefined phases)
//
//------------------------------------------------------------------------------

`ovm_phase_func_decl(build,1)
`ovm_phase_func_decl(connect,0)
`ovm_phase_func_decl(end_of_elaboration,0)
`ovm_phase_func_decl(start_of_simulation,0)
`ovm_phase_task_decl(run,0)
`ovm_phase_func_decl(extract,0)
`ovm_phase_func_decl(check,0)
`ovm_phase_func_decl(report,0)

build_phase               #(ovm_component) build_ph;
connect_phase             #(ovm_component) connect_ph;
end_of_elaboration_phase  #(ovm_component) end_of_elaboration_ph;
start_of_simulation_phase #(ovm_component) start_of_simulation_ph;
run_phase                 #(ovm_component) run_ph;
extract_phase             #(ovm_component) extract_ph;
check_phase               #(ovm_component) check_ph;
report_phase              #(ovm_component) report_ph;

// DEPRECATED PHASES - DO NOT USE IN NEW CODE

`ovm_phase_func_decl(post_new,0)
`ovm_phase_func_decl(export_connections,0)
`ovm_phase_func_decl(import_connections,1)
`ovm_phase_func_decl(pre_run,0)
`ovm_phase_func_decl(configure,0)
post_new_phase            #(ovm_component) post_new_ph;
export_connections_phase  #(ovm_component) export_connections_ph;
import_connections_phase  #(ovm_component) import_connections_ph;
pre_run_phase             #(ovm_component) pre_run_ph;
configure_phase           #(ovm_component) configure_ph;


//-----------------------------------------------------------------------------
//
// IMPLEMENTATION
//
//-----------------------------------------------------------------------------

// get
// ---

function ovm_root ovm_root::get();
  if (m_inst == null)
    m_inst = new();
  return m_inst;
endfunction


// new
// ---

function ovm_root::new();

  ovm_root_report_handler rh;

  super.new("__top__", null);

  rh = new;
  set_report_handler(rh);

  check_verbosity();

  report_header();
  print_enabled=0;
  build_ph = new;
  post_new_ph = new;
  export_connections_ph = new;
  connect_ph = new;
  import_connections_ph = new;
  configure_ph = new;
  end_of_elaboration_ph = new;
  start_of_simulation_ph = new;
  pre_run_ph = new;
  run_ph = new;
  extract_ph = new;
  check_ph = new;
  report_ph = new;
  insert_phase(build_ph,              null);
  insert_phase(post_new_ph,           build_ph);
  insert_phase(export_connections_ph, post_new_ph);
  insert_phase(connect_ph,            export_connections_ph);
  insert_phase(import_connections_ph, connect_ph);
  insert_phase(configure_ph,          import_connections_ph);
  insert_phase(end_of_elaboration_ph, configure_ph);
  insert_phase(start_of_simulation_ph,end_of_elaboration_ph);
  insert_phase(pre_run_ph,            start_of_simulation_ph);
  insert_phase(run_ph,                pre_run_ph);
  insert_phase(extract_ph,            run_ph);
  insert_phase(check_ph,              extract_ph);
  insert_phase(report_ph,             check_ph);
endfunction


// check_verbosity
// ---------------

function void ovm_root::check_verbosity();

  string s;
  int plusarg;
  string msg;
  int verbosity= OVM_MEDIUM;

  case(1)
    $value$plusargs("OVM_VERBOSITY=%s", s) > 0 : plusarg = 1;
    $value$plusargs("ovm_verbosity=%s", s) > 0 : plusarg = 1;
    $value$plusargs("VERBOSITY=%s", s)     > 0 : plusarg = 1;
    $value$plusargs("verbosity=%s", s)     > 0 : plusarg = 1;
    default                                    : plusarg = 0;
  endcase

  if(plusarg == 1) begin
    case(s.toupper())
      "OVM_NONE"    : verbosity = OVM_NONE;
      "NONE"        : verbosity = OVM_NONE;
      "OVM_LOW"     : verbosity = OVM_LOW;
      "LOW"         : verbosity = OVM_LOW;
      "LO"          : verbosity = OVM_LOW;
      "OVM_MEDIUM"  : verbosity = OVM_MEDIUM;
      "OVM_MED"     : verbosity = OVM_MEDIUM;
      "MEDIUM"      : verbosity = OVM_MEDIUM;
      "MED"         : verbosity = OVM_MEDIUM;
      "OVM_HIGH"    : verbosity = OVM_HIGH;
      "OVM_HI"      : verbosity = OVM_HIGH;
      "HIGH"        : verbosity = OVM_HIGH;
      "HI"          : verbosity = OVM_HIGH;
      "OVM_FULL"    : verbosity = OVM_FULL;
      "FULL"        : verbosity = OVM_FULL;
      "OVM_DEBUG"   : verbosity = OVM_DEBUG;
      "DEBUG"       : verbosity = OVM_DEBUG;
      default       : begin
                        verbosity = s.atoi();
                        if(verbosity == 0) begin
                          verbosity = OVM_MEDIUM;
                          $sformat(msg, "illegal verbosity value, using default of %0d",
                                   OVM_MEDIUM);
                         ovm_report_warning("verbosity", msg, OVM_NONE);
                      end
                end
    endcase
  end

  set_report_verbosity_level_hier(verbosity);

endfunction


//------------------------------------------------------------------------------

// Variable: ovm_top
//
// This is the top-level that governs phase execution and provides component
// search interface. See <ovm_root> for more information.

`const ovm_root ovm_top = ovm_root::get();

// for backward compatibility
`const ovm_root _global_reporter = ovm_root::get();


//------------------------------------------------------------------------------



/* deprecated */ ovm_component ovm_test_top;
/* deprecated */ bit ovm_enable_print_topology = 0;


//------------------------------------------------------------------------------
//
// Primary Simulation Entry Points
//
//------------------------------------------------------------------------------

// run_test
// --------

task ovm_root::run_test(string test_name="");

  ovm_factory factory = ovm_factory::get();
  bit testname_plusarg;
  string msg;

  testname_plusarg = 0;

  // plusarg overrides argument
  if ($value$plusargs("OVM_TESTNAME=%s", test_name))
    testname_plusarg = 1;

  if ($value$plusargs("TESTNAME=%s", test_name)) begin
    ovm_report_warning("DPRFT",
          "+TESTNAME is deprecated. Use +OVM_TESTNAME instead.", OVM_NONE);
    testname_plusarg = 1;
  end

  // if test now defined, create it using common factory
  if (test_name != "") begin
    if(m_children.exists("ovm_test_top")) begin
      ovm_report_fatal("TTINST",
          "An ovm_test_top already exists via a previous call to run_test", OVM_NONE);
      #0; // forces shutdown because $finish is forked
    end
    $cast(ovm_test_top, factory.create_component_by_name(test_name,
          "ovm_test_top", "ovm_test_top", null));

    if (ovm_test_top == null) begin
      msg = testname_plusarg ? "command line +OVM_TESTNAME=": "call to run_test(";
      ovm_report_fatal("INVTST",
          {"Requested test from ",msg, test_name, ") not found." }, OVM_NONE);
    end
  end

  if (m_children.num() == 0) begin
    ovm_report_fatal("NOCOMP",
          {"No components instantiated. You must instantiate",
           " at least one component before calling run_test. To run",
           " a test, use +OVM_TESTNAME or supply the test name in",
           " the argument to run_test(). Exiting simulation."}, OVM_NONE);
    return;
  end

  ovm_report_info("RNTST", {"Running test ",test_name, "..."}, OVM_LOW);

  fork 
    // isolated from calling process
    run_global_phase();
  join_any

  report_summarize();

  if (finish_on_completion) begin
    // forking allows current delta to complete
    fork
      $finish;
    join_none
  end

endtask


// m_reset_phase
// -------------

function void ovm_root::m_reset_phase(ovm_component comp, ovm_phase phase=null);
  string name;

  if (comp.get_first_child(name))
    do
      this.m_reset_phase(comp.get_child(name));
    while (comp.get_next_child(name));

  comp.m_curr_phase=phase;

endfunction


// m_get_phase_master
// ------------------

function ovm_phase ovm_root::m_get_phase_master(ovm_phase phase, bit set=0);
  // Returns the master phase if one hase been initialized. Otherwise, finds
  // a master by name. If none is found then the master is initialized
  // to itself.
  if(phase == null) return phase;
  if(m_phase_master.exists(phase)) return m_phase_master[phase];
  foreach(m_phase_master[i])
    if(m_phase_master[i].get_name() == phase.get_name()) begin
      if(set == 1) m_phase_master[phase] = m_phase_master[i];
      return m_phase_master[i];
    end

  if(set == 1) m_phase_master[phase] = phase;
  return phase;
endfunction


//------------------------------------------------------------------------------
// Phase control
//------------------------------------------------------------------------------


// run_global_func_phase
// ---------------------

// Limitations on usage:
//
// Given phase can not be ahead of any un-executed task-based phases.
//
// The #0 after triggering the phase's start and done events can not occur
// in a function. Any processes waiting on a function-based phase to start
// or finish will not resume until all phases up through the given phase
// have executed.

function void ovm_root::run_global_func_phase(ovm_phase phase=null, bit upto=0);

  time timeout;
  bit run_all_phases;

  //Get the master phase in case the input phase is an alias.
  phase = m_get_phase_master(phase);

  if (phase != null) begin
    if (!m_phase_q.exists(phase)) begin
      ovm_report_fatal("PHNTFD", {"Phase %0s not registered.",phase.get_name()}, OVM_NONE); 
      return;
    end
    if (upto) begin
      ovm_phase prev_ph;
      if (phase == m_first_phase)
        return;
      prev_ph = m_first_phase;
      while (phase != m_phase_q[prev_ph])
        prev_ph = m_phase_q[prev_ph];
      phase = prev_ph;
    end
    // make sure we've something to do
    if (phase.is_done()) begin
      ovm_report_warning("PHDONE", {"Phase ", phase.get_name()," already executed."}, OVM_NONE);
      return;
    end

  end
  else begin
    run_all_phases = 1;
    phase = m_last_phase;
  end

  while (m_curr_phase != phase) begin

    if (m_curr_phase == null)
      m_curr_phase = m_first_phase;
    else
      m_curr_phase = m_phase_q[m_curr_phase];

    if (m_curr_phase.is_task()) begin
        ovm_report_fatal("TASKPH",
          {"Phase ", m_curr_phase.get_name(),
          " is a time-consuming method. Cannot be run using",
          " ovm_root::run_global_phase_func()"}, OVM_NONE);
        return;
    end

    // Trigger phase's in_progress event.
    m_curr_phase.m_set_in_progress();
    // #0; can't call this in a func

    ovm_report_info("STARTPH",
      $psprintf("STARTING PHASE %0s",m_curr_phase.get_name()),int'(OVM_FULL)+1);

      m_do_phase(this,m_curr_phase);

    ovm_report_info("ENDPH",
      $psprintf("ENDING PHASE %0s",m_curr_phase.get_name()),int'(OVM_FULL)+1);

    // Trigger phase's done event.
    m_curr_phase.m_set_done();
    // #0; can't call this in a func

    // If error occurred during elaboration, exit with FATAL.
    if (m_curr_phase == end_of_elaboration_ph) begin
      ovm_report_server srvr;
      srvr = get_report_server();
      if(srvr.get_severity_count(OVM_ERROR) > 0) begin
        ovm_report_fatal("ovm", "elaboration errors", OVM_NONE);
        //#0; // $finish is called in a forked process in ovm_report_object::die.
            // this forces that process to start, preventing us from continuing
        return;
      end

      if (enable_print_topology || ovm_enable_print_topology)
        print_topology();
    end

    // if next phase is end_of_elab, the resolve all connections
    if (m_phase_q[m_curr_phase] == end_of_elaboration_ph)
      do_resolve_bindings();

    if (run_all_phases)
      phase = m_last_phase;

  end

endfunction



// run_global_phase
// ----------------

task ovm_root::run_global_phase(ovm_phase phase=null, bit upto=0);

  static semaphore sema=new(1);

  time timeout;
  bit run_all_phases;

  sema.get();

  //Get the master phase in case the input phase is an alias.
  phase = m_get_phase_master(phase);

  if (phase != null) begin
    if (!m_phase_q.exists(phase)) begin
      ovm_report_fatal("PHNTFD", {"Phase ", phase.get_name()," not registered."}, OVM_NONE);
      return;
    end
    // if only running up to the given phase, run through previous phase 
    if (upto) begin
      ovm_phase prev_ph;
      if (phase == m_first_phase)
        return;
      prev_ph = m_first_phase;
      while (phase != m_phase_q[prev_ph])
        prev_ph = m_phase_q[prev_ph];
      phase = prev_ph;
    end
    // make sure we've something to do
    if (phase.is_done()) begin
      ovm_report_warning("PHDONE", {"Phase ", phase.get_name()," already executed."}, OVM_NONE);
      return;
    end
      
  end
  else begin
    run_all_phases = 1;
    phase = m_last_phase;
  end


  // MAIN LOOP: Executes all phases from the current phase
  // through the phase given in the argument. If 'phase' is null,
  // will run through all phases, even those that may have been added in
  // phases that have yet to run.

  while (m_curr_phase != phase) begin

    if (m_curr_phase == null)
      m_curr_phase = m_first_phase;
    else
      m_curr_phase = m_phase_q[m_curr_phase];

    // Trigger phase's in_progress event.
    // The #0 allows any waiting processes to resume before we continue.
    m_curr_phase.m_set_in_progress();
    #0;

    ovm_report_info("STARTPH",
      $psprintf("STARTING PHASE %0s",m_curr_phase.get_name()),int'(OVM_FULL)+1);

    // TASK-based phase
    if (m_curr_phase.is_task()) begin

      timeout = phase_timeout;
      // timeout is absolute time
      if ($time > 0)
        if (timeout > $time)
          timeout = timeout - $time;
        else
          timeout = 1;

       `ifdef INCA
       `define ALT_PHASING
       `endif
      `ifdef ALT_PHASING

        // IUS does not support disabling named fork blocks, so we isolate the
        // inner fork block so we can kill it using disable fork
        fork // guard process
        begin

        fork

          // Start an independent process that kills the phase, else the killing
          // stops prematurely at the component that issued the request.
          m_stop_process();

          begin // guard process
            fork
              begin
                #0; // ensures stop_process active before potential stop_request
                m_do_phase(this,m_curr_phase);
                wait fork;
              end
              begin
                if (timeout == 0)
                  wait(timeout != 0);
                #timeout ovm_report_error("TIMOUT",
                      $psprintf("Watchdog timeout of '%0t' expired.", timeout), OVM_NONE);
              end
            join_any
            disable fork;
          end // end guard process

        join_any
        disable fork;

        end
        join // end guard process

      `else // QUESTA

        fork : task_based_phase
          m_stop_process();
          begin
            #0 m_do_phase(this,m_curr_phase);
            wait fork;
          end
          begin
            if (timeout == 0)
              wait(timeout != 0);
            #timeout ovm_report_error("TIMOUT",
                $psprintf("Watchdog timeout of '%0t' expired.", timeout), OVM_NONE);
          end
        join_any
        disable task_based_phase;

      `endif // INCA-QUESTA

      if(ovm_test_done.get_objection_total(ovm_root::get()) != 0) begin
        ovm_test_done.ovm_report_warning("OBJOUT", $psprintf("%0d objection(s) are still outstanding", ovm_test_done.get_objection_total(ovm_root::get())));
        ovm_report_info("SHOW_OBJECTIONS",ovm_test_done.convert2string());
      end

    end // if (is_task)

    // FUNCTION-based phase
    else begin
      m_do_phase(this,m_curr_phase);
    end

    ovm_report_info("ENDPH",
      $psprintf("ENDING PHASE %0s",m_curr_phase.get_name()),int'(OVM_FULL)+1);

    // Trigger phase's done event.
    // The #0 allows any waiting processes to resume before we continue.
    m_curr_phase.m_set_done();
    #0;

    // If error occurred during elaboration, exit with FATAL.
    if (m_curr_phase == end_of_elaboration_ph) begin
      ovm_report_server srvr;
      srvr = get_report_server();
      if(srvr.get_severity_count(OVM_ERROR) > 0) begin
        ovm_report_fatal("ovm", "elaboration errors", OVM_NONE);
        #0; // $finish is called in a forked process in ovm_report_object::die.
            // this forces that process to start, preventing us from continuing
      end

      if (enable_print_topology || ovm_enable_print_topology)
        print_topology();
    end

    // if next phase is end_of_elab, the resolve all connections
    if (m_phase_q[m_curr_phase] == end_of_elaboration_ph)
      do_resolve_bindings();

    if (m_curr_phase == report_ph) 
      check_config_usage();
    if (run_all_phases)
      phase = m_last_phase;

  end

  sema.put();

endtask


// m_do_phase
// --------

function void ovm_root::m_do_phase (ovm_component comp, ovm_phase phase);

  // run_global_phase calls this private function for each phase in consecutive
  // order.  If the phase is a function, then all components' functions are
  // called sequentially in top-down or bottom-up order. If the phase is a
  // task, all components' tasks are forked and we return with no waiting.
  // The caller can subsequently call 'wait fork' to wait for the forked
  // tasks to complete.

  ovm_phase curr_phase;
  bit done[string];

  phase = m_get_phase_master(phase);
  curr_phase = comp.m_curr_phase;

  // This while loop is needed in case new componenents are created
  // several phases into a simulation.

  while (curr_phase != phase) begin

    ovm_phase ph;
    done.delete();

    if (curr_phase == null)
      curr_phase = m_first_phase;
    else
      curr_phase = m_phase_q[curr_phase];

    // bottom-up
    if (!curr_phase.is_top_down()) begin
      string name;
      if (comp.get_first_child(name)) begin
        do begin
          this.m_do_phase(comp.get_child(name),curr_phase);
          done[name] = 1;
        end
        while (comp.get_next_child(name));
      end
    end

    ovm_report_info("COMPPH", $psprintf("*** comp %0s (%0s) curr_phase is %0s",
      comp.get_full_name(),comp.get_type_name(),
      curr_phase.get_name()),int'(OVM_FULL)+1);

    if (curr_phase.is_task()) begin
      // We fork here to ensure that do_task_phase, a user-overridable task,
      // does not inadvertently block this process
      fork
        comp.do_task_phase(curr_phase);
      join_none
    end
    else
      comp.do_func_phase(curr_phase);

    // bottom-up 2nd pass: phase newly created components, if any
    if (!curr_phase.is_top_down()) begin

      while (comp.get_num_children() != done.num()) begin
        string name;
        if (comp.get_first_child(name)) begin
          do begin
            if (!done.exists(name)) begin
              this.m_do_phase(comp.get_child(name),curr_phase);
              done[name] = 1;
            end
          end
          while (comp.get_next_child(name));
        end
      end
    end

    // top-down
    else begin
      string name;
      if (comp.get_first_child(name))
        do begin
          this.m_do_phase(comp.get_child(name),curr_phase);
        end
        while (comp.get_next_child(name));
    end

  end
endfunction


// get_current_phase
// -----------------

function ovm_phase ovm_root::get_current_phase();
  return m_curr_phase;
endfunction


//------------------------------------------------------------------------------
// Stopping
//------------------------------------------------------------------------------

// stop_request
// ------------

function void ovm_root::stop_request();
  ->m_stop_request_e;
endfunction


// m_stop_process
// --------------

task ovm_root::m_stop_process();
  @m_stop_request_e;
  m_stop_request(stop_timeout);
endtask

// in_stop_request
// ---------------

function bit ovm_root::in_stop_request();
  return m_in_stop_request;
endfunction

// m_stop_request
// --------------

task ovm_root::m_stop_request(time timeout=0);

  // timeout is absolute time
  if ($time > 0)
    if (timeout > $time)
      timeout = timeout - $time;
    else
      timeout = 1;

  // stop request valid for running task-based phases only
  if (m_curr_phase == null || !m_curr_phase.is_task()) begin
    ovm_report_warning("STPNA",
      $psprintf("Stop-request has no effect outside non-time-consuming phases%s%s",
                "current phase is ",m_curr_phase==null?
                "none (not started":m_curr_phase.get_name()), OVM_NONE);
    return;
  end
  m_in_stop_request=1;

  // All stop tasks are forked from a single thread so 'wait fork'
  // can be used. We fork the single thread as well so that 'wait fork'
  // does not wait for threads previously started by the caller's thread.

  // IUS does not support disabling named fork blocks, so we isolate the
  // inner fork block so we can kill it using disable fork
  `ifdef INCA

  fork begin // guard process
    fork
      begin
        //If objections are outstanding, wait for them to finish first
        wait(m_objections_outstanding==0);
        m_executing_stop_processes = 1;
        m_do_stop_all(this);
        wait fork;
        m_executing_stop_processes = 0;
      end
      begin
        if (timeout == 0)
          wait(timeout != 0);
        #timeout ovm_report_warning("STPTO",
         $psprintf("Stop-request timeout of %0t expired. Stopping phase '%0s'",
                           timeout, m_curr_phase.get_name()), OVM_NONE);
      end
    join_any
    disable fork;
  end
  join

  `else // QUESTA

  fork : stop_tasks
    begin
      //If objections are outstanding, wait for them to finish first
      wait(m_objections_outstanding==0);
      m_executing_stop_processes = 1;
      m_do_stop_all(this);
      wait fork;
      m_executing_stop_processes = 0;
    end
    begin
      if (timeout == 0)
        wait(timeout != 0);
      #timeout ovm_report_warning("STPTO",
       $psprintf("Stop-request timeout of %0t expired. Stopping phase '%0s'",
                         timeout, m_curr_phase.get_name()), OVM_NONE);
    end
  join_any
  disable stop_tasks;

  `endif // INCA

  // all stop processes have completed, or a timeout has occured
  this.do_kill_all();

  m_in_stop_request=0;
endtask


// m_do_stop_all
// -------------

task ovm_root::m_do_stop_all(ovm_component comp);

  string name;

  // we use an external traversal to ensure all forks are 
  // made from a single threaad.
  if (comp.get_first_child(name))
    do begin
      m_do_stop_all(comp.get_child(name));
    end
    while (comp.get_next_child(name));

  if (comp.enable_stop_interrupt) begin
    fork begin
      comp.stop(m_curr_phase.get_name());
    end
    join_none
  end

endtask


// This objection is used to communicate all objections dropped at the
// root level so that the ovm_top can start the shutdown.

// Function: raised
//
//

function void ovm_root::raised (ovm_objection objection, ovm_object source_obj, 
                              int count);
  if (m_executing_stop_processes)
    ovm_report_warning("ILLRAISE", "An ovm_test_done objection was raised during the execution of component stop processes for the stop_request. The objection is ignored by the stop process.", OVM_NONE);
  else
    m_objections_outstanding = 1;
endfunction


// Task: all_dropped
//
//

task ovm_root::all_dropped (ovm_objection objection, ovm_object source_obj, 
                          int count);
  m_objections_outstanding = 0;
endtask

//------------------------------------------------------------------------------
// Phase Insertion
//------------------------------------------------------------------------------

// insert_phase
// ------------

function void ovm_root::insert_phase(ovm_phase new_phase,
                                     ovm_phase exist_phase);
  ovm_phase exist_ph;
  ovm_phase master_ph;
  string s;

  // Get the phase object that is in charge of a given named phase. Since we
  // are inserting the phase, set the master if not set.
  master_ph = m_get_phase_master(new_phase, 1);
  exist_phase = m_get_phase_master(exist_phase);

  if (build_ph.is_done()) begin
    ovm_report_fatal("PHINST", "Phase insertion after build phase prohibited.", OVM_NONE);
    return;
  end

  if (exist_phase != null && exist_phase.is_done() ||
      exist_phase == null && m_curr_phase != null) begin 
    ovm_report_fatal("PHINST", {"Can not insert a phase at a point that has ",
      "already executed. Current phase is '", m_curr_phase.get_name(),"'."}, OVM_NONE);
    return;
  end

  if (new_phase == null) begin
    ovm_report_fatal("PHNULL", "Phase argument is null.", OVM_NONE);
    return;
  end

  if (exist_phase != null && !m_phase_q.exists(exist_phase)) begin
    //could be an aliased phase. The phase may not exist in the queue, but if
    //the name matches one in the queue then it is a possible alias
    if(get_phase_by_name(exist_phase.get_name()) == null) begin
      ovm_report_fatal("PHNTFD", {"Phase '",exist_phase.get_name(),
                      "' is not registered."}, OVM_NONE);
      return;
    end
  end

  // If the new phase being added is an alias object, add the alias and
  // return.
  if(master_ph != new_phase) begin
    master_ph.add_alias(new_phase, exist_phase);
    return;
  end

  if (m_phase_q.exists(new_phase)) begin
    if ((exist_phase == null && m_first_phase != new_phase) ||
        (exist_phase != null && m_phase_q[exist_phase] != new_phase)) begin
      ovm_report_error("PHDUPL", {"Phase '", new_phase.get_name(),
        "' is already registered in a different order."}, OVM_NONE);
    end
    return;
  end

  new_phase.set_insertion_phase(exist_phase);
  if (exist_phase == null) begin
    m_phase_q[new_phase] = m_first_phase;
    m_first_phase = new_phase;
  end
  else begin
    m_phase_q[new_phase] = m_phase_q[exist_phase];
    m_phase_q[exist_phase] = new_phase;
  end

  if (m_phase_q[new_phase] == null)
    m_last_phase = new_phase;

endfunction


// get_phase_by_name
// -----------------

function ovm_phase ovm_root::get_phase_by_name (string name);
  ovm_phase m_ph;
  foreach (m_phase_q[ph]) begin
    m_ph = ph;
    if(m_ph.get_name() == name) 
      return ph;
  end
  return null;
endfunction


//------------------------------------------------------------------------------
// Component Search & Printing
//------------------------------------------------------------------------------


// find_all
// --------

function void ovm_root::find_all(string comp_match, ref ovm_component comps[$],
                                 input ovm_component comp=null); 
  string name;

  if (comp==null)
    comp = this;

  if (comp.get_first_child(name))
    do begin
      this.find_all(comp_match,comps,comp.get_child(name));
    end
    while (comp.get_next_child(name));

  if (ovm_is_match(comp_match, comp.get_full_name()) &&
       comp.get_name() != "") /* ovm_top */
    comps.push_back(comp);

endfunction


// find
// ----

function ovm_component ovm_root::find (string comp_match);
  ovm_component comp_list[$];

  find_all(comp_match,comp_list);

  if (comp_list.size() > 1)
    ovm_report_warning("MMATCH",
    $psprintf("Found %0d components matching '%s'. Returning first match, %0s.",
              comp_list.size(),comp_match,comp_list[0].get_full_name()), OVM_NONE);

  if (comp_list.size() == 0) begin
    ovm_report_warning("CMPNFD",
      {"Component matching '",comp_match,
       "' was not found in the list of ovm_components"}, OVM_NONE);
    return null;
  end

  return comp_list[0];
endfunction


// print_topology
// --------------

function void ovm_root::print_topology(ovm_printer printer=null);

  string s;

  ovm_report_info("OVMTOP", "OVM testbench topology:", OVM_LOW);

  if (m_children.num()==0) begin
    ovm_report_warning("EMTCOMP", "print_topology - No OVM components to print.", OVM_NONE);
    return;
  end

  if (printer==null)
    printer = ovm_default_printer;

  if (printer.knobs.sprint)
    s = printer.m_string;

  foreach (m_children[c]) begin
    if(m_children[c].print_enabled) begin
      printer.print_object("", m_children[c]);  
      if(printer.knobs.sprint)
        s = {s, printer.m_string};
    end
  end

  printer.m_string = s;

endfunction


//------------------------------------------------------------------------------
//
// REVIEW FOR DEPRECATION OR REMOVAL
//
//------------------------------------------------------------------------------

// print_unit
// ----------

function void ovm_root::print_unit (string name, ovm_printer printer=null);

  ovm_component comp;
  static bit issued=0;

  if (!issued) begin
    issued=1;
    ovm_report_warning("deprecated",
      {"ovm_root::print_unit() is an internal method that has been deprecated.",
      " It is replaced by comp=ovm_top.find(name); comp.print(printer);"}, OVM_NONE);
  end
  comp = find(name);
  if (comp != null)
    comp.print(printer);
endfunction


// print_units
// -----------

function void ovm_root::print_units (ovm_printer printer=null);

  string s;
  static bit issued=0;

  if (!issued) begin
    issued=1;
    ovm_report_warning("deprecated",
      {"ovm_root::print_units() is an internal method that ",
      "has been deprecated. It can be replaced by ovm_top.print(printer);"}, OVM_NONE);
  end

  print_topology(printer);

endfunction


// print_unit_list
// ---------------

function void ovm_root::print_unit_list(ovm_component comp=null);

  string name;
  static bit issued=0;

  if (!issued) begin
    issued=1;
    ovm_report_warning("deprecated",
      {"ovm_root::print_unit_list() is an internal method that ",
      "has been deprecated."}, OVM_NONE);
  end

  if (comp==null) begin
    comp = this;
    if (m_children.num()==0) begin
      ovm_report_warning("NOUNIT","No OVM components to print. ", OVM_NONE);
      return;
    end
    $display("List of ovm components");
  end
  else begin
    $display("%s (%s)", comp.get_full_name(), comp.get_type_name());
  end

  if (comp.get_first_child(name))
    do begin
      this.print_unit_list(comp.get_child(name));
    end
    while (comp.get_next_child(name));

endfunction

`endif //OVM_ROOT_SVH
