// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    All Rights Reserved Worldwide
// 
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
// 

import "DPI" function int vmm_xvc_get_next_cmd(output int argc,
                                               output string argv_array[0:99],
                                               output string testfile,
                                               output string linec,
                                               output string errmsg);

import "DPI" function void vmm_xvc_tcl_execute_file(string filename);

typedef class vmm_xvc_stop_on_event;

`include "std_lib/vmm_xvc_event.sv"

`ifdef VCS
(* _vcs_vmm_class = 1 *)
`endif
class vmm_xvc_manager extends xvc_manager;

   // Command parsing state variables
   local string line;
   local string argv[$];
   local int    linec;
   local string testfile;
   local string errMsg;

   // Logging command state variables
   local int    iter;
   local string pattern;
   local bit    is_pattern;
   local int    open_files[string];
   local int    open_trace_files[string];

   // Scenario execution state variables
   local vmm_xvc_scenario   current_sc;
   local vmm_xvc_scenario   scenarios[$];
   local vmm_xvc_scenario   exec_scenarios[$];
   /*local*/ vmm_xvc_event  events[`VMM_AA_INT];

   local vmm_xvc_stop_on_event stop_on[string]; //indexed by fully qualified event name
                                                //of the form <sid>.<sev> or <gev>
   local event terminate_ev;
   local event terminate_ex;

   extern function new(string name = "VMM XVC Manager");
   extern task run(string testfile);

   extern local function int get_next_cmd();
   extern local function bit process_cmd();
   extern local function void for_reset(string inst);
   extern local function xvc_xactor for_each();
   extern local function bit try_verbosity();
   extern local function bit try_log();
   extern local function bit try_xvctrace();
   extern local function bit try_covfile();
   extern local function bit try_stoponerror();
   extern local function bit try_stoponevent();
   extern local function bit try_scenario();
   extern local function bit try_mapevent();
   extern local function bit try_event();
   extern local function bit try_action();
   extern local function bit try_interrupt();
   extern local function bit try_execute();

   extern local function void save_scenario(vmm_xvc_scenario sc);
   extern local task execute();
   extern local task execute_scenario(vmm_xvc_scenario sc);
   extern local task execute_actions(vmm_xvc_scenario sc,
                                     xvc_xactor   xvc);

   extern /*local*/ function vmm_xvc_scenario lookup_scenario(string name);

   extern local task add_stop_on (string ev_fullname, 
                                  int    count, 
                                  int    immediate,
                                  string fname, 
                                  int    linec);
   extern local function void terminate_stop_on();
   extern local function vmm_xvc_event get_stop_on_event(string ev_str);
   extern local function void start_stop_on(ref vmm_xvc_scenario current_sc);
endclass: vmm_xvc_manager


//
// Models the details of the action with associated information
//
`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
class vmm_xvc_action_block;

    xvc_action       action;
    string           descr;
    xvc_xactor       xvc;
    vmm_xvc_scenario sc;
    vmm_xvc_manager  xvc_mgr;
    int              wait_id; //-1 if there is nothing to wait on
    int              emitQ[$];

    bit is_interrupt;
    bit is_interrupt_oneshot;

    local event terminate_ev;

    extern task emit();
    extern task wait_for();
    extern function void kill();
    extern function void set_emit(ref string emit_ids[$]);
    extern function void set_wait(string wait_str);
endclass: vmm_xvc_action_block


`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
class vmm_xvc_stop_on_event;
  
   int    count;      //no. of occurences to wait before stopping
   int    immediate;  //1 if immediate termination, 0 if wait until scn end
   string fname;      //fname where cmd was seen
   int    linec;      //lineno. where cmd was seen
  
   extern function new(int    count,
                       int    immediate,
                       string fname,
                       int    linec);
endclass: vmm_xvc_stop_on_event


`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
class vmm_xvc_scenario;
   static `VMM_LOG log = new("vmm_xvc_scenario", "class");
   
   string name;
   string descr;

   string testfile;
   int linec;

   vmm_notify notify;
   vmm_xvc_event events[`VMM_AA_INT];

   vmm_xvc_action_block actionQ[$];

   typedef enum {STARTED, DONE} notify_e;

   extern function new(string name);
endclass: vmm_xvc_scenario






function vmm_xvc_scenario::new(string name);
   this.name   = name;
   this.notify = new(this.log);

   void'(this.notify.configure(STARTED, vmm_notify::ON_OFF));
   void'(this.notify.configure(DONE, vmm_notify::ON_OFF));
endfunction: new





function vmm_xvc_manager::new(string name);
   super.new(name);
endfunction: new


task vmm_xvc_manager::run(string testfile);

   // Start all known xvcs
   `foreach (this.xvcQ,i) begin
      this.xvcQ[i].start_xactor();
   end

   // Provide the file to be executed to the C-TCL interpreter
   // which pre-processes the file
   vmm_xvc_tcl_execute_file(testfile);

   // Iterate over every command in the file and process it
   begin
      while (this.get_next_cmd()) begin
         this.process_cmd();
      end
   end

   // Execute only if there are no errors in the testfile
   if (this.log.get_message_count(vmm_log::FATAL_SEV + vmm_log::ERROR_SEV,
                                  "/./", "/./") > 0) begin
      `vmm_fatal(this.log, "Unable to execute testfile because of errors");
   end else 
      this.execute();
endtask: run


//
// Check if one more command is available.
// Returns 1 when command is available, 0 if completed
//
function int vmm_xvc_manager::get_next_cmd();
   string argv_array[0:99];
   int    argc, i;
   string linec_str;

`ifdef VCS2006_06
   // Work-around for NYI feature in VCS2006.06
   // but IEEE 1800-2009 compliant
   this.argv.delete();
`else
`ifdef INCA
   this.argv.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.argv = '{};
`endif
`endif

   get_next_cmd = vmm_xvc_get_next_cmd(argc,
                                       argv_array,
                                       this.testfile,
                                       linec_str,
                                       this.errMsg);
   if (get_next_cmd == 0) return 0;

   this.line = "";
   this.linec = linec_str.atoi();
   for (i = 0; i < argc; i++) begin
      this.argv.push_back(argv_array[i]); 
      this.line = {this.line, argv_array[i], " "};
   end
endfunction: get_next_cmd


//
// Process a parsed command and return 1 on success.
//
function bit vmm_xvc_manager::process_cmd();

`ifdef VMM_DETAILED_MSGS
   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::DEBUG_SEV )) begin
      void'(this.log.text($psprintf("%s, line %0d:%s",
                                    this.testfile, this.linec, this.line)));
      this.log.end_msg(); 
   end
`endif

   // is it a known command??
   if (this.try_scenario()) return 1;
   if (this.try_action()) return 1;
   if (this.try_verbosity()) return 1;
   if (this.try_log()) return 1;
   if (this.try_xvctrace()) return 1;
   if (this.try_covfile()) return 1;
   if (this.try_stoponerror()) return 1;
   if (this.try_stoponevent()) return 1;
   if (this.try_event()) return 1;
   if (this.try_mapevent()) return 1;
   if (this.try_interrupt()) return 1;
   if (this.try_execute()) return 1;
   
   `vmm_error(this.log, 
              $psprintf("%s, line %0d: Unknown command '%s'.",
                        this.testfile, 
                        this.linec, 
                        this.argv[0])
             );
endfunction: process_cmd


function void vmm_xvc_manager::for_reset(string inst);
   this.iter = 0;
   this.pattern = inst;
   if(`vmm_str_match(this.pattern, "^/(.*)/$")) begin
      this.pattern = `vmm_str_backref(this.pattern, 0);
      this.is_pattern = 1;
   end else begin
      this.is_pattern = 0;
   end
endfunction: for_reset
  

function xvc_xactor vmm_xvc_manager::for_each();
   xvc_xactor xvc;
   string     name;
   string     inst;
   bit        pattern_match;

   while (this.iter < xvcQ.size()) begin

      xvc = this.xvcQ[this.iter++];

      inst = xvc.get_instance();
      pattern_match = `vmm_str_match(inst, this.pattern);

      if ((this.is_pattern && pattern_match) ||
           (!this.is_pattern && (inst == this.pattern))) begin
         return xvc;
      end
   end
   for_each = null;
endfunction: for_each


//
// Check if this is a VERBOSITY command.
// Returns 1 if it is, 0 otherwise.
//
function bit vmm_xvc_manager::try_verbosity();
   int severity;
 
   if (this.argv[0].tolower() != "verbosity") begin
      return 0;
   end
   try_verbosity = 1;
 
   //put out any messages caught in the parser
   if (this.errMsg.len() > 0) begin
      `vmm_fatal(this.log, this.errMsg);
      return 1;
   end 

   begin
      string level = this.argv[this.argv.size-1].tolower;
      if (level == "error") 
         severity = vmm_log::ERROR_SEV;
      else if (level == "warning")
         severity = vmm_log::WARNING_SEV;
      else if (level == "normal")
         severity = vmm_log::NORMAL_SEV;
      else if (level == "trace")
         severity = vmm_log::TRACE_SEV;
      else if (level == "debug")
         severity = vmm_log::DEBUG_SEV;
      else if (level == "verbose")
         severity = vmm_log::VERBOSE_SEV;
      else begin
         `vmm_fatal(this.log, 
                    $psprintf("%s, line %0d: Invalid severity level \"%s\"",
                              this.testfile, 
                              this.linec, 
                              level)
                   );
         return 1;
      end
   end

   begin
     string inst;
     inst = this.argv[1];
     if (inst.tolower() == "all") 
        inst = "/./";
     this.log.set_verbosity(severity, "/./", inst, 1);
   end
endfunction: try_verbosity


//
// Check if this is a LOG command.
// Returns 1 if it is, 0 otherwise.
//
function bit vmm_xvc_manager::try_log();
   int fp;
   int stop;
   int append;

   if (this.argv[0].tolower() != "log") begin
      return 0;
   end
   try_log = 1;

   //put out any messages caught in the parser
   if (this.errMsg.len() > 0) begin
      `vmm_fatal(this.log, this.errMsg);
      return 1;
   end 
 
   //log NONE
   if (this.argv.size() == 2) begin
      string tmpname;
      for (int i = this.open_files.first(tmpname);
           i != 0;
           i = this.open_files.next(tmpname)) begin
         this.log.log_stop(this.open_files[tmpname], "/./", "/./", 1);
      end
      return 1;
   end

   begin
      string fname;
      int fname_len;
      append = 0;
      fname  = this.argv[this.argv.size()-1];
      fname_len = fname.len();

      // Append or stop?
      if (fname.getc(0) == 45) begin // '-'
         stop = 1;
         fname = fname.substr(1,fname_len-1);
      end else begin
         stop = 0;
         if (fname.getc(0) == 43) begin // '+'
            append = 1;
            fname = fname.substr(1,fname_len-1);
         end
      end

      // Is the file already open?
      if (this.open_files.exists(fname)) begin
         fp = this.open_files[fname];
      end else begin
         if (stop) begin
            `vmm_fatal(this.log, 
                       $psprintf("%s, line %0d: Unknown file \"%s\"",
                                 this.testfile, 
                                 this.linec, 
                                 fname)
                      );
            return 1;
         end
         fp = $fopen(fname, (append)? "a" : "w");
         if (!fp) begin
            `vmm_fatal(this.log, 
                       $psprintf("%s, line %0d: Unable to open file \"%s\" for %s",
                                 this.testfile, 
                                 this.linec, 
                                 fname,
                                 (append) ? "appending" : "writing")
                      );
            return 1;
         end
         this.open_files[fname] = fp;
      end
   end

   begin
     string inst;
     inst = this.argv[1];
     if (inst.tolower() == "all") 
        inst = "/./";
     if (stop) begin
        this.log.log_stop(fp, "/./", inst, 1);
     end else begin
        this.log.log_start(fp, "/./", inst, 1);
     end
   end
endfunction: try_log


//
// Check if this is a XVC_TRACE command.
// Returns 1 if it is, 0 otherwise.
//
function bit vmm_xvc_manager::try_xvctrace();
   int fp;
   int stop;
   int append;

   if (this.argv[0].tolower() != "xvctrace") begin
      return 0;
   end
   try_xvctrace = 1;

   //put out any messages caught in the parser
   if (this.errMsg.len() > 0) begin
      `vmm_fatal(this.log, this.errMsg);
      return 1;
   end 
 
   //xvctrace NONE
   if (this.argv.size() == 2) begin
      string tmpname;
      for (int i = this.open_trace_files.first(tmpname);
           i != 0;
           i = this.open_trace_files.next(tmpname)) begin
         this.trace.log_stop(this.open_trace_files[tmpname], "/./", "/./", 1);
      end
      return 1;
   end

   begin
      int fname_len;
      string fname;
      append = 0;
      fname  = this.argv[this.argv.size()-1];
      fname_len = fname.len();

      // Append or stop?
      if (fname.getc(0) == 45) begin  // '-'
         stop = 1;
         fname = fname.substr(1,fname_len-1);
      end else begin
         stop = 0;
         if (fname.getc(0) == 43) begin  // '+'
            append = 1;
            fname = fname.substr(1,fname_len-1);
         end
      end

      // Is the file already open?
      if (this.open_files.exists(fname)) begin
         fp = this.open_trace_files[fname];
      end else begin
         if (stop) begin
            `vmm_fatal(this.log, 
                       $psprintf("%s, line %0d: Unknown file \"%s\"",
                                 this.testfile, 
                                 this.linec, 
                                 fname)
                                );
            return 1;
         end
         fp = $fopen(fname, (append)? "a" : "w");
         if (!fp) begin
            `vmm_fatal(this.log, 
                       $psprintf("%s, line %0d: Unable to open file \"%s\" for %s",
                                 this.testfile, 
                                 this.linec, 
                                 fname,
                                 (append) ? "appending" : "writing")
                                );
            return 1;
         end
         this.open_trace_files[fname] = fp;
      end

   end

   begin
     string inst;
     string name;
     inst = this.argv[1];
     name = "/./";
     if (inst.tolower() == "all") begin
        inst = "/./";
     end 
     if (inst.tolower() == "manager") begin
        inst = "";
        name = "";
     end
      
     if (stop) begin
        this.trace.log_stop(fp, name, inst, 1);
     end else begin
        this.trace.log_start(fp, name, inst, 1);
     end
   end
endfunction: try_xvctrace
 

//
// Check if this is a COVFILE command.
// Returns 1 if it is, 0 otherwise.
//
function bit vmm_xvc_manager::try_covfile();

   if (this.argv[0].tolower() != "covfile") begin
      return 0;
   end
   try_covfile = 1;

   if (this.argv[1].tolower() == "none") begin
      `vmm_warning(this.log, 
                   $psprintf("%s, line %0d: NYI: Turning coverage OFF... NYI: ignoring",
                             this.testfile, 
                             this.linec)
                  );
      return 1;
   end

   $set_coverage_db_name(this.argv[1]);
endfunction: try_covfile

 
//
// Check if this is a STOPONERROR command.
// Returns 1 if it is, 0 otherwise.
//
function bit vmm_xvc_manager::try_stoponerror();
   int n;

   if (this.argv[0].tolower() != "stoponerror") begin
      return 0;
   end
   try_stoponerror = 1;
   n = this.argv[1].atoi();
   if (n <= 0) begin
      `vmm_fatal(this.log, 
                 $psprintf("%s, line %0d: Invalid number of error messages",
                           this.testfile, 
                           this.linec)
                );
      return 1;
   end

   this.log.stop_after_n_errors(n);
endfunction: try_stoponerror


//
// Check if this is a STOPONEVENT command.
// Returns 1 if it is, 0 otherwise.
//
function bit vmm_xvc_manager::try_stoponevent();
   int arg_no;
   int count;
   int immediate;
   string ev_fullname;

   if (this.argv[0].tolower() != "stoponevent") begin
      return 0;
   end
   try_stoponevent = 1;

   //put out any messages caught in the parser
   if (this.errMsg.len() > 0) begin
      `vmm_fatal(this.log, this.errMsg);
      return 1;
   end 

   ev_fullname = this.argv[1];
   arg_no = 2;

   //get the type of stop: IMMEDIATE or GRACEFUL
   if ((this.argv[arg_no].tolower() == "immediate") ||
       (this.argv[arg_no].tolower() == "graceful")) begin
      immediate = (this.argv[arg_no].tolower() == "immediate");
      arg_no++;
   end else begin
      immediate = 1;
   end

   count = 1;
   if (arg_no < this.argv.size()) begin
      count = this.argv[arg_no].atoi();
      if (count < 0) begin
         `vmm_error(this.log,
                    $psprintf("%s, line %0d: stoponerror count [%0d] < 0 ",
                              this.testfile, 
                              this.linec, 
                              count )
                   );
          count = 1; //reset count to 1
      end
   end

   //add to stopwatch
   this.add_stop_on(ev_fullname, count, immediate, this.testfile, this.linec);
 
endfunction: try_stoponevent
 

//
// Check if this is a SCENARIO command.
// Returns 1 if it is, 0 otherwise.
//
function bit vmm_xvc_manager::try_scenario();
   if (this.argv[0].tolower() != "scenario") begin
      return 0;
   end
   try_scenario = 1;
   //put out any messages caught in the parser
   if (this.errMsg.len() > 0) begin
      `vmm_fatal(this.log, this.errMsg);
      return 1;
   end 

   if (this.current_sc != null) begin
      this.save_scenario(this.current_sc);
      this.current_sc = null;  
   end      

   this.current_sc = this.lookup_scenario(this.argv[1]);
   if (this.current_sc != null) begin
      `vmm_fatal(this.log, 
                 $psprintf("%s, line %0d: Scenario \"%s\" already defined at %s, line %0d",
                           this.testfile, 
                           this.linec, 
                           this.argv[1],
                           this.current_sc.testfile, 
                           this.current_sc.linec)
                );
      this.current_sc = null;
      return 1;
   end
   this.current_sc = new(this.argv[1]);
   if (this.argv.size() == 3)
      this.current_sc.descr = this.argv[2];
   else
      $sformat(this.current_sc.descr,
              "Unnamed Scenario:%s[%0d]",
              this.testfile, 
              this.linec);
   this.current_sc.testfile = this.testfile;
   this.current_sc.linec    = this.linec;

endfunction: try_scenario
 

//
// Check if this is a MAPEVENT command.
// Returns 1 if it is, 0 otherwise.
//
function bit vmm_xvc_manager::try_mapevent();

   vmm_xvc_event_mapped ev;
   string event_id;
   string event_descr;
   string event_map;
   string inst; //xvc_instance
   string local_id; //event in the xvc_instance 
   int event_global;
   int event_oneshot; 
   int arg_no;

   if (this.argv[0].tolower() != "mapevent") begin
      return 0;
   end
   try_mapevent = 1;
   
   //put out any messages caught in the parser
   if (this.errMsg.len() > 0) begin
      `vmm_fatal(this.log, this.errMsg);
      return 1;
   end 

   //default settings for the event
   event_global = 0;
   event_oneshot = 0;

   arg_no = 1;
   if (this.argv[arg_no].tolower() == "oneshot") begin
      event_oneshot = 1;
      arg_no++;
   end
   if (this.argv[arg_no].tolower() == "global") begin
      event_global = 1;
      arg_no++;
   end else if (this.argv[arg_no].tolower() == "local") begin
      arg_no++;
   end else if (this.current_sc == null) begin
      event_global = 1;
   end

   event_id = this.argv[arg_no++];
   //Check on event_id be positive
   if (event_id.atoi() < 0) begin
      `vmm_fatal(this.log,
                 $psprintf("%s[%0d] Event id should be > 0",
                 this.testfile,
                 this.linec)
                 );
   end

   //next arg should  be an 'IS' command : need not enforce it?
   arg_no++;
   //next arg is the xvc instance string 
   inst = this.argv[arg_no++];
   //next arg is the "E[VENT]" command, need not enforce it ?
   arg_no++;
   //next arg is the local event id.
   local_id = this.argv[arg_no++];
   //Check on local_id be positive
   if (local_id.atoi() < 0) begin
      `vmm_fatal(this.log,
                 $psprintf("%s[%0d] Event id should be > 0",
                 this.testfile,
                 this.linec)
                 );
   end

   //next arg is the optional event description
   if (arg_no < this.argv.size())
      event_descr = this.argv[arg_no];
   else
      $sformat(event_descr,
          "Indicating %s event %s",
          ((this.current_sc == null) || (event_global)) ? "global" : "scenario",
          event_id);

   //More checks: doesnt make sense having a local event
   //  if the current scenario is null
   if (!event_global) begin
      if (this.current_sc == null) begin
         `vmm_fatal(this.log,
                    $psprintf("%s[%0d] Local event declared before scenario declaration",
                    this.testfile,
                    this.linec)
                    );
          return 1;
      end
   end

   ev = new(event_id.atoi(),
            event_descr,
            event_global,
            event_oneshot,
            event_global ? this.log : this.current_sc.log,
            event_global ? this.notify : this.current_sc.notify,
            event_global ? null : this.current_sc,
            this
            );

   // Identify all target XVCs
   begin
      xvc_xactor xvc;

      this.for_reset(inst);
      for (xvc = this.for_each(); xvc != null; xvc = this.for_each()) begin
         vmm_xvc_event_local local_ev = new(xvc, local_id.atoi());
         ev.xvcQ.push_back(local_ev);
      end
      if (ev.xvcQ.size() == 0) begin
         `vmm_error(this.log, 
                    $psprintf("%s, line %0d: No such XVC %s",
                              this.testfile, this.linec,
                              inst)
                   );
         return 1;
      end
   end 
  

   //Add to either global or current scenario assoc array
   if (event_global) begin
      if (this.events.exists(ev.id)) begin
         `vmm_error(this.log, 
                    $psprintf("%s, line %0d: Global event %0d already exists...",
                              this.testfile, 
                              this.linec, 
                              ev.id)
                   );
         return 1;
      end else
         this.events[ev.id] = ev;
   end else begin //scenario event
      if (this.current_sc.events.exists(ev.id)) begin
         `vmm_error(this.log, 
                    $psprintf("%s, line %0d: Scenario-level event %0d already exists in scenario %s started at %s, line %0d...",
                              this.testfile, 
                              this.linec, 
                              ev.id,
                              this.current_sc.name,
                              this.current_sc.testfile,
                              this.current_sc.linec)
                    );
         return 1;
      end else
         this.current_sc.events[ev.id] = ev;
   end
  

endfunction: try_mapevent
  

//
// Check if this is a EVENT command.
// Returns 1 if it is, 0 otherwise.
//
function bit vmm_xvc_manager::try_event();
   vmm_xvc_event_any_all ev;
   string event_id;
   string event_descr;
   string event_map;
   int event_global;
   int event_oneshot; 
   int arg_no;
 
   if (this.argv[0].tolower() != "event") begin
      return 0;
   end
   try_event = 1;
   //put out any messages caught in the parser
   if (this.errMsg.len() > 0) begin
      `vmm_fatal(this.log, this.errMsg);
      return 1;
   end 

   //default settings for the event
   event_global = 0;
   event_oneshot = 0;

   arg_no = 1;
   if (this.argv[arg_no].tolower() == "oneshot") begin
      event_oneshot = 1;
      arg_no++;
   end
   if (this.argv[arg_no].tolower() == "global") begin
      event_global = 1;
      arg_no++;
   end else if (this.argv[arg_no].tolower() == "local") begin
      arg_no++;
   end else if (this.current_sc == null) begin
      event_global = 1;
   end
   event_id = this.argv[arg_no++];
   //Check on event_id be positive
   if (event_id.atoi() < 0) begin
      `vmm_fatal(this.log,
                 $psprintf("%s[%0d] Event id should be > 0",
                 this.testfile,
                 this.linec)
                 );
   end
   
   //next arg should  be an 'IS' command : need not enforce it?
   arg_no++;
   //next arg is the event_map string i.,e 2,3.1+4 etc.,
   //  Assumed that the parser takes care of removing whitespace
   event_map = this.argv[arg_no++];
   //Event description
   if (arg_no < this.argv.size())
      event_descr = this.argv[arg_no];
   else
      $sformat(event_descr,
               "Indicating %s event %s",
                   ((this.current_sc == null) || (event_global)) ? "global" : "scenario",
               event_id);

   //More checks: doesnt make sense having a local event
   //  if the current scenario is null
   if (!event_global) begin
      if (this.current_sc == null) begin
         `vmm_fatal(this.log,
                    $psprintf("%s[%0d] Local event declared before scenario declaration",
                    this.testfile,
                    this.linec)
                    );
          return 1;
      end
   end
  
   ev = new(event_id.atoi(),
            event_descr,
            event_map,
            event_global,
            event_oneshot,
            event_global ? this.log : this.current_sc.log,
            event_global ? this.notify : this.current_sc.notify,
            event_global ? null: this.current_sc,
            this
            );

   //Add to either global or current scenario assoc array
   if (event_global) begin
      if (this.events.exists(ev.id)) begin
         `vmm_error(this.log, 
                    $psprintf("%s, line %0d: Global event %0d already exists...",
                              this.testfile, 
                              this.linec, 
                              ev.id)
                   );
         return 1;
      end else
         this.events[ev.id] = ev;
   end else begin //scenario event
      if (this.current_sc.events.exists(ev.id)) begin
         `vmm_error(this.log, 
                    $psprintf("%s, line %0d: Scenario-level event %0d already exists in scenario %s started at %s, line %0d...",
                              this.testfile, 
                              this.linec, 
                              ev.id,
                              this.current_sc.name,
                              this.current_sc.testfile,
                              this.current_sc.linec)
                    );
         return 1;
      end else
         this.current_sc.events[ev.id] = ev;
   end

endfunction: try_event


//
// Check if this is a ACTION command.
// Returns 1 if it is, 0 otherwise.
//
function bit vmm_xvc_manager::try_action();

   string inst;
   string action_str;
   string wait_for_ev;
   string emit_ev_list[$];
   int arg_no;
   
   if (this.argv[0].tolower() != "action") begin
      return 0;
   end
   try_action = 1;
   //put out any messages caught in the parser
   if (this.errMsg.len() > 0) begin
      `vmm_fatal(this.log, this.errMsg);
      return 1;
   end 

   //parse cmd and extract information.
   //syntax is of the form:
   //  A[CTION] <instance> <action> \
   //    [W[AIT] wait_for] \ 
   //    [E[VENT] event [event]]
   arg_no = 1;
   inst       = this.argv[arg_no++];
   action_str = this.argv[arg_no++]; 
   while (1) begin
      string tmpstr;
      //if there are args still left over..
      if (arg_no >= this.argv.size()) 
         break;
      tmpstr = this.argv[arg_no].tolower;
      if (`vmm_str_match(tmpstr, "^(w|wait)")) begin
         arg_no++;
         //ToDo: error if no wait argument
         wait_for_ev = this.argv[arg_no++];
         continue;
      end
      tmpstr = this.argv[arg_no].tolower;
      if (`vmm_str_match(tmpstr, "^(e|event)"))  begin
         arg_no++;
         //ToDo: error if dont have atleast 1 arg
         while(`vmm_str_match(this.argv[arg_no], "^[0-9.]*$")) begin
            emit_ev_list.push_back(this.argv[arg_no]);
            arg_no++;
            if (arg_no >= this.argv.size()) 
               break;
         end
      end   
   end

   //Iterate over xactor instances
   begin
      xvc_xactor xvc;
      xvc_action action;

      this.for_reset(inst);
      xvc = this.for_each();
      if (xvc == null) begin
         `vmm_error(this.log, 
                    $psprintf("%s, line %0d: No such XVC %s",
                              this.testfile, 
                              this.linec,
                              inst)
                   );
         return 1;
      end
      // Actions can only apply to one XVC
      if (this.for_each() != null) begin
         `vmm_error(this.log, 
                    $psprintf("%s, line %0d: Action matches multiple XVCs %s",
                              this.testfile, 
                              this.linec,
                              inst)
                   );
         return 1;
      end

      //There must be a current scenario for an action/interrupt
      if (this.current_sc == null) begin
         `vmm_error(this.log, 
                    $psprintf("%s, line %0d: Action not preceded by scenario",
                              this.testfile, 
                              this.linec)
                   );
         return 1;
      end

      //Split up string , remove white spaces
      // and pass it as a argv array to the xvc.parse()
      begin
         string action_str_args[];
         this.split(action_str, action_str_args);
         action = xvc.parse(action_str_args);
         if (action == null) return 1;
      end

      //create the action and put it in the Q. 
      begin
         vmm_xvc_action_block act_b = new;
         act_b.descr = action_str;
         act_b.xvc_mgr = this;
         act_b.action = action; 
         act_b.xvc = xvc;
         act_b.sc  = this.current_sc;
         act_b.set_wait(wait_for_ev);
         act_b.set_emit(emit_ev_list);
         this.current_sc.actionQ.push_back(act_b);
      end
   
`ifdef VMM_DETAILED_MSGS
      if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::DEBUG_SEV )) begin
         void'(this.log.text(
                 $psprintf("%s, line %0d: Adding action %s to scenario %s...",
                           this.testfile, 
                           this.linec, 
                           action_str,
                           this.current_sc.name)));
         this.log.end_msg();
      end
`endif
   end

endfunction: try_action 



//
// Check if this is a INTERRUPT command.
// Returns 1 if it is, 0 otherwise.
//
function bit vmm_xvc_manager::try_interrupt();

   string inst;
   string action_str;
   string wait_for_ev;
   string emit_ev_list[$];
   bit is_oneshot;
   int arg_no;
   
   if (this.argv[0].tolower() != "interrupt") begin
      return 0;
   end
   try_interrupt = 1;
   //put out any messages caught in the parser
   if (this.errMsg.len() > 0) begin
      `vmm_fatal(this.log, this.errMsg);
      return 1;
   end 

   //parse cmd and extract information.
   //syntax is of the form:
   //  I[NTERRUPT] [ONESHOT] <instance> <action> \
   //    [W[AIT] wait_for] \ 
   //    [E[VENT] event [event]]
   arg_no = 1;
   if (this.argv[arg_no].tolower() == "oneshot") begin
      is_oneshot = 1;
      arg_no++;
   end else begin
      is_oneshot = 0;
   end
   inst       = this.argv[arg_no++];
   action_str = this.argv[arg_no++]; 
   while (1) begin
      string tmpstr;
      //if there are args still left over..
      if (arg_no >= this.argv.size()) 
         break;
      tmpstr = this.argv[arg_no].tolower;
      if(`vmm_str_match(tmpstr, "^(w|wait)")) begin
         arg_no++;
         //ToDo: error if no wait argument
         wait_for_ev = this.argv[arg_no++];
         continue;
      end
      tmpstr = this.argv[arg_no].tolower;
      if (`vmm_str_match(tmpstr, "^(e|event)")) begin
         arg_no++;
         //ToDo: error if dont have atleast 1 arg
         while (`vmm_str_match(this.argv[arg_no], "^[0-9.]*$")) begin
            emit_ev_list.push_back(this.argv[arg_no]);
            arg_no++;
            if (arg_no >= this.argv.size()) 
               break;
         end
      end   
   end

   //Iterate over xactor instances
   begin
      xvc_xactor xvc;
      xvc_action action;

      this.for_reset(inst);
      xvc = this.for_each();
      if (xvc == null) begin
         `vmm_error(this.log, 
                    $psprintf("%s, line %0d: No such XVC %s",
                              this.testfile, 
                              this.linec,
                              inst)
                   );
         return 1;
      end
      // Actions can only apply to one XVC
      if (this.for_each() != null) begin
         `vmm_error(this.log, 
                    $psprintf("%s, line %0d: Action matches multiple XVCs %s",
                              this.testfile, 
                              this.linec,
                              inst)
                   );
         return 1;
      end
      //There must be a current scenario for an action/interrupt
      if (this.current_sc == null) begin
         `vmm_error(this.log, 
                    $psprintf("%s, line %0d: Action not preceded by scenario",
                              this.testfile, 
                              this.linec)
                   );
         return 1;
      end

      //Split up string , remove extra white spaces
      // and pass it as a argv array to the xvc.parse()
      begin
         string action_str_args[];
         this.split(action_str, action_str_args);
         action = xvc.parse(action_str_args);
         if (action == null) return 1;
      end

      //create the action and put it in the Q. 
      begin
         vmm_xvc_action_block act_b = new;
         act_b.xvc_mgr = this;
         act_b.descr = action_str;
         act_b.action = action; 
         act_b.xvc = xvc;
         act_b.sc  = this.current_sc;
         act_b.is_interrupt = 1;
         act_b.is_interrupt_oneshot = is_oneshot; 
         act_b.set_wait(wait_for_ev);
         act_b.set_emit(emit_ev_list);
         this.current_sc.actionQ.push_back(act_b);
      end

`ifdef VMM_DETAILED_MSGS
      if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::DEBUG_SEV )) begin
         void'(this.log.text(
                 $psprintf("%s, line %0d: Adding interrupt action %s to scenario %s...",
                           this.testfile, 
                           this.linec, 
                           action_str,
                           this.current_sc.name)));
         this.log.end_msg();
      end
`endif
        
   end

endfunction: try_interrupt 


//
// Check if this is a EXECUTE command.
// Returns 1 if it is, 0 otherwise.
//
function bit vmm_xvc_manager::try_execute();
   
   if (this.argv[0].tolower() != "execute") begin
      return 0;
   end
   try_execute = 1;
   //put out any messages caught in the parser
   if (this.errMsg.len() > 0) begin
      `vmm_fatal(this.log, this.errMsg);
      return 1;
   end 

   // Terminate any scenario being defined
   if (this.current_sc != null) begin
      this.save_scenario(this.current_sc);
      this.current_sc = null;
   end

   //Put each of the scenario arguments in the list 
   //   of scenarios to be executed.
   begin
      vmm_xvc_scenario scenario;
      for (int i = 1; i < this.argv.size(); i++) begin
         //check if its in the defined scenario q
         scenario = this.lookup_scenario(this.argv[i]);
         if (scenario == null) begin
            `vmm_error(this.log, 
                       $psprintf("%s, line %0d: Scenario %s has not been defined !",
                                 this.testfile, 
                                 this.linec, 
                                 this.argv[i])
                      );
             continue;
         end
         this.exec_scenarios.push_back(scenario);
      end
   end

endfunction: try_execute 


function void vmm_xvc_manager::save_scenario(vmm_xvc_scenario sc);

   //Scenario has to be unique, else its an error.
   `foreach (this.scenarios,i) begin
      if (this.scenarios[i].name == sc.name) begin
         `vmm_error(this.log, 
                    $psprintf("Scenario %s started at %s, line %0d already exists !",
                              this.current_sc.name,
                              this.current_sc.testfile, 
                              this.current_sc.linec)
                   );
         break;
      end
   end

   if(sc == null) begin
     `vmm_error(this.log,"Trying to save null reference to scenarios");
     return;
   end
   this.scenarios.push_back(sc);
endfunction: save_scenario


// Actually perform the "EXECUTE" commands, in order
task vmm_xvc_manager::execute();

   //Initialize all event monitors in scenario space 
   `foreach (this.exec_scenarios,i) begin
      int index;
      for (int j = this.exec_scenarios[i].events.first(index);
           j != 0;
           j = this.exec_scenarios[i].events.next(index))
         this.exec_scenarios[i].events[index].init();
   end

   //Initialize and schedule all the global events
   // i.,e watching for other event occurences.
   //also start the stoponevent watchers 
   begin
      int index;
      for (int i = this.events.first(index);
           i != 0;
           i = this.events.next(index)) begin
         this.events[index].init();
         this.events[index].start();
      end
   end

   //initialize the 'stop-on-event' watch
   this.start_stop_on( this.current_sc ); //ref vmm_xvc_scenario argument


   fork
      begin
        //Execute scenarios
         `foreach (this.exec_scenarios,i) begin
            this.current_sc = this.exec_scenarios[i];
            this.execute_scenario(current_sc);
         end

         //Terminate Stopwatch on all events
         this.terminate_stop_on();

         //Terminate Global events
         begin
            int index;
            for (int i = this.events.first(index);
                 i != 0;
                 i = this.events.next(index)) begin
               this.events[index].kill();
            end
         end
         disable execute;
      end
   join_none

   // Handle forced termination
   @(this.terminate_ex);
   disable execute;

endtask: execute


//
// Execute an entire scenario, returning when the entire scenario
// has been executed
//
task vmm_xvc_manager::execute_scenario(vmm_xvc_scenario sc);
   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text($psprintf("Executing scenario %s started at %s, line %0d...",
                     sc.name, 
                     sc.testfile, 
                     sc.linec)));
      this.log.end_msg();
   end

   sc.notify.indicate(vmm_xvc_scenario::STARTED);

   // Schedule scenario-level events
   // Also start stoponevent watches on scenario events
   begin
      int index;
      for (int i = sc.events.first(index);
           i != 0;
           i = sc.events.next(index)) begin
         sc.events[index].start();
      end
   end

   // First, schedule all interrupt actions
   `foreach (sc.actionQ,i) begin
      xvc_action act;
      xvc_xactor xvc;
      vmm_xvc_action_block act_b = sc.actionQ[i];
      if (!act_b.is_interrupt) continue;
      act = act_b.action;
      xvc = act_b.xvc;

      if (act_b.wait_id < 0) begin
         // Execute interrupt action immediately
`ifdef VMM_DETAILED_MSGS
         if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::DEBUG_SEV )) begin
            void'(this.log.text(
                    $psprintf("Requesting interrupt action %s on XVC %s(%s)...",
                              act.get_name(), 
                              xvc.get_name(), 
                              xvc.get_instance())));
            this.log.end_msg();
         end
`endif
         xvc.interrupt_chan.sneak(act);

         //Emit events
         act_b.emit();

         continue;
      end

      // Schedule the interrupt action when the trigger occurs
      fork
         begin
            fork
               begin
                  while (1) begin
                     //wait for the "waited_on event" to occur
                     act_b.wait_for();
                     // Execute interrupt action immediately
`ifdef VMM_DETAILED_MSGS
                     if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::DEBUG_SEV )) begin
			void'(this.log.text( $psprintf("Requesting interrupt action %s on XVC %s(%s)...",
						       act.get_name(), 
						       xvc.get_name(), 
						       xvc.get_instance())));
                        this.log.end_msg();
		     end
`endif
                     xvc.interrupt_chan.sneak(act);

                     //Emit events
                     act_b.emit();

                     //if a one-shot event, done
                     if (act_b.is_interrupt_oneshot)
                        break; 
                  end //while (1)
               end
               begin
                  //terminate interrupts at the end of the scenario
                  sc.notify.wait_for(vmm_xvc_scenario::DONE);
               end
            join_any
            disable fork;
         end
      join_none
      
   end //foreach

   begin
      // Dispatch regular actions to each XVC, as fast as possible
      `foreach (this.xvcQ,i) begin
         automatic int j = i;
         fork
            this.execute_actions(sc, this.xvcQ[j]);
         join_none
      end
      // Wait until the all actions are completed
      wait fork;
   end

   // Unschedule scenario-level events
   begin
      int index;
      for (int i = sc.events.first(index);
           i != 0;
           i = sc.events.next(index)) begin
         sc.events[index].kill();
      end
   end


   // Unschedule interrupt actions:
   // Automatically done by the interrupt threads..
   // on seeing DONE notification

   sc.notify.indicate(vmm_xvc_scenario::DONE);

endtask: execute_scenario


task vmm_xvc_manager::execute_actions(vmm_xvc_scenario sc,
                                      xvc_xactor   xvc);
   xvc_action act;
   vmm_xvc_action_block act_b;

   `foreach (sc.actionQ,i) begin

      act_b = sc.actionQ[i];
      if ((act_b.is_interrupt) || //skip interrupts
          (act_b.xvc != xvc))     // This action is not for me
         continue; // This action is not for me
      act = act_b.action;

`ifdef VMM_DETAILED_MSGS
      if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::DEBUG_SEV )) begin
         void'(this.log.text( $psprintf("Executing action '%s' on XVC %s(%s)...",
                                        act_b.descr, 
                                        xvc.get_name(), 
                                        xvc.get_instance())));
         this.log.end_msg();
      end
`endif

      //wait for the specified event to occur
      act_b.wait_for();
      xvc.action_chan.put(act);
      //emit the appropriate events when the action completes
      act_b.emit();

`ifdef VMM_DETAILED_MSGS
      if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::DEBUG_SEV )) begin
         void'(this.log.text($psprintf("Completed action '%s' on XVC %s(%s)...",
                                       act_b.descr, 
                                       xvc.get_name(), 
                                       xvc.get_instance())));
         this.log.end_msg();
      end
`endif
   end
endtask: execute_actions




//emit local notifications in the xactor when action is DONE
task vmm_xvc_action_block::emit();
   if (emitQ.size() == 0)
       return;
   fork
      begin
         this.action.notify.wait_for(xvc_action::ENDED); 
         foreach (emitQ[i]) begin
            this.xvc.notify.indicate(emitQ[i]);
         end
      end
   join_none
endtask: emit


//wait for event wait to occur
task vmm_xvc_action_block::wait_for();
   if (wait_id < 0)
       return;
   fork
      begin
      if (this.sc.events.exists(this.wait_id)) begin
         //check the scenario events to see if the wait exists
         sc.notify.wait_for(this.wait_id);
      end else if (this.xvc_mgr.events.exists(this.wait_id)) begin
         //else, check the global events
         xvc_mgr.notify.wait_for(this.wait_id);
      end else
         //if its in none of the above, its a warning as
         //  an undeclared event is being waited on.
         `vmm_error(this.sc.log,
                    $psprintf("Event %0d waited on in action %s(scenario %s) does not exist in either scenario or global space",
                              this.wait_id,
                              this.action.get_name(),
                              this.sc.name)
                   );
       end
       begin
          @(this.terminate_ev);
       end
    join_any
    disable fork;
          
endtask: wait_for


function void vmm_xvc_action_block::kill();
   ->this.terminate_ev;
endfunction: kill


//create the list of local emitted events in the xvc
//  from the parsed input string obtained from the
//  action or interrupt command
function void vmm_xvc_action_block::set_emit(ref string emit_ids[$]);

`ifdef VCS2006_06
   // Work-around for NYI feature in VCS2006.06
   // but IEEE 1800-2009 compliant
   this.emitQ.delete();
`else
`ifdef INCA
   this.emitQ.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.emitQ = '{};
`endif
`endif

   if (emit_ids.size() == 0) return;

   //emit event may already be configured i.,e exist in the
   //    list of known xactor local events.
   //if it does not, configure a new notification and
   //  add to the xvc
   foreach (emit_ids[i]) begin 
      int emit_id = emit_ids[i].atoi();
      `foreach (this.emitQ,j) begin
         if (emit_id == this.emitQ[j]) continue;
      end
      if (!this.xvc.notify.is_configured(emit_id))
         void'(this.xvc.notify.configure(emit_id)); 

      //Add to the emitQ of this action Block
      this.emitQ.push_back(emit_id); 
   end
endfunction: set_emit


//Set the id of the waiting event
function void vmm_xvc_action_block::set_wait(string wait_str);
   if (wait_str == "") 
      this.wait_id = -1;
   else
      this.wait_id = wait_str.atoi();
endfunction: set_wait

    


function vmm_xvc_stop_on_event::new(int    count,
                                    int    immediate,
                                    string fname,
                                    int    linec);
   this.count = count;
   this.immediate = immediate;
   this.fname = fname;
   this.linec = linec;
endfunction: new


function vmm_xvc_scenario vmm_xvc_manager::lookup_scenario(string name);
   lookup_scenario = null;
   `foreach(this.scenarios,i) begin
      if (this.scenarios[i].name == name) begin
         lookup_scenario = this.scenarios[i];
         break;
      end
   end
endfunction: lookup_scenario


task vmm_xvc_manager::add_stop_on(string ev_fullname, 
                                  int    count, 
                                  int    immediate,
                                  string fname, 
                                  int    linec);
   //if it already exists, it is overridden
   this.stop_on[ev_fullname] = new(count,
                                   immediate,
                                   fname,
                                   linec); 
endtask: add_stop_on


//
// Terminate all watching threads
//
function void vmm_xvc_manager::terminate_stop_on();
   ->this.terminate_ev;
endfunction: terminate_stop_on


//
// Return an vmm_xvc_event, given the string representing the event
// The string is of the form gev or <sid>.<sev>
//
function vmm_xvc_event vmm_xvc_manager::get_stop_on_event(string ev_str);
   string tmpstr;
   int ev_id;

   get_stop_on_event = null;

   if (`vmm_str_match(ev_str, "[.]")) begin
      //if matches <sid.sev>: get sid and sev
      string event_info[2];
      vmm_xvc_scenario scn;
      event_info[0] = `vmm_str_prematch(ev_str);
      event_info[1] = `vmm_str_postmatch(ev_str);

      //lookup scenario event_info[0]
      scn = this.lookup_scenario(event_info[0]);

      //fatal if scn is null, continue
      if (scn == null) begin
         `vmm_fatal(this.log,
                    $psprintf("Stoponevent: Scenario %s does not exist",
                              event_info[0])
                    );
      end else begin
         //Get a handle to the sid.sev event
         ev_id = event_info[1].atoi();
         if (!scn.events.exists(ev_id)) begin
            `vmm_fatal(this.log,
                       $psprintf("Stoponevent: Scenario %s does not have any event %0d",
                                 event_info[0],
                                 ev_id
                                 )
                       );
         end else begin
            return scn.events[ev_id];
         end
      end
   end else begin
      //else get gev
      ev_id = ev_str.atoi();
      if (!this.events.exists(ev_id)) begin
         `vmm_fatal(this.log,
                    $psprintf("Stoponevent: Xvc_manager does not have any event %0d",
                              ev_id
                              )
                    );
      end else begin
         return this.events[ev_id];
      end
   end
endfunction: get_stop_on_event


function void vmm_xvc_manager::start_stop_on(ref vmm_xvc_scenario current_sc);
   //for each event in the list of watched events,
   //start a thread which waits for the event to
   //be notified, with the appropriate no. of occurences

   //if the stopwatch associated with the event has the
   //  immediate attribute, it is stopped immediately,
   //  else it waits until the current scenario is complete

   string index;
   vmm_xvc_stop_on_event stop;
   vmm_xvc_event xvc_ev;
   
   for (int i = this.stop_on.first(index); i != 0; i = this.stop_on.next(index)) begin
     	
      stop = this.stop_on[index];
      xvc_ev = this.get_stop_on_event(index);

      fork
     	 begin
     	    fork
     	       begin
     		  automatic int    count = stop.count;
     		  automatic string local_index = index;

     		  //wait for counter to expire
     		  while (count--) begin
     		     xvc_ev.wait_for();
     		  end

     		  //if graceful termination, wait for DONE  
     		  if (!stop.immediate) begin
     		     if (current_sc != null) begin
     			current_sc.notify.wait_for(vmm_xvc_scenario::DONE);
                     end
     		  end
                  // Signal the manager to terminate execution
                  -> this.terminate_ex;
               end  
               begin
     	          @(this.terminate_ev);
     	       end
           join_any
     	   disable fork;
     	end
      join_none 
   end
endfunction: start_stop_on
