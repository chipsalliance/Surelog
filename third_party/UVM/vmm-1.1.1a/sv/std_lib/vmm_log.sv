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


`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
class vmm_log_modifier;
   int       typ;
   int       severity;
   string    pattern;
   int       new_typ;
   int       new_severity;
   int       handling;

   static local vmm_log log;

   function new();
      // Initialize all static properties
      if (log == null) this.log = new("vmm_log_modifier", "class");
   endfunction: new
   
   extern function string psdisplay(string prefix = "");
endclass: vmm_log_modifier
     

typedef class vmm_log_msg;

`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
class vmm_log_watchpoint;
   int       typ;
   int       severity;
   string    pattern;
   logic     issued;

   event       seen;
   vmm_log_msg msg;

   static local vmm_log log;
   
   function new();
      // Initialize all static properties
      if (log == null) this.log = new("vmm_log_watchpoint", "class");
   endfunction: new

   extern function void   display(string prefix = "");
   extern function string psdisplay(string prefix = "");
endclass:vmm_log_watchpoint


`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
class vmm_log_msg;
   vmm_log    log;

   bit        invalid;   
   time       timestamp;
   int        original_typ;
   int        original_severity;
   int        effective_typ;
   int        effective_severity;
   string     fname;
   int        line;
   string     text[$];
   logic      issued;
   int        handling;

   /*local*/ int flushed;

   function new(vmm_log log);
      this.log     = log;
      this.invalid = 1;
   endfunction: new

   extern function void   display(string prefix = "");
   extern function string psdisplay(string prefix = "");
   extern function vmm_log_msg copy();
endclass: vmm_log_msg


`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
class vmm_log_catcher_descr;
    vmm_log_catcher catcher;

    string text;
    string name;
    string inst;
    int typs;
    int severity;
    bit recurse;
endclass: vmm_log_catcher_descr
   

   //
   // vmm_log_modifier
   //

function string vmm_log_modifier::psdisplay(string prefix="");
   $sformat(psdisplay, "%s%s [%s] with \"%s\" -> %s [%s] then %s",
          prefix, this.log.typ_image(this.typ),
          this.log.sev_image(this.severity),
          (this.pattern == "") ? "/./" : this.pattern,
          this.log.typ_image(this.new_typ),
          this.log.sev_image(this.new_severity),
          this.log.handling_image(this.handling));
endfunction: psdisplay


  //
  // vmm_log_watchpoint
  //

function void vmm_log_watchpoint::display(string prefix="");
   $write("%s\n", this.psdisplay(prefix));
endfunction: display
   
function string vmm_log_watchpoint::psdisplay(string prefix="");
   $sformat(psdisplay, "%s%s [%s] with \"%s\"%s",
            prefix, this.log.typ_image(this.typ),
            this.log.sev_image(this.severity),
            (this.pattern == "") ? "/./" : this.pattern,
            (this.issued === 1'bx) ? "" : (this.issued) ? "if issued" : "if not issued");
endfunction: psdisplay


  //
  // vmm_log_msg
  //
  
function void   vmm_log_msg::display(string prefix="");
   $write("%s\n", this.psdisplay(prefix));
endfunction: display

function string vmm_log_msg::psdisplay(string prefix="");
   $sformat(psdisplay, "%s%s [%s] at %0t", prefix,
            this.log.typ_image(this.effective_typ),
            this.log.sev_image(this.effective_severity),
            this.timestamp);
   `foreach(this.text,i) begin
      $sformat(psdisplay, "%s\n%s    %s", psdisplay, prefix,
               this.text[i]);
   end
endfunction: psdisplay

function vmm_log_msg vmm_log_msg::copy();
   copy = new(this.log);

   copy.timestamp          = this.timestamp;
   copy.original_typ       = this.original_typ;
   copy.original_severity  = this.original_severity;
   copy.effective_typ      = this.effective_typ;
   copy.effective_severity = this.effective_severity;
   copy.text               = this.text;
   copy.issued             = this.issued;
   copy.handling           = this.handling;

   copy.flushed = this.flushed;
endfunction: copy


  //
  // vmm_log;
  //

function bit vmm_log::uses_hier_inst_name();
   return !this.is_orig;
endfunction: uses_hier_inst_name


function void vmm_log::use_hier_inst_name();
   this.recurse_id++;
   `foreach (this.known,i) begin
      if (this.known[i].parent_count == 0) this.make_hier_inst_name();
   end
   this.is_orig = 0;
endfunction: use_hier_inst_name


function void vmm_log::use_orig_inst_name();
   `foreach (this.known,i) begin
      this.known[i].inst = this.known[i].orig_inst;
   end
   this.is_orig = 1;
endfunction: use_orig_inst_name


function void vmm_log::make_hier_inst_name(string prefix = "");
   string name;

   // Detect cycles in log trees
   if (this.visited == this.recurse_id) return;
   this.visited = this.recurse_id;

   name = this.orig_inst;
   // In case no instance names were specified...
   if (name == "") name = this.name;
   if (name == "") name = "[Anonymous]";
   if (prefix == "") prefix = name;
   else begin
      this.inst = {prefix, name};
      prefix = this.inst;
   end
   prefix = {prefix, "."};

   `foreach (this.below,i) begin
      this.below[i].make_hier_inst_name(prefix);
   end
endfunction: make_hier_inst_name


function void vmm_log::reset(string name="/./",
                             string inst="/./",
                             bit    recurse=0);
   this.is_self = 0;
   this.is_all  = 0;

   this.known_idx = 0;
   this.recurse = recurse;
   this.recurse_id++;
`ifdef VCS2006_06
   // Work-around for NYI feature in 2006.06
   // but IEEE 1800-2009 compliant
   this.recurse_stack.delete();
`else
`ifdef INCA
   this.recurse_stack.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.recurse_stack = '{};
`endif
`endif

   // Trivial iterators?
   if (name == "" && inst == "") begin
      this.is_self = 1;
      return;
   end
   if (name == "/./" && inst == "/./") begin
      this.is_all = 1;
      this.recurse = 0; // No point in recursion
      return;
   end
   
   if (name == "") name = this.name;
   if (inst == "") inst = this.inst;
 
   this.pattern[0] = name;
   this.is_pattern[0] = `vmm_str_match(this.pattern[0], "^/(.*)/$");
   if (is_pattern[0]) begin
      this.pattern[0] = `vmm_str_backref(this.pattern[0], 0);
   end

   this.pattern[1] = inst;
   this.is_pattern[1] = `vmm_str_match(this.pattern[1], "^/(.*)/$");
   if (is_pattern[1]) begin
      this.pattern[1] = `vmm_str_backref(this.pattern[1], 0);
   end
endfunction: reset
   

`ifdef VCS
(* vmm_private_class, _vcs_vmm_class = 1 *)
`endif
class vmm_log_below_iter;
   local vmm_log log;
   local int idx;

   function new(vmm_log log);
      this.log = log;
      this.idx = 0;
   endfunction

   function vmm_log data();
      if (this.idx >= this.log.below.size()) data = null;
      else data = this.log.below[idx];
   endfunction

   function vmm_log start();
      this.idx = 0;
      start = this.data();
   endfunction

   function vmm_log next();
      if (idx < this.log.below.size()) idx++;
      next = this.data();
   endfunction
endclass


function vmm_log vmm_log::for_each();
   if (this.is_self) begin
      if (this.is_self == 1) begin
         this.is_self = 2;
         if (this.recurse) begin
            vmm_log_below_iter j = new(this);
            this.visited = this.recurse_id;
            this.recurse_stack.push_back(j);
         end
         return this;
      end else if (!this.recurse) begin
         return null;
      end
   end

   while (this.recurse && this.recurse_stack.size() > 0) begin
      vmm_log_below_iter i = recurse_stack[$];

      while (i.data() != null) begin
         vmm_log that = i.data();
         void'(i.next());
         if (that.visited != this.recurse_id) begin
            vmm_log_below_iter j = new(that);
            that.visited = this.recurse_id;
            this.recurse_stack.push_back(j);
            return that;
         end
      end
      void'(this.recurse_stack.pop_back());
   end

   if (this.is_self) begin
      return null;
   end

   while (this.known_idx < this.known.size()) begin
      vmm_log that = this.known[this.known_idx++];
      bit name_ok;
      bit inst_ok;

      if (this.is_all) begin
         return that;
      end

      if (is_pattern[0]) name_ok = `vmm_str_match(that.name, this.pattern[0]);
      else               name_ok = (that.name == this.pattern[0]);

      if (is_pattern[1]) inst_ok = `vmm_str_match(that.inst, this.pattern[1]);
      else               inst_ok = (that.inst == this.pattern[1]);

      if (name_ok && inst_ok) begin
         if (that.visited != this.recurse_id) begin
            that.visited = this.recurse_id;
            if (this.recurse) begin
               vmm_log_below_iter j = new(that);
               this.recurse_stack.push_back(j);
            end
            return that;
         end
      end
   end
   for_each = null;
endfunction: for_each

   
function vmm_log::new(string  name,
                      string  inst,
                      vmm_log under=null);
`ifdef VMM_LOG_BASE_NEW_CALL
   super.new(`VMM_LOG_BASE_NEW_CALL);
`endif

   if (_vmm_opts == null) _vmm_opts = new;

   this.name = name;
   this.inst = inst;
   this.orig_inst = inst;
   this.parent_count = 0;
   if (under != null) under.is_above(this);

   this.msg   = new(this);

   this.n_msg[FATAL_SEV]   = 0;
   this.n_msg[ERROR_SEV]   = 0;
   this.n_msg[WARNING_SEV] = 0;
   this.n_msg[NORMAL_SEV] = 0;
   this.n_msg[TRACE_SEV] = 0;
   this.n_msg[DEBUG_SEV] = 0;
   this.n_msg[VERBOSE_SEV] = 0;
   this.n_msg[HIDDEN_SEV] = 0;
   this.n_msg[IGNORE_SEV] = 0;

   this.has_text_modifiers = 0;
   this.n_demoted[ERROR_SEV] = 0;
   this.n_demoted[WARNING_SEV] = 0;

   this.known.push_back(this);

   this.enabled_typs = ALL_TYPS;

   if (this.known.size() == 1) begin
      this.type_list.push_back(FAILURE_TYP);
      this.type_list.push_back(NOTE_TYP);
      this.type_list.push_back(DEBUG_TYP);
      this.type_list.push_back(REPORT_TYP);
      this.type_list.push_back(NOTIFY_TYP);
      this.type_list.push_back(TIMING_TYP);
      this.type_list.push_back(XHANDLING_TYP);
      this.type_list.push_back(PROTOCOL_TYP);
      this.type_list.push_back(TRANSACTION_TYP);
      this.type_list.push_back(COMMAND_TYP);
      this.type_list.push_back(CYCLE_TYP);
      this.type_list.push_back(USER_TYP_0);
      this.type_list.push_back(USER_TYP_1);
      this.type_list.push_back(USER_TYP_2);
      this.type_list.push_back(INTERNAL_TYP);

      this.sev_list.push_back(FATAL_SEV);
      this.sev_list.push_back(ERROR_SEV);
      this.sev_list.push_back(WARNING_SEV);
      this.sev_list.push_back(NORMAL_SEV);
      this.sev_list.push_back(TRACE_SEV);
      this.sev_list.push_back(DEBUG_SEV);
      this.sev_list.push_back(VERBOSE_SEV);

      // Define default images
      this.type_images[FAILURE_TYP    ] = "FAILURE";
      this.type_images[NOTE_TYP       ] = "NOTE";
      this.type_images[DEBUG_TYP      ] = "DEBUG";
      this.type_images[REPORT_TYP     ] = "REPORT";
      this.type_images[NOTIFY_TYP     ] = "NOTIFY";
      this.type_images[TIMING_TYP     ] = "TIMING";
      this.type_images[XHANDLING_TYP  ] = "XHANDLING";
      this.type_images[PROTOCOL_TYP   ] = "PROTOCOL";
      this.type_images[TRANSACTION_TYP] = "XACTION";
      this.type_images[COMMAND_TYP    ] = "COMMAND";
      this.type_images[CYCLE_TYP      ] = "CYCLE";
      this.type_images[USER_TYP_0     ] = "USER_0";
      this.type_images[USER_TYP_1     ] = "USER_1";
      this.type_images[USER_TYP_2     ] = "USER_2";
      this.type_images[INTERNAL_TYP   ] = "INTERNAL";

`ifdef VMM_LOG_ANSI_COLOR
      this.sev_images[FATAL_SEV  ] = "\033[41m*FATAL*\033[0m";
      this.sev_images[ERROR_SEV  ] = "\033[31m!ERROR!\033[0m";
      this.sev_images[WARNING_SEV] = "\033[33mWARNING\033[0m";
`else
      this.sev_images[FATAL_SEV  ] = "*FATAL*";
      this.sev_images[ERROR_SEV  ] = "!ERROR!";
      this.sev_images[WARNING_SEV] = "WARNING";
`endif
      this.sev_images[NORMAL_SEV ] = "Normal";
      this.sev_images[TRACE_SEV  ] = "Trace";
      this.sev_images[DEBUG_SEV  ] = "Debug";
      this.sev_images[VERBOSE_SEV] = "Verbose";


      // Process command-line options
      if ($test$plusargs("rvm_log_debug")) begin
         this.plus_debug = 1;
      end
      // Cache those options here so they'll show up in the help
      void'(_vmm_opts.get_bit("log_nowarn_at_200", "Supress warning message for more than 200 vmm_log instances creation"));
      void'(_vmm_opts.get_bit("log_nofatal_at_1000", "Supress fatal message for more than 1000 vmm_log instances creation"));

      begin
         bit    plusarg;
         string arg;
         string level;

         plusarg = $value$plusargs("rvm_log_default=%s", arg);
         if (!plusarg) begin
            arg = _vmm_opts.get_string("log_default", , "Sets the default message verbosity");
            if (arg != "") plusarg = 1;
         end
         if (plusarg) begin
            level = arg.substr(0, 1); // Only look at the 1st 2 chars

            level = level.tolower();
            if (level == "er")
               this.dflt_lvl = ERROR_SEV;
            else if (level == "wa")
               this.dflt_lvl = WARNING_SEV;
            else if (level == "no")
               this.dflt_lvl = NORMAL_SEV;
            else if (level == "tr")
               this.dflt_lvl = TRACE_SEV;
            else if (level == "de")
               this.dflt_lvl = DEBUG_SEV;
            else if (level == "ve")
               this.dflt_lvl = VERBOSE_SEV;
            else if (level == "hi")
               this.dflt_lvl = HIDDEN_SEV;
            else
               $write("Warning: Invalid +vmm_log_default specification: \"%s\"\n",
                      arg);
         end
         // Sometimes, VCS screws up static initialization order
         else this.dflt_lvl = NORMAL_SEV;

         plusarg = $value$plusargs("rvm_force_verbosity=%s", arg);
         if (!plusarg) begin
            arg = _vmm_opts.get_string("force_verbosity", , "Overrides the message verbosity level with the specified one");
            if (arg != "") plusarg = 1;
         end
         if (plusarg) begin
            level = arg.substr(0, 1); // Only look at the 1st 2 chars

            level = level.tolower();
            if (level == "er")
              this.force_lvl = ERROR_SEV;
            else if (level == "wa")
              this.force_lvl = WARNING_SEV;
            else if (level == "no")
              this.force_lvl = NORMAL_SEV;
            else if (level == "tr")
              this.force_lvl = TRACE_SEV;
            else if (level == "de")
              this.force_lvl = DEBUG_SEV;
            else if (level == "ve")
              this.force_lvl = VERBOSE_SEV;
            else if (level == "hi")
              this.force_lvl = HIDDEN_SEV;
            else
              $write("Warning: Invalid +vmm_force_verbosity level: \"%s\"\n",
                     arg);
         end
      end



   end

   this.log_lvl = this.dflt_lvl;
   this.log_start(STDOUT);

   //
   // Catch a common usage error
   ///
   if (this.known.size() == 200) begin
      if (!_vmm_opts.get_bit("log_nowarn_at_200") &&
          !$test$plusargs("rvm_log_nowarn_at_200")) begin
      `ifdef VMM_LOG_FORMAT_FILE_LINE
         if (this.start_msg(FAILURE_TYP, WARNING_SEV, `__FILE__, `__LINE__)) begin
      `else
         if (this.start_msg(FAILURE_TYP, WARNING_SEV)) begin
      `endif
            void'(this.text("Over 200 vmm_log instances have been created."));
            void'(this.text("Check that all vmm_data extensions use a static instance"));
            void'(this.text("or use +vmm_log_nowarn_at_200 to disable this warning."));
            this.end_msg();
         end
      end
   end
      
   if (this.known.size() == 1000) begin
      if (!_vmm_opts.get_bit("log_nofatal_at_1000") &&
          !$test$plusargs("rvm_log_nofatal_at_1000")) begin
      `ifdef VMM_LOG_FORMAT_FILE_LINE          
         if (this.start_msg(FAILURE_TYP, FATAL_SEV, `__FILE__, `__LINE__)) begin
      `else
         if (this.start_msg(FAILURE_TYP, FATAL_SEV)) begin
      `endif
            void'(this.text("Over 1000 vmm_log instances have been created."));
            void'(this.text("Check that all vmm_data extensions use a static instance"));
            void'(this.text("or use +vmm_log_nofatal_at_1000 to disable this failure."));
            this.end_msg();
         end
      end
   end



endfunction: new


function void vmm_log::is_above(vmm_log log);
   if (log == null || log == this) return;
   // Make sure it is added only once
   `foreach (this.below,i) begin
      if (this.below[i] == log) return;
   end
   this.below.push_back(log);
   log.parent_count++;



endfunction: is_above

  
function void vmm_log::is_not_above(vmm_log log);
   if (log == null || log == this) return;
   `foreach (this.below,i) begin
      if (this.below[i] == log) begin
         this.below.delete(i);
         if (log.parent_count > 0) log.parent_count--;



         return;
      end
   end
endfunction: is_not_above


  
function vmm_log vmm_log::copy(vmm_log to = null);
   if (to == null) to = new(this.name, this.inst);
   else begin
      to.name = this.name;
      to.inst = this.inst;
   end

   to.enabled_typs = this.enabled_typs;
   to.log_lvl      = this.log_lvl;
   to.fp           = this.fp;

   copy = to;
endfunction: copy


function void vmm_log::set_name(string name);
   this.name = name;
endfunction: set_name

  
function string vmm_log::get_name();
   get_name = this.name;
endfunction: get_name

  
function void vmm_log::set_instance(string inst);
   this.inst = inst;
endfunction: set_instance
   

function string vmm_log::get_instance();
   get_instance = this.inst;
endfunction: get_instance
   

function void vmm_log::list(string name="/./",
                            string inst="/./",
                            bit    recurse=0);
   this.reset(name, inst, recurse);
   for (vmm_log log = this.for_each(); log != null; log = this.for_each()) begin   
      $write("%s(%s) [%s] F/E/W/e/w=%0d/%0d/%0d/%0d/%0d\n", log.name, log.inst, this.sev_image(log.log_lvl), log.n_msg[FATAL_SEV], log.n_msg[ERROR_SEV], log.n_msg[WARNING_SEV], log.n_demoted[ERROR_SEV], log.n_demoted[WARNING_SEV]);
      for(int i = 0; i < log.below.size(); i++) begin
         $write("  +--- %s(%s)\n", log.below[i].name, log.below[i].inst);
      end
   end
endfunction: list
   

function void vmm_log::display(string prefix="");
   $display("%s", this.psdisplay(prefix));
endfunction


function string vmm_log::psdisplay(string prefix="");
   $sformat(psdisplay, "%s%s(%s) [%s]", prefix, this.name, this.inst,
            this.sev_image(this.log_lvl));
   for (int i = 0; i < this.below.size(); i++) begin
      string name, inst;
      name = this.below[i].name; inst = this.below[i].inst;
      $sformat(psdisplay, "%s\n%s   +--- %s(%s)", psdisplay, prefix,
               name, inst);
   end
   for (int i = 0; i < this.modifier_ids.size(); i++) begin
      $sformat(psdisplay, "%s\n%s", psdisplay, this.modifier_cache[this.modifier_ids[i]].psdisplay({prefix, "   "}));
   end
endfunction


function void vmm_log::kill();
   `foreach(this.known,i) begin
      if (this.known[i] == this) this.known.delete(i);
   end
endfunction: kill


function vmm_log_format vmm_log::set_format(vmm_log_format fmt);
   if (fmt == null) begin
      `vmm_error(this, "Cannot use NULL formatter in vmm_log::set_format(). Unchanged");
      return null;
   end

   set_format = this.fmt;
   this.fmt = fmt;
endfunction: set_format

  
function string vmm_log::set_typ_image(int    typ,
                                       string image);
   if (!this.type_images.exists(typ)) begin
      `vmm_error(this, "Invalid message type specified to vmm_log::set_typ_image()");
      return "";
   end

   set_typ_image = this.type_images[typ];
   this.type_images[typ] = image;



endfunction: set_typ_image
   

function string vmm_log::typ_image(int typ);
   string sep = "";

   if (this.type_images.exists(typ)) begin
      return this.type_images[typ];
   end

   // Special types
   if (typ == DEFAULT) begin
      return "(default)";
   end
   if (typ == UNCHANGED) begin
      return "(unchanged)";
   end

   // Composite type?
   typ_image = "";
   `foreach(this.type_list,i) begin
      if (typ & this.type_list[i]) begin
         typ_image = {typ_image, sep, this.type_images[this.type_list[i]]};
         sep = "/";
      end
   end
   if (typ_image == "") typ_image = "?MSG_TYP?";
endfunction: typ_image
   

function string vmm_log::set_sev_image(int    severity,
                                       string image);
   if (!this.sev_images.exists(severity)) begin
      `vmm_error(this, "Invalid message severity specified to vmm_log::set_sev_image()");
      return "";
   end

   set_sev_image = this.sev_images[severity];
   this.sev_images[severity] = image;



endfunction: set_sev_image

  
function string vmm_log::sev_image(int severity);
   string sep = "";

   if (this.sev_images.exists(severity)) begin
      return this.sev_images[severity];
   end

   // Special severities
   if (severity == DEFAULT) begin
      return "(default)";
   end
   if (severity == UNCHANGED) begin
      return "(unchanged)";
   end
   if (severity == IGNORE_SEV) begin
      return "(ignored)";
   end

   // Composite severity?
   sev_image = "";
   `foreach(this.sev_list,i) begin
      if (severity & this.sev_list[i]) begin
         sev_image = {sev_image, sep, this.sev_images[this.sev_list[i]]};
         sep = "/";
      end
   end
   if (sev_image == "") sev_image = "?SEV_TYP?";
endfunction: sev_image


function string vmm_log::handling_image(int handling);
   case (handling)
      ABORT_SIM        : handling_image = "ABORT";
      COUNT_ERROR      : handling_image = "ERROR";
      STOP_PROMPT      : handling_image = "STOP";
      DEBUGGER         : handling_image = "DEBUGGER";
      DUMP_STACK       : handling_image = "DUMPSTACK";
      CONTINUE         : handling_image = "CONTINUE";
      IGNORE           : handling_image = "IGNORE";
      DEFAULT          : handling_image = "(default)";
      UNCHANGED        : handling_image = "(unchanged)";
      default          : handling_image = "?HANDLING?";
   endcase
endfunction: handling_image

   
function int vmm_log::default_handling(int severity);
   case (severity)
      FATAL_SEV   : default_handling = ABORT_SIM;
      ERROR_SEV   : default_handling = COUNT_ERROR;
      default     : default_handling = CONTINUE;
   endcase
endfunction: default_handling
   

function void vmm_log::report(string name="/./",
                              string inst="/./",
                              bit    recurse=0);
   vmm_log log;
   int    n_fatals = 0;
   int    n_errs   = 0;
   int    n_warns  = 0;
   int    n_derrs  = 0;
   int    n_dwarns = 0;
   string msg;

   this.reset(name, inst, recurse);
   for(log = this.for_each(); log != null; log = this.for_each()) begin

      n_fatals += log.n_msg[FATAL_SEV];
      n_errs   += log.n_msg[ERROR_SEV];
      n_warns  += log.n_msg[WARNING_SEV];
      n_derrs  += log.n_demoted[ERROR_SEV];
      n_dwarns += log.n_demoted[WARNING_SEV];
   end

   msg = this.fmt.pass_or_fail(n_fatals == 0 && n_errs == 0,
                               name, inst, n_fatals, n_errs, n_warns,
                               n_derrs, n_dwarns);
   if (msg != "") $display("%s", msg);
endfunction: report
   

function bit vmm_log::start_msg(int typ,
                                int severity = DEFAULT_SEV
`ifdef VMM_LOG_FORMAT_FILE_LINE
                                , string fname = ""
                                , int    line = -1
`endif
                                );
   if (this.in_catcher) begin
      string msg;
      string txt[$];

      txt.push_back("Cannot issue a new message from vmm_log_catcher::caught()");
      msg = this.fmt.format_msg(this.name, this.inst, 
                                this.typ_image(FAILURE_TYP),
                                this.sev_image(FATAL_SEV),
`ifdef VMM_LOG_FORMAT_FILE_LINE
                                fname, line,
`endif
                                txt);
      $display("%s\n", msg);
      this.n_msg[ERROR_SEV]++;
      this.report(this.name, this.inst, 1);
      $finish;
   end

   if (this.msg != null && !this.msg.invalid && this.msg.issued !== 1'b0) this.end_msg();

   // Provide a default severity if none specified
   if (severity < 0) begin
      case (typ)
         FAILURE_TYP    :  severity = ERROR_SEV;
         NOTE_TYP       :  severity = NORMAL_SEV;
         DEBUG_TYP      :  severity = DEBUG_SEV;
         REPORT_TYP     :  severity = DEBUG_SEV;
         NOTIFY_TYP     :  severity = HIDDEN_SEV;
         TIMING_TYP     :  severity = WARNING_SEV;
         XHANDLING_TYP  :  severity = WARNING_SEV;
         PROTOCOL_TYP   :  severity = DEBUG_SEV;
         TRANSACTION_TYP:  severity = TRACE_SEV;
         COMMAND_TYP    :  severity = TRACE_SEV;
         CYCLE_TYP      :  severity = VERBOSE_SEV;
         default        :  severity = NORMAL_SEV;
      endcase
   end

   // Perform a quick, less expensive filtering here for loggers without
   // promotion/demotion or watchpoints.  Return immediately if the
   // message is not printed based on severity and enabled categories
   if (this.modifier_ids.size() == 0 &&
       this.watchpoint_ids.size() == 0) begin

      if ((this.force_lvl != DEFAULT_SEV && severity > this.force_lvl) || // Forced?
          (this.force_lvl == DEFAULT_SEV && severity > this.log_lvl) ||   // Above?
          (!(typ & this.enabled_typs) && (severity >= WARNING_SEV)) // Disabled?
          ) begin
         this.msg.invalid = 1;
         return 0;
      end
   end

   this.msg.invalid = 0;
   this.msg.original_typ = typ;
   this.msg.original_severity = severity;
   this.msg.effective_typ = typ;
   this.msg.effective_severity = severity;
   
`ifdef VMM_LOG_FORMAT_FILE_LINE
   this.msg.fname = fname;
   this.msg.line = line;
`endif

   this.msg.flushed = 0;
`ifdef VCS2006_06
   // Work-around for NYI feature in 2006.06
   // but IEEE 1800-2009 compliant
   this.msg.text.delete();
`else
`ifdef INCA
   this.msg.text.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.msg.text = '{};
`endif
`endif
   this.msg.handling = DEFAULT;
   this.msg.issued = 1'bx;

   start_msg = 1;

   // Do property-based promotion and filtering
   // if there are no text-based filters
   if (!this.has_text_modifiers) begin
      this.promote();
      this.filter();

      if (this.msg.issued === 1'b0) begin
         start_msg = 0;

         // Record risky demotions
         if (this.msg.effective_severity > this.msg.original_severity) begin
            case (this.msg.original_severity)
               ERROR_SEV  : this.n_demoted[ERROR_SEV]++;
               WARNING_SEV: this.n_demoted[WARNING_SEV]++;
            endcase
         end

         this.msg.invalid = 1;
      end
   end
endfunction: start_msg
   

function bit vmm_log::text(string msg = "");
   if (this.msg.invalid)
   begin
      `vmm_error(this, "Malformed message: vmm_log::text() called before vmm_log::start_msg()");
      return 0;
   end

   text = 1;

   if (msg == "")
   begin
      this.flush_msg();
      return 1;
   end

   this.msg.text.push_back(msg);

endfunction: text
   

function void vmm_log::end_msg();
   int handling;

   if (this.msg.invalid)
   begin
      `vmm_error(this, "Malformed message: vmm_log::end_msg() called before vmm_log::start_msg()");
      return;
   end

   this.flush_msg();




   // If the message was not issued, it does not exists
   if (!this.msg.issued) begin
      this.msg.invalid = 1;
      return;
   end

   handling = this.msg.handling;
   if (handling == DEFAULT) handling = default_handling(this.msg.effective_severity);

   // Avoid recursive handling in callbacks
   if (this.in_callbacks) handling = CONTINUE;

   case (handling)

     ABORT_SIM: begin
        bit finished = 0;
        this.in_callbacks = 1;
        `vmm_callback(vmm_log_callbacks, pre_abort(this));
        `vmm_callback(vmm_log_callbacks, pre_finish(this, finished));
        this.in_callbacks = 0;
        if (!finished) begin
           this.report();
           $finish;
        end
     end

     DUMP_STACK: begin
        this.in_callbacks = 1;
        `vmm_callback(vmm_log_callbacks, pre_debug(this));
        this.in_callbacks = 0;
`ifdef VCS
          $stack;
        `endif
        $stop;
     end

     DEBUGGER: begin
        this.in_callbacks = 1;
        `vmm_callback(vmm_log_callbacks, pre_debug(this));
        this.in_callbacks = 0;
        $stop;
     end

     STOP_PROMPT: begin
        this.in_callbacks = 1;
        `vmm_callback(vmm_log_callbacks, pre_stop(this));
        this.in_callbacks = 0;
        $stop;
     end

     COUNT_ERROR: begin
        this.error_count++;
        if (this.error_limit > 0 && this.error_count >= this.error_limit) begin
           bit finished = 0;
           string msg = this.fmt.abort_on_error(this.error_count,
                                                this.error_limit);
           if (msg != "") $display("%s", msg);
           this.in_callbacks = 1;
           `vmm_callback(vmm_log_callbacks, pre_abort(this));
           `vmm_callback(vmm_log_callbacks, pre_finish(this, finished));
           this.in_callbacks = 0;
           if (!finished) begin
              this.report();
              $finish;
           end
        end                                          
     end
   endcase

   this.msg.invalid = 1;
endfunction: end_msg


function void vmm_log::process_catch(vmm_log_msg msg);
   `foreach (this.catcher_ids,i) begin
      vmm_log_catcher_descr catcher_item;

      catcher_item = this.catcher_cache[this.catcher_ids[i]];
      
      if (!(catcher_item.severity & msg.effective_severity))
	continue;
      
      if (!(catcher_item.typs & msg.effective_typ))
	continue;

      if (catcher_item.text != "") begin
         bit match = 0;
         `foreach (msg.text,j) begin
            if (`vmm_str_match(msg.text[j], catcher_item.text)) begin
	       match = 1;
               break;
            end
         end
	 if (!match) continue;
      end

      catcher_item.catcher.thrown = 0;
      catcher_item.catcher.issued = 0;
      catcher_item.catcher.caught(msg);

      if (catcher_item.catcher.thrown &&
          catcher_item.catcher.issued) begin
         string img;
         string txt[$];

         txt.push_back("Cannot call vmm_log_catcher::issue() AND vmm_log_catcher::throw() in the same vmm_log_catcher::caught() implementation. Ignoring throw.");

         catcher_item.catcher.thrown = 0;

         img = this.fmt.format_msg(this.name, this.inst, 
                                   this.typ_image(FAILURE_TYP),
                                   this.sev_image(WARNING_SEV),
`ifdef VMM_LOG_FORMAT_FILE_LINE
                                   msg.fname, msg.line,
`endif
                                   txt);
         $write("%s\n", img);
         this.n_msg[WARNING_SEV]++;
      end
      if (!catcher_item.catcher.thrown) begin
         this.msg.issued = catcher_item.catcher.issued;
         break;
      end
   end
endfunction


function void vmm_log::flush_msg();
   string msg;

   if (this.msg.flushed == 0) begin

      // Perform promotion/demotion if there are text filters
      // (it will have been done in start_msg() if there were none)
      if (this.has_text_modifiers) begin
         this.promote();
         this.filter();
      end
      // Record risky demotions
      if (this.msg.effective_severity > this.msg.original_severity) begin
         case (this.msg.original_severity)
            ERROR_SEV  : this.n_demoted[ERROR_SEV]++;
            WARNING_SEV: this.n_demoted[WARNING_SEV]++;
         endcase
      end

      if (this.msg.issued === 1'b0) begin
         this.notify();
         return;
      end

      this.in_catcher = 1;
      this.process_catch(this.msg);
      this.in_catcher = 0;
      this.notify();
      if (this.msg.issued === 1'b0) return;




      msg = this.fmt.format_msg(this.name, this.inst, 
                                this.typ_image(this.msg.effective_typ),
                                this.sev_image(this.msg.effective_severity),
`ifdef VMM_LOG_FORMAT_FILE_LINE
                                this.msg.fname, this.msg.line,
`endif
                                this.msg.text);
      if (msg != "") begin
         `foreach(this.fp,i) begin
            $fdisplay(this.fp[i], "%s", msg);
         end
         // Did we just send an ERROR or FATAL message to /dev/null??
         if (this.fp.size() == 0 && this.msg.effective_severity <= ERROR_SEV) begin
            // Force it to appear on STDOUT
            $display("%s", msg);
         end
      end

      this.msg.flushed++;
`ifdef VCS2006_06
      // Work-around for NYI feature in 2006.06
      // but IEEE 1800-2009 compliant
      this.msg.text.delete();
`else
`ifdef INCA
      this.msg.text.delete();
`else
      // Works in VCS2008.03 or later
      // IEEE 1800-2005 compliant
      this.msg.text = '{};
`endif
`endif
   end
   else begin
      if (this.msg.text.size() > 0) begin
         msg = this.fmt.continue_msg(this.name, this.inst, 
                                     this.typ_image(this.msg.effective_typ),
                                     this.sev_image(this.msg.effective_severity),
`ifdef VMM_LOG_FORMAT_FILE_LINE
                                     this.msg.fname, this.msg.line,
`endif
                                     this.msg.text);
         if (msg != "") begin
            `foreach(this.fp,i) begin
               $fdisplay(this.fp[i], "%s", msg);
            end
            // Did we just send an ERROR or FATAL message to /dev/null??
            if (this.fp.size() == 0 && this.msg.effective_severity <= ERROR_SEV) begin
               // Force it to appear on STDOUT
               $display("%s", msg);
            end
         end

         this.msg.flushed++;
`ifdef VCS2006_06
         // Work-around for NYI feature in 2006.06
         // but IEEE 1800-2009 compliant
         this.msg.text.delete();
`else
`ifdef INCA
         this.msg.text.delete();
`else
         // Works in VCS2008.03 or later
         // IEEE 1800-2005 compliant
         this.msg.text = '{};
`endif
`endif
      end
      return;
   end

   this.n_msg[this.msg.effective_severity]++;
endfunction: flush_msg


function void vmm_log::enable_types(int    typs,
                                    string name = "",
                                    string inst = "",
                                    bit    recursive = 0);
   if (typs == DEFAULT_TYP ) typs = ALL_TYPS ;
   if (typs < 0) begin
      `vmm_error(this, "Invalid message type specified to vmm_log::enable_types");
      return;
   end

   //
   // Enable specified types in all specified log insts
   //
   this.reset(name, inst, recursive);
   for(vmm_log log = this.for_each(); log != null; log = this.for_each()) begin
      log.enabled_typs |= typs;
   end
endfunction: enable_types


function void vmm_log::disable_types(int    typs,
                                     string name = "",
                                     string inst = "",
                                     bit    recursive = 0);
   if (typs < 0) begin
      `vmm_error(this, "Invalid message type specified to vmm_log::disable_types");
      return;
   end
   // Cannot disable failure messages
   if (typs & FAILURE_TYP) begin
      `vmm_warning(this, "Cannot disable FAILURE_TYP messages");
      typs -= FAILURE_TYP;
   end

   //
   // Disable specified types in all specified log insts
   //
   this.reset(name, inst, recursive);
   for(vmm_log log = this.for_each(); log != null; log = this.for_each()) begin
      log.enabled_typs &= ~(typs);
   end
endfunction: disable_types

   
function int vmm_log::modify(string name         = "",
                             string inst         = "",
                             bit    recursive    = 0,
                             int    typ          = ALL_TYPS,
                             int    severity     = ALL_SEVS,
                             string text         = "",
                             int    new_typ      = UNCHANGED,
                             int    new_severity = UNCHANGED,
                             int    handling     = UNCHANGED);
   vmm_log_modifier modifier;
   int          mod_id;

   // Some severities cannot be demoted too far
   if (severity == FATAL_SEV &&
       new_severity > ERROR_SEV) begin
      `vmm_error(this, "Cannot demote FATAL_SEV severity to less than ERROR_SEV");
      return -2;
   end
   if (severity == ERROR_SEV &&
       new_severity > WARNING_SEV) begin
      `vmm_error(this, "Cannot demote ERROR severity to less than WARNING");
      return -2;
   end

   //
   // Add a description of the modification to the cache
   //
   modifier = new;
   modifier.typ          = typ;
   modifier.severity     = severity;
   modifier.pattern      = text;
   modifier.new_typ      = new_typ;
   modifier.new_severity = new_severity;
   modifier.handling     = handling;

   // Remove "/" surrounding the pattern, if any
   if (`vmm_str_match(modifier.pattern, "^/(.*)/$")) begin
      modifier.pattern = `vmm_str_backref(modifier.pattern, 0);
   end

   mod_id = this.modifier_cache.num();
   this.modifier_cache[mod_id] = modifier;

   //
   // Link all affected log instances
   //
   this.reset(name, inst, recursive);
   for(vmm_log log = this.for_each(); log != null; log = this.for_each()) begin
      log.modifier_ids.push_back(mod_id);
      if (modifier.pattern != "") log.has_text_modifiers++;
   end

   modify = mod_id;
endfunction: modify


function void vmm_log::unmodify(int    modification_id = -1,
                                string name            = "",
                                string inst            = "",
                                bit    recursive       = 0);
   if (modification_id < -1) begin
      `vmm_error(this, `vmm_sformatf("Invalid modification ID %0d specified to vmm_log::unmodify()",
                                     modification_id));
      return;
   end

   // Does it exist?
   if (modification_id >= 0) begin
      if (!this.modifier_cache.exists(modification_id)) begin
         `vmm_error(this, `vmm_sformatf("Unknown modification ID %0d specified to vmm_log::unmodify()",
                                        modification_id));
         return;
      end
   end
   
   //
   // Unlink all affected log instances
   //
   this.reset(name, inst, recursive);
   for(vmm_log log = this.for_each(); log != null; log = this.for_each()) begin

      // Find the specified modifier...
      `foreach(log.modifier_ids,i) begin
         if (modification_id >= 0 && log.modifier_ids[i] != modification_id) continue;

         if (this.modifier_cache[log.modifier_ids[i]].pattern != "") begin
            log.has_text_modifiers--;
            if (log.has_text_modifiers < 0) begin
               $write("***** vmm_log Internal ERROR: has_text_modifiers < 0\n");
               log.has_text_modifiers = 0;
            end
         end
         if (modification_id >= 0) begin
            log.modifier_ids.delete(i);
            break;
         end
      end
      if (modification_id < 0) begin
`ifdef VCS2006_06
         // Work-around for NYI feature in 2006.06
         // but IEEE 1800-2009 compliant
         log.modifier_ids.delete();
`else
`ifdef INCA
         log.modifier_ids.delete();
`else
         // Works in VCS2008.03 or later
         // IEEE 1800-2005 compliant
         log.modifier_ids = '{};
`endif
`endif
      end
   end
endfunction: unmodify


function void vmm_log::promote();

   // Apply modifiers in the order they were created
   `foreach(this.modifier_ids,i) begin
      vmm_log_modifier mod;
      
      mod = this.modifier_cache[this.modifier_ids[i]];

      // Does it apply to this message?

      // Message type must be included
      if (!(mod.typ & this.msg.effective_typ)) continue;

      // Message severity must be included
      if (!(mod.severity & this.msg.effective_severity)) continue;

      // If specified, the text pattern must match
      if (mod.pattern != "") begin
         bit matched = 0;
         int idx;
         `foreach (this.msg.text,idx) begin
            if (`vmm_str_match(this.msg.text[idx], mod.pattern)) begin
               matched = 1;
               break;
            end
         end
         if (!matched) continue;
      end

      // Promote message!
      if (mod.new_typ != UNCHANGED) begin
         if (mod.new_typ == DEFAULT) begin
            this.msg.effective_typ = this.msg.original_typ;
         end else begin
            this.msg.effective_typ = mod.new_typ;
         end
      end

      if (mod.new_severity != UNCHANGED) begin
         if (mod.new_severity == DEFAULT) begin
            this.msg.effective_severity = this.msg.original_severity;
         end else begin
            this.msg.effective_severity = mod.new_severity;
         end
         // Some severities cannot be demoted too far
         if (this.msg.original_severity == FATAL_SEV &&
             this.msg.effective_severity > ERROR_SEV) begin
            this.msg.effective_severity = ERROR_SEV ;
         end
         if (this.msg.original_severity == ERROR_SEV &&
             this.msg.effective_severity > WARNING_SEV) begin
            this.msg.effective_severity = WARNING_SEV;
         end
      end

      if (mod.handling != UNCHANGED) begin
         this.msg.handling = mod.handling;
      end
   end
endfunction: promote
   

function void vmm_log::filter();

   if (this.msg.issued === 1'b0 ||  // Already filtered out
       this.msg.effective_severity == IGNORE_SEV ||  // Demoted to be ignored
       // Cannot disable any types with severity FATAL or ERROR
       (!(this.msg.effective_typ & this.enabled_typs) &&     // Disabled
        (this.msg.effective_severity >= WARNING_SEV)) ||
       (this.force_lvl != DEFAULT_SEV && this.msg.effective_severity > this.force_lvl) ||
       (this.force_lvl == DEFAULT_SEV && this.log_lvl < this.msg.effective_severity)) begin
      this.msg.issued = 1'b0;

      return;
   end

   this.msg.issued = 1'b1;
endfunction: filter
   

function void vmm_log::notify();
   // Check notifiers in the order they were created
   `foreach(this.watchpoint_ids,i) begin
      vmm_log_watchpoint wp;

      wp = this.watchpoint_cache[this.watchpoint_ids[i]];

      // Does it apply to this message?

      // Message type must be included
      if (!(wp.typ & this.msg.effective_typ)) continue;

      // Message severity must be included
      if (!(wp.severity & this.msg.effective_severity)) continue;

      // The message must be issued or not
      if (wp.issued !== 1'bx && wp.issued !== this.msg.issued) begin
         continue;
      end

      // If specified, the text pattern must match
      if (wp.pattern != "") begin
         bit matched = 0;
         integer idx;
         `foreach(this.msg.text,idx) begin
            if (`vmm_str_match(this.msg.text[idx], wp.pattern)) begin
               matched = 1;
               break;
            end
         end
         if (!matched) continue; // to the next watchpt
      end

      // This is a watched message
      wp.msg = this.msg.copy();
      -> wp.seen;
   end
endfunction: notify


function void vmm_log::set_verbosity(int    severity,
                                     string name    = "",
                                     string inst    = "",
                                     bit    recursive = 0);
   if (!this.sev_images.exists(severity) ||
       severity < ERROR_SEV ||
       severity > VERBOSE_SEV) begin
      `vmm_error(this, "Invalid severity specified to vmm_log::set_verbosity()");
      return;
   end

   this.reset(name, inst, recursive);
   for(vmm_log log = this.for_each(); log != null; log = this.for_each()) begin
      log.log_lvl = severity;
   end
endfunction: set_verbosity
   

function int vmm_log::get_verbosity();
   if(this.force_lvl != DEFAULT_SEV)
     get_verbosity = this.force_lvl;
   else
     get_verbosity = this.log_lvl;
endfunction: get_verbosity


function void vmm_log::log_start(int    file,
                                 string name = "",
                                 string inst = "",
                                 bit    recurse = 0);
   // Find the loggers in question
   vmm_log log;
      
   this.reset(name, inst, recurse);
   for(log = this.for_each(); log != null; log = this.for_each()) begin
      
      // Check that we are not already logging to this file
      `foreach(log.fp,i) begin
         if (log.fp[i] == file) return;
      end
      log.fp.push_back(file);


   end
endfunction: log_start


function void vmm_log::log_stop(int    file,
                                string name = "",
                                string inst = "",
                                bit    recurse = 0);
   // Find the loggers in question
   vmm_log log;
      
   this.reset(name, inst, recurse);
   for(log = this.for_each(); log != null; log = this.for_each()) begin
      
      // Check that we are indeed logging to this file
      `foreach(log.fp,i) begin
         if (log.fp[i] == file) log.fp.delete(i);
         // Cannot close this file because it may still be used by other loggers
      end
   end
endfunction: log_stop


function void vmm_log::stop_after_n_errors(int n);
   this.error_count = 0;
   this.error_limit = n;
endfunction: stop_after_n_errors
   
function int vmm_log::get_message_count(int    severity = ALL_SEVS,
                                        string name = "",
                                        string inst = "",
                                        bit    recurse = 0);
   get_message_count = 0;

   this.reset(name, inst, recurse);
   for(vmm_log log = this.for_each(); log != null; log = this.for_each()) begin

      if (severity & FATAL_SEV)   get_message_count += log.n_msg[FATAL_SEV];
      if (severity & ERROR_SEV)   get_message_count += log.n_msg[ERROR_SEV];
      if (severity & WARNING_SEV) get_message_count += log.n_msg[WARNING_SEV];
      if (severity & NORMAL_SEV)  get_message_count += log.n_msg[NORMAL_SEV];
      if (severity & TRACE_SEV)   get_message_count += log.n_msg[TRACE_SEV];
      if (severity & DEBUG_SEV)   get_message_count += log.n_msg[DEBUG_SEV];
      if (severity & VERBOSE_SEV) get_message_count += log.n_msg[VERBOSE_SEV];
      if (severity & HIDDEN_SEV)  get_message_count += log.n_msg[HIDDEN_SEV];
      if (severity & IGNORE_SEV)  get_message_count += log.n_msg[IGNORE_SEV];
   end
endfunction: get_message_count


task vmm_log::wait_for_msg(string          name = "",
                           string          inst = "",
                           bit             recurse = 0,
                           int             typs = ALL_TYPS,
                           int             severity = ALL_SEVS,
                           string          text = "",
                           logic           issued = 1'bx,
                           ref vmm_log_msg msg);
   int wp_id;

   wp_id = this.create_watchpoint(typs, severity, text, issued);
   this.add_watchpoint(wp_id, name, inst, recurse);
   this.wait_for_watchpoint(wp_id, msg);
   this.remove_watchpoint(wp_id, name, inst, recurse);
endtask: wait_for_msg


function int vmm_log::create_watchpoint(int     typs = ALL_TYPS,
                                        int     severity = ALL_SEVS,
                                        string  text = "",
                                        logic   issued = 1'bx);
   vmm_log_watchpoint wp = new;
   int                wp_id;

   //
   // Add a description of the watchpoint to the cache
   //
   wp.typ          = typs;
   wp.severity     = severity;
   wp.pattern      = text;
   wp.issued       = issued;

   // Remove "/" surrounding the pattern, if any
   if (`vmm_str_match(wp.pattern, "^/(.*)/$")) begin
      wp.pattern = `vmm_str_backref(wp.pattern, 0);
   end

   wp_id = this.watchpoint_cache.num();
   this.watchpoint_cache[wp_id] = wp;

   create_watchpoint = wp_id;
endfunction: create_watchpoint


function void vmm_log::add_watchpoint(int     watchpoint_id,
                                      string  name = "",
                                      string  inst = "",
                                      bit     recurse = 0);
   vmm_log            log;
   vmm_log_watchpoint wp;

   if (!this.watchpoint_cache.exists(watchpoint_id)) begin
      `vmm_warning(this, `vmm_sformatf("Watchpoint #%0d does not exist", watchpoint_id));
      return;
   end
   wp = this.watchpoint_cache[watchpoint_id];
   
   //
   // Link all affected log insts
   //
   this.reset(name, inst, recurse);
   for(log = this.for_each(); log != null; log = this.for_each()) begin
      log.watchpoint_ids.push_back(watchpoint_id);
      if (wp.pattern != "") log.has_text_modifiers++;
   end
endfunction: add_watchpoint
   

function void vmm_log::remove_watchpoint(int     watchpoint_id = -1,
                                         string  name = "",
                                         string  inst = "",
                                         bit     recurse = 0);
   vmm_log log;
   
   //
   // Unlink all affected log insts
   //
   this.reset(name, inst, recurse);
   for(log = this.for_each(); log != null; log = this.for_each()) begin

      // Find the specified watchpoint...
      `foreach(log.watchpoint_ids,i) begin
         if (watchpoint_id < 0 || log.watchpoint_ids[i] == watchpoint_id) begin
            if (this.watchpoint_cache[log.watchpoint_ids[i]].pattern != "") begin
               log.has_text_modifiers--;
               if (log.has_text_modifiers < 0) begin
                  $write("***** vmm_log Internal ERROR: has_text_modifiers < 0\n");
                  log.has_text_modifiers = 0;
               end
            end
            log.watchpoint_ids.delete(i);
            if (watchpoint_id >= 0) break;
         end
      end
   end
endfunction: remove_watchpoint

   
task vmm_log::wait_for_watchpoint(int             watchpoint_id,
                                  ref vmm_log_msg msg);
   vmm_log_watchpoint wp;
   
   if (!this.watchpoint_cache.exists(watchpoint_id)) begin
      `vmm_warning(this, `vmm_sformatf("Watchpoint #%0d does not exist", watchpoint_id));
      msg = null;
   end
   else begin
      //
      // Wait for a triggering of the watchpoint
      //
      wp = this.watchpoint_cache[watchpoint_id];
      @wp.seen;
      msg = wp.msg;
   end
endtask: wait_for_watchpoint


function int vmm_log::catch(vmm_log_catcher catcher,
			    string name     = "",
			    string inst     = "",
			    bit    recurse  = 0,
			    int    typs     = ALL_TYPS,
			    int    severity = ALL_SEVS,
			    string text     = "");
   int catcher_id = 0;
   vmm_log_catcher_descr catcher_item;

   if (catcher == null) begin
      `vmm_error(this,"Null vmm_log_catcher object passed to vmm_log::catch");
      return -1;
   end

   catcher_item = new();
   catcher_item.catcher = catcher;

   // Remove "/" surrounding the pattern, if any
   if (`vmm_str_match(text, "^/(.*)/$")) begin
      catcher_item.text = `vmm_str_backref(text, 0);
   end
   else catcher_item.text = text;

   catcher_item.name     = name;
   catcher_item.inst     = inst;
   catcher_item.recurse  = recurse;
   catcher_item.typs     = typs;
   catcher_item.severity = severity;

   catcher_id = this.catcher_cache.num();
   this.catcher_cache[catcher_id] = catcher_item;

   this.reset(name, inst, recurse);
   for(vmm_log log = this.for_each(); log != null; log = this.for_each()) begin
      log.catcher_ids.push_front(catcher_id);
   end

   return catcher_id;
endfunction: catch


function bit vmm_log::uncatch (int catcher_id);
   vmm_log_catcher_descr catcher_item;

   int index = 0;
   int match = 0;

   if((catcher_id < 0 )) begin
      `vmm_warning(this,"Invalid catcher_id given to vmm_log::uncatch. Cannot uncatch");
      return 0;
   end

   // Does it exist?
   if (catcher_id >= 0) begin
      if (!this.catcher_cache.exists(catcher_id)) begin
         `vmm_error(this, `vmm_sformatf("Unknown catcher ID %0d specified to vmm_log::uncatch()",
                                        catcher_id));
         return 0;
      end
   end
   catcher_item = this.catcher_cache[catcher_id];
   
   this.reset(catcher_item.name, catcher_item.inst, catcher_item.recurse);
   for(vmm_log log = this.for_each(); log != null; log = this.for_each()) begin
      `foreach(log.catcher_ids,i) begin
         if (log.catcher_ids[i] == catcher_id) begin
            log.catcher_ids.delete(i);
            break;
         end
      end
   end
endfunction: uncatch


function void vmm_log::uncatch_all();
   this.catcher_cache.delete();
   `foreach (this.known,i) begin
`ifdef VCS2006_06
      // Work-around for NYI feature in 2006.06
      // but IEEE 1800-2009 compliant
      this.known[i].catcher_ids.delete();
`else
`ifdef INCA
      this.known[i].catcher_ids.delete();
`else
      // Works in VCS2008.03 or later
      // IEEE 1800-2005 compliant
      this.known[i].catcher_ids = '{};
`endif
`endif
   end
endfunction: uncatch_all


function void vmm_log::prepend_callback(vmm_log_callbacks cb);
   // Check if callback has already been registered...
   `foreach (this.callbacks,i) begin
      if (this.callbacks[i] == cb) begin
      `ifdef VMM_LOG_FORMAT_FILE_LINE      
         if (this.start_msg(FAILURE_TYP, WARNING_SEV, `__FILE__, `__LINE__)) begin
      `else
         if (this.start_msg(FAILURE_TYP, WARNING_SEV)) begin
      `endif
            void'(this.text("Callback has already been registered"));
            this.end_msg();
         end
         return;
      end
   end

   // Register new callback
   this.callbacks.push_front(cb);
endfunction: prepend_callback
   

function void vmm_log::append_callback(vmm_log_callbacks cb);
   // Check if callback has already been registered...
   `foreach (this.callbacks,i) begin
      if (this.callbacks[i] == cb) begin
      `ifdef VMM_LOG_FORMAT_FILE_LINE
         if (this.start_msg(FAILURE_TYP, WARNING_SEV, `__FILE__, `__LINE__)) begin
      `else
          if (this.start_msg(FAILURE_TYP, WARNING_SEV)) begin
      `endif
            void'(this.text("Callback has already been registered"));
            this.end_msg();
         end
         return;
      end
   end

   // Register new callback
   this.callbacks.push_back(cb);
endfunction: append_callback
   

function void vmm_log::unregister_callback(vmm_log_callbacks cb);
   // Look for callback
   `foreach (this.callbacks,i) begin
      if (this.callbacks[i] == cb) begin
         // Unregister it
         this.callbacks.delete(i);
         return;
      end
   end
`ifdef VMM_LOG_FORMAT_FILE_LINE
   if (this.start_msg(FAILURE_TYP, WARNING_SEV, `__FILE__, `__LINE__)) begin
`else
   if (this.start_msg(FAILURE_TYP, WARNING_SEV)) begin
`endif
      void'(this.text("Callback was not registered"));
      this.end_msg();
   end
endfunction: unregister_callback   


  //
  // vmm_log_format
  //

function string vmm_log_format::format_msg(string name,
                                           string inst,
                                           string msg_typ,
                                           string severity,
`ifdef VMM_LOG_FORMAT_FILE_LINE
                                           string fname,
                                           int    line,
`endif
                                           ref string lines[$]);
`ifdef VMM_LOG_FORMAT_FILE_LINE
if (line >= 0)
   $sformat(format_msg, "%s[%s] on %s(%s) at %t from %s, line %0d:",
            severity, msg_typ, name, inst, $realtime, fname, line);
else
`endif
   $sformat(format_msg, "%s[%s] on %s(%s) at %t:",
            severity, msg_typ, name, inst, $realtime);
   foreach(lines[i]) begin
      string line = lines[i];
      string t;

      format_msg = {format_msg, "\n    "};

      while (1) begin
         string pre;
         if (!`vmm_str_match(line, "\n")) begin
            format_msg = {format_msg, line};
            break;
         end

         pre = `vmm_str_prematch(line);
         format_msg = {format_msg, pre, "\n    "};
         line = `vmm_str_postmatch(line);
      end
   end
endfunction: format_msg
  

function string vmm_log_format::continue_msg(string name,
                                             string inst,
                                             string msg_typ,
                                             string severity,
`ifdef VMM_LOG_FORMAT_FILE_LINE
                                             string fname,
                                             int    line,
`endif
                                             ref string lines[$]);
   continue_msg = "";
   foreach (lines[i]) begin
      if (i > 0) continue_msg = {continue_msg, "\n"};
      continue_msg = { continue_msg, "    ", lines[i] };
   end
endfunction: continue_msg


function string vmm_log_format::abort_on_error(int count,
                                               int limit);
   abort_on_error = "Maximum number of error messages exceeded. Aborting\nUse method stop_after_n_errors() of vmm_log to increase threshold.";
endfunction: abort_on_error


function string vmm_log_format::pass_or_fail(bit    pass,
                                             string name,
                                             string inst,
                                             int    fatals,
                                             int    errors,
                                             int    warnings,
                                             int    dem_errs,
                                             int    dem_warns);
   if (pass) begin
      $sformat(pass_or_fail, "Simulation PASSED on %s (%s) at %t (%0d warnings, %0d demoted errors & %0d demoted warnings)",
               name, inst, $realtime, warnings, dem_errs, dem_warns);
   end else begin
      $sformat(pass_or_fail, "Simulation *FAILED* on %s (%s) at %t: %0d errors, %0d warnings",
             name, inst, $realtime, fatals + errors, warnings);
   end
endfunction: pass_or_fail




function void vmm_log_catcher::issue(vmm_log_msg msg);
   this.issued = 1;
endfunction:issue


function void vmm_log_catcher::throw(vmm_log_msg msg);
   this.thrown = 1;
endfunction:throw




