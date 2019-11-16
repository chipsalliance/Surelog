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



function xvc_xactor::new(string             name,
                         string             inst,
                         int                stream_id = -1,
                         xvc_action_channel action_chan = null,
                         xvc_action_channel interrupt_chan = null
                         `VMM_XACTOR_NEW_EXTERN_ARGS);
   super.new(name, inst, stream_id `VMM_XACTOR_NEW_CALL);

   this.trace = new({name, " Trace"}, inst);

   if (action_chan == null) begin
      action_chan = new({name, "Action Channel"}, inst);
   end else action_chan.reconfigure(1, 0);
   this.action_chan = action_chan;
   this.log.is_above(this.action_chan.log);

   if (interrupt_chan == null) begin
      interrupt_chan = new({name, "Interrupt Channel"}, inst, 65535);
   end else interrupt_chan.reconfigure(65535, 0);
   this.interrupt_chan = interrupt_chan;
   this.log.is_above(this.interrupt_chan.log);

   this.interrupt = 0;
   this.interrupted = 0;

   this.idle = new("Dummy idle action", this.log);
endfunction: new


function void xvc_xactor::add_action(xvc_action action);
   int i;

   if (action == null) begin
      `vmm_error(this.log, "Attempting to add a NULL action");
      return;
   end

   // Do we already know about this action?
   `foreach(this.known_actions,i) begin
      if (this.known_actions[i] == action) begin
         `vmm_warning(this.log, "Attempting to add already-known action");
         return;
      end
   end

   this.known_actions.push_back(action);
endfunction: add_action


function xvc_action xvc_xactor::parse(string argv[]);
   int i;

   parse = null;

   `foreach(this.known_actions,i) begin
      parse = this.known_actions[i].parse(argv);
      if (parse != null) return parse;
   end

   if (this.log.start_msg(vmm_log::FAILURE_TYP,
                          vmm_log::ERROR_SEV)) begin
       string msg = "Unknown action command:";
       foreach (argv[i]) begin
          msg = {msg, " ", argv[i]};
       end
       void'(this.log.text(msg));
       this.log.end_msg();
   end
endfunction: parse


function void xvc_xactor::start_xactor();
   super.start_xactor();
endfunction: start_xactor


function void xvc_xactor::stop_xactor();
   super.stop_xactor();
endfunction: stop_xactor


function void xvc_xactor::reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);
   super.reset_xactor(rst_typ);

   this.action_chan.flush();
   this.interrupt_chan.flush();
   this.executing = null;
   this.interrupt = 0;
   this.interrupted = 0;
       
   if (rst_typ > vmm_xactor::HARD_RST) begin
`ifdef VCS2006_06
      // Work-around for NYI feature in VCS2006.06
      // but IEEE 1800-2009 compliant
      this.known_actions.delete();
`else
`ifdef INCA
      this.known_actions.delete();
`else
      // Works in VCS2008.03 or later
      // IEEE 1800-2005 compliant
      this.known_actions = '{};
`endif
`endif
   end
endfunction: reset_xactor


function void xvc_xactor::xactor_status(string prefix = "");
   super.xactor_status(prefix);

   if (this.interrupt) begin
      // Pending interrupt
      if (this.interrupted) begin
         // Interrupted...
         if (this.executing == null) begin
            `vmm_error(this.log,
                       "Internal Error: interrupted but not executing");
         end else begin
            $display("   Executing interrupt action \"%s\".",
                     this.executing.get_name());
         end
      end else begin
         $display("   Waiting for action \"%s\" to be interrupted.",
                  this.executing.get_name());
      end
   end else begin
      if (this.executing == null) begin
         $display("   Waiting to execute an action...");
      end else begin
         $display("   Executing action \"%s\".",
                this.executing.get_name());
      end
   end
endfunction: xactor_status


task xvc_xactor::main();
   fork
       super.main();
       this.execute_actions();
       this.execute_interruptions();
   join_none
endtask: main


task xvc_xactor::execute_actions();
   xvc_action action;

   while (1) begin
      // OK to be interrupted while not executing actions
      this.interrupted = 1;
      this.wait_if_stopped_or_empty(this.action_chan);
      this.action_chan.activate(action);
      this.interrupted = 0;

      this.executing = action;
      this.wait_if_interrupted();

      this.execute_action(this.action_chan, "action");
   end
endtask: execute_actions


task xvc_xactor::execute_interruptions();
   xvc_action action;

   while (1) begin
      this.wait_if_stopped_or_empty(this.interrupt_chan);
      this.interrupt_chan.activate(action);

      this.interrupt = 1;
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
         void'(this.log.text("Requesting action interrupt..."));
         this.log.end_msg();
      end
      wait (this.interrupted);

      if (this.suspended == null) this.suspended = idle;
      this.execute_action(this.interrupt_chan, "interrupt action");
      if (this.suspended == idle) this.suspended = null;
   
     if (this.interrupt_chan.level() == 0) begin
         this.interrupt = 0;
         -> this.rte;
      end
   end
endtask: execute_interruptions          


task xvc_xactor::wait_if_interrupted();
   if (this.suspended != null) begin
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::WARNING_SEV)) begin
         void'(this.log.text("Interrupt actions cannot be interrupted. Ignoring call to xvc_xactor::wait_if_interrupted()"));
         this.log.end_msg();
      end
      return;
   end

   // Wait, not only for an interrupt action that is
   // requesting execution - but also if there is
   // one ready in the interrupt channel to resolve
   // race condition between the regular executor and
   // the interrupt executor.
   if (this.interrupt || this.interrupt_chan.level() > 0) begin
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
         void'(this.log.text(`vmm_sformatf("Interrupting action \"%s\"...",
                                           this.executing.get_name())));
         this.log.end_msg();
      end
      this.suspended = this.executing;
      this.executing = null;
      this.interrupted = 1;

      @this.rte;
      this.executing = this.suspended;
      this.suspended = null;
      this.interrupted = 0;
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
         void'(this.log.text(`vmm_sformatf("Resuming action \"%s\"...",
                                           this.executing.get_name())));
         this.log.end_msg();
      end
   end
endtask: wait_if_interrupted


task xvc_xactor::execute_action(xvc_action_channel chan,
                                string             descr);
   xvc_action action;
   int i;

   action = chan.active_slot();

   if (this.trace.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
      void'(this.trace.text(`vmm_sformatf("Executing %s \"%s\"...",
                                          descr, action.get_name())));
      this.trace.end_msg();
   end

   this.executing = action;
   this.executing.display({descr,": "});
   // Prepend any callback required by the action
   `foreach (action.callbacks,i) begin
      if (action.callbacks[i] != null) begin
         if (i >= this.xactors.size() || this.xactors[i] == null) begin
            `vmm_fatal(this.log,
                       `vmm_sformatf("No xvc_xactor::xactors[%0d] to register callback from action \"%s\".",
                                     i, action.get_name()));
            continue;
         end
         this.xactors[i].prepend_callback(action.callbacks[i]);
      end
   end
   
   void'(chan.start());
   action.execute(this.exec_chan, this);
   void'(chan.complete());

   // De-register callbacks
   `foreach (action.callbacks,i) begin
      if (action.callbacks[i] != null) begin
         if (i >= this.xactors.size() || this.xactors[i] == null) continue;
         this.xactors[i].unregister_callback(action.callbacks[i]);
      end
   end
   
   this.executing = null;

   if (this.trace.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
      void'(this.trace.text(`vmm_sformatf("Completed %s \"%s\"...",
                                          descr, action.get_name())));
      this.trace.end_msg();
   end
   
   void'(chan.remove());
endtask: execute_action


function void xvc_xactor::save_rng_state();
endfunction: save_rng_state


function void xvc_xactor::restore_rng_state();
endfunction: restore_rng_state
