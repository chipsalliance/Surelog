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


function vmm_xactor::new(string name,
                         string inst,
     	                 int    stream_id = -1
                         `VMM_XACTOR_BASE_NEW_EXTERN_ARGS);


`ifdef VMM_XACTOR_BASE_NEW_CALL
   super.new(`VMM_XACTOR_BASE_NEW_CALL);
`endif

   this.log  = new(name, inst);
   this.notify = new(this.log);
   `VMM_OBJECT_SET_PARENT(this.notify, this)

   void'(this.notify.configure(XACTOR_IDLE, vmm_notify::ON_OFF));
   void'(this.notify.configure(XACTOR_BUSY, vmm_notify::ON_OFF));
   void'(this.notify.configure(XACTOR_STARTED));
   void'(this.notify.configure(XACTOR_STOPPING, vmm_notify::ON_OFF));
   void'(this.notify.configure(XACTOR_IS_STOPPED, vmm_notify::ON_OFF));
   void'(this.notify.configure(XACTOR_STOPPED));
   void'(this.notify.configure(XACTOR_RESET));

   this.is_stopped = 1;
   this.notify.indicate(XACTOR_IS_STOPPED);
   this.notify.indicate(XACTOR_IDLE);
   this.notify.reset(XACTOR_BUSY);

   this.stream_id   = stream_id;

   this.start_it   = 0;
   this.stop_it    = 1;
   this.reset_it   = 0;
   this.n_threads_to_stop = -1;
   this.n_threads_stopped = 0;
   this.main_running = 0;

   // Dummy first entry in list of known transactors
   if (this._vmm_available_xactor.size() == 0) begin
      this._vmm_available_xactor.push_back(null);
   end
   this._vmm_available_xactor.push_back(this); 

   fork
      begin
      this.save_main_rng_state    = 1;
      this.restore_main_rng_state = 0;
      this.main_rng_state = get_randstate();

      while (1) begin
         this.main_running = 0;

         // wait to start
         while (!this.start_it) @(this.control_event);
         this.start_it = 0;
         this.stop_it  = 0;
         this.reset_it = 0;
         this.n_threads_to_stop = -1;
         this.n_threads_stopped = 0;
         this.is_stopped = 0;

         // We may be held back by on-going reset operation
         fork
            if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
               void'(this.log.text("Start delayed by on-going reset activity"));
               this.log.end_msg();
            end
         join_none

         while (this.reset_pending > 0) begin
            `vmm_fatal(this.log, "Pending resets not currently supported");
            // `wait(@(this.reset_pending)); // Not supported yet.
         end
         disable fork;

         //
         // Fork the main body
         //
               
         if (this.save_main_rng_state) begin
            this.main_rng_state = get_randstate();
         end
         if (this.restore_main_rng_state) begin
            set_randstate(main_rng_state);
         end
         this.save_main_rng_state    = 0;
         this.restore_main_rng_state = 0;

         fork
            begin
               if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV )) begin
                  void'(this.log.text("Started"));
                  this.log.end_msg();
               end

               this.is_stopped = 0;
               this.notify.reset(XACTOR_IDLE);
               this.notify.reset(XACTOR_IS_STOPPED);
               this.notify.indicate(XACTOR_BUSY);
               this.notify.indicate(XACTOR_STARTED);
               main();
            end

            begin
               // Check that super.main() was called in all
               // extensions of this class
               repeat (10) #0;
               if (!this.main_running) begin
                  `vmm_warning(this.log, "Virtual vmm_xactor::main() does not call super.main()");
               end
            end
         join_none

         // Wait to reset
         while (!this.reset_it) @(this.control_event);
         this.reset_it  = 0;
         this.n_threads_to_stop = -1;
         this.n_threads_stopped = 0;
         if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
            void'(this.log.text("Reset"));
            this.log.end_msg();
         end
         this.is_stopped = 1;
         this.notify.reset(XACTOR_BUSY);
         this.notify.indicate(XACTOR_IDLE);
         this.notify.reset(XACTOR_STOPPING);
         this.notify.indicate(XACTOR_IS_STOPPED);
         this.notify.indicate(XACTOR_STOPPED);
         this.notify.indicate(XACTOR_RESET);
         disable fork;
      end
   end
   join_none
endfunction: new


function string vmm_xactor::get_name();
   get_name = this.log.get_name();
endfunction:get_name


function string vmm_xactor::get_instance();
   get_instance = this.log.get_instance();
endfunction: get_instance


function void vmm_xactor::start_xactor();
   this.start_it = 1;
   this.stop_it  = 0;
   -> this.control_event;
   this.notify.reset(XACTOR_STOPPING);
endfunction: start_xactor


function void vmm_xactor::stop_xactor();
   this.start_it = 0;
   this.stop_it  = 1;
   -> this.control_event;
   this.notify.indicate(XACTOR_STOPPING);

   // Is it already stopped?
   if (this.is_stopped) begin
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
         void'(this.log.text("Already stopped"));
         this.log.end_msg();
      end
      this.notify.indicate(XACTOR_STOPPED);
      return;
   end

   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
      void'(this.log.text("Stop requested"));
      this.log.end_msg();
   end
   this.check_all_threads_stopped();
endfunction: stop_xactor


function void vmm_xactor::reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);
   this.start_it = 0;
   this.reset_it = 1;
   -> this.control_event;
   this.is_stopped = 1;

   // Reset notifier & RNG state on FIRM and above
   if (rst_typ == FIRM_RST ||
       rst_typ == HARD_RST) begin
      this.notify.reset(-1, vmm_notify::HARD);
      this.restore_rng_state();
   end
   else begin
      this.notify.reset(-1, vmm_notify::SOFT);
   end

   // Unregister all callbacks on HARD reset
   if (rst_typ == HARD_RST) begin
`ifdef VCS2006_06
      // Work-around for NYI feature in VCS2006.06
      // but IEEE 1800-2009 compliant
      this.callbacks.delete();
`else
`ifdef INCA
      this.callbacks.delete();
`else
      // Works in VCS2008.03 or later
      // IEEE 1800-2005 compliant
      this.callbacks = '{};
`endif
`endif
   end
endfunction: reset_xactor


function void vmm_xactor::save_rng_state();
   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
      void'(this.log.text("Saving RNG state information..."));
      this.log.end_msg();
   end

   if (!this.is_stopped) begin
      `vmm_warning(this.log, "save_rng_state() called while transactor is still running");
   end
   this.save_main_rng_state = 1;
endfunction: save_rng_state


function void vmm_xactor::restore_rng_state();
   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
      void'(this.log.text("Restoring RNG state information..."));
      this.log.end_msg();
   end

   if (!this.is_stopped) begin
      `vmm_warning(this.log, "restore_rng_state() called while transactor is still running");
   end
   this.restore_main_rng_state = 1;
endfunction: restore_rng_state


function string vmm_xactor::psdisplay(string prefix = "");
   $sformat(psdisplay, "%sTransactor %s (%s):", prefix,
            this.log.get_name(), this.log.get_instance());

   if (this.is_stopped) begin
      return {psdisplay, "\n", prefix, "Transactor is STOPPED"};
   end

   if (this.n_threads_stopped < this.n_threads_to_stop) begin
      return `vmm_sformatf("%s\n%sTransactor is STOPPING (%0d out of %0d threads stopped)",
                           psdisplay, prefix, this.n_threads_stopped,
                           this.n_threads_to_stop);
   end

   return {psdisplay, "\n", prefix, "Transactor is RUNNING"};
endfunction: psdisplay


function void vmm_xactor::xactor_status(string prefix = "");
   `vmm_note(this.log, this.psdisplay(prefix));
endfunction: xactor_status


task vmm_xactor::main();
   this.main_running = 1;
endtask: main


function void vmm_xactor::check_all_threads_stopped();
   if (this.n_threads_to_stop > 0) begin
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
         void'(this.log.text($psprintf("%0d out of %0d threads have now stopped",n_threads_stopped,this.n_threads_to_stop)));
         this.log.end_msg();
      end

      if (this.n_threads_stopped >= this.n_threads_to_stop) begin
         if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
            void'(this.log.text("Stopped"));
            this.log.end_msg();
         end
         
         this.is_stopped = 1;
         this.notify.reset(XACTOR_BUSY);
         this.notify.indicate(XACTOR_IDLE);
         this.notify.reset(XACTOR_STOPPING);
         this.notify.indicate(XACTOR_IS_STOPPED);
         this.notify.indicate(XACTOR_STOPPED);
      end
   end
endfunction


task vmm_xactor::wait_if_stopped(int unsigned n_threads = 1);
   if (n_threads == 0) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV)) begin
         void'(this.log.text("Number of threads to stop specified to vmm_xactor::wait_if_stopped() must be greater than 0"));
         this.log.end_msg();
      end
      n_threads = 1;
   end

   if (this.n_threads_to_stop <= 0) this.n_threads_to_stop = n_threads;
   else if (this.n_threads_to_stop != n_threads) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV)) begin
         void'(this.log.text("All threads must specify the same number of threads to stop to vmm_xactor::wait_if_stopped() and  vmm_xactor::wait_if_stopped_or_empty()"));
         this.log.end_msg();
      end
      if (this.n_threads_to_stop < n_threads) this.n_threads_to_stop = n_threads;
   end

   if (this.stop_it) begin
      this.n_threads_stopped++;
      this.check_all_threads_stopped();

      while (this.stop_it) @(this.control_event);
      // Make sure these are done only once if
      // there are multiple stopped threads
      if (this.is_stopped) begin
         if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
            void'(this.log.text("Restarted"));
            this.log.end_msg();
         end
         this.is_stopped = 0;
         this.notify.indicate(XACTOR_STARTED);
         this.notify.reset(XACTOR_IS_STOPPED);
         this.notify.reset(XACTOR_IDLE);
         this.notify.indicate(XACTOR_BUSY);
      end
      this.n_threads_stopped--;
   end
endtask: wait_if_stopped


task vmm_xactor::wait_if_stopped_or_empty(vmm_channel  chan,
                                          int unsigned n_threads = 1);

   if(chan == null) begin
     `vmm_error(this.log,"Passed null reference for channel to wait_if_stopped_or_empty");
     return;
   end

   this.wait_if_stopped(n_threads); 
   while (chan.level() == 0) begin
       vmm_data data;

       this.n_threads_stopped++;
       // If all other threads are blocked, indicate IDLE
       // because we are going to block on the channel
       if (this.n_threads_stopped >= this.n_threads_to_stop) begin
         this.notify.reset(XACTOR_BUSY);
         this.notify.indicate(XACTOR_IDLE);
       end

       if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
          void'(this.log.text($psprintf("%0d threads have now stopped or blocked",n_threads_stopped)));
          this.log.end_msg();
       end

       chan.peek(data);
       this.n_threads_stopped--;
       this.wait_if_stopped(n_threads);
  end

  this.notify.reset(XACTOR_IDLE);
  this.notify.indicate(XACTOR_BUSY);
endtask: wait_if_stopped_or_empty


function void vmm_xactor::prepend_callback(vmm_xactor_callbacks cb);
   if (cb == null) begin
      `vmm_error(this.log, "Attempting to prepend a NULL callback extension");
      return;
   end

   `foreach(this.callbacks,i) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, "Callback has already been registered");
         return;
      end
   end
   //Prepend new callback
   this.callbacks.push_front(cb);
endfunction: prepend_callback


function void vmm_xactor::append_callback(vmm_xactor_callbacks cb);
   if (cb == null) begin
      `vmm_error(this.log, "Attempting to append a NULL callback extension");
      return;
   end

   `foreach(this.callbacks,i) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, "Callback has already been registered");
         return;
      end
   end
   //Append new callback
   this.callbacks.push_back(cb);
endfunction: append_callback


function void vmm_xactor::unregister_callback(vmm_xactor_callbacks cb);
   `foreach(this.callbacks,i) begin
      if (this.callbacks[i] == cb) begin
         // Unregister it
         this.callbacks.delete(i);
         return;
      end
   end

   `vmm_warning(this.log, "Callback was not registered");
endfunction: unregister_callback


function void vmm_xactor::get_input_channels(ref vmm_channel chans[$]);
   chans = this.Xinput_chansX;
endfunction: get_input_channels


function void vmm_xactor::get_output_channels(ref vmm_channel chans[$]);
   chans = this.Xoutput_chansX;
endfunction: get_output_channels


function void vmm_xactor::kill();
   vmm_channel ins[$] = this.Xinput_chansX;
   vmm_channel outs[$] = this.Xoutput_chansX;

`ifdef VCS2006_06
   // Work-around for NYI feature in VCS2006.06
   // but IEEE 1800-2009 compliant
   this.Xinput_chansX.delete();
   this.Xoutput_chansX.delete();
`else
`ifdef INCA
   this.Xinput_chansX.delete();
   this.Xoutput_chansX.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.Xinput_chansX = '{};
   this.Xoutput_chansX = '{};
`endif
`endif
   
   foreach(ins[i]) begin
      if (ins[i].get_consumer() == this) begin
         ins[i].set_consumer(null);
         if (ins[i].get_producer() == null) ins[i].kill();
      end
   end
      
   foreach(outs[i]) begin
      if (outs[i].get_producer() == this) begin
         outs[i].set_producer(null);
         if (outs[i].get_consumer() == null) outs[i].kill();
      end
   end
      
   `foreach(this._vmm_available_xactor,i) begin
     if (this._vmm_available_xactor[i] == this) begin
        this._vmm_available_xactor.delete(i);
        break;
     end
   end

   this.log.kill();
endfunction: kill





`ifdef VMM_SB_DS_IN_STDLIB
function void vmm_xactor::inp_vmm_sb_ds(vmm_data tr);
   `foreach (this._vmm_sb_ds,i) begin
      if (this._vmm_sb_ds[i].is_in) begin
         this._vmm_sb_ds[i].sb.insert(tr);
      end
   end
endfunction: inp_vmm_sb_ds


function void vmm_xactor::exp_vmm_sb_ds(vmm_data tr);
   `foreach (this._vmm_sb_ds,i) begin
      if (this._vmm_sb_ds[i].is_out) begin
         case (this._vmm_sb_ds[i].order)
           vmm_sb_ds::IN_ORDER:
             this._vmm_sb_ds[i].sb.expect_in_order(tr);

           vmm_sb_ds::WITH_LOSSES: begin
              vmm_data p;
              vmm_data losses[];
              this._vmm_sb_ds[i].sb.expect_with_losses(tr, p, losses);
           end

           vmm_sb_ds::OUT_ORDER:
             this._vmm_sb_ds[i].sb.expect_out_of_order(tr);

         endcase
      end
   end
endfunction: exp_vmm_sb_ds


function void vmm_xactor::register_vmm_sb_ds(vmm_sb_ds             sb,
                                             vmm_sb_ds::kind_e     kind,
                                             vmm_sb_ds::ordering_e order = vmm_sb_ds::IN_ORDER);
   vmm_sb_ds_registration ds;

   `foreach (this._vmm_sb_ds,i) begin
      if (this._vmm_sb_ds[i].sb == sb) begin
         `vmm_warning(this.log, "Data stream scoreboard is already registered");
         return;
      end
   end

   if(sb == null) begin
     `vmm_error(this.log,"Trying to register null reference to register_vmm_sb_ds");
     return;
   end

   ds = new;
   ds.sb = sb;
   ds.is_in = (kind == vmm_sb_ds::INPUT ||
               kind == vmm_sb_ds::EITHER);
   ds.is_out = (kind == vmm_sb_ds::EXPECT ||
                kind == vmm_sb_ds::EITHER);
   ds.order = order;
   this._vmm_sb_ds.push_back(ds);
endfunction: register_vmm_sb_ds


function void vmm_xactor::unregister_vmm_sb_ds(vmm_sb_ds sb);
   `foreach (this._vmm_sb_ds,i) begin
      if (this._vmm_sb_ds[i].sb == sb) begin
         this._vmm_sb_ds.delete(i);
         return;
      end
   end

   `vmm_error(this.log, "Data stream scoreboard is not registered");
endfunction: unregister_vmm_sb_ds
`endif


function string vmm_xactor::do_psdisplay(string prefix = "");
   this.__vmm_done_user = 0;
   return "";
endfunction


function void vmm_xactor::do_start_xactor();
   this.__vmm_done_user = 0;
endfunction


function void vmm_xactor::do_stop_xactor();
   this.__vmm_done_user = 0;
endfunction


function void vmm_xactor::do_reset_xactor(vmm_xactor::reset_e rst_typ);
   this.__vmm_done_user = 0;
endfunction


function void vmm_xactor::do_kill_xactor();
   this.__vmm_done_user = 0;
endfunction


function vmm_xactor_iter::new(string  name = "",
                              string  inst = "");
   if (name == "") this.name = ".";
   else begin
      // Remove "/" surrounding the pattern, if any
      if (`vmm_str_match(name, "^/(.*)/$")) name = `vmm_str_backref(name, 0);
      this.name = name;
   end

   if (inst == "") this.inst = ".";
   else begin
      // Remove "/" surrounding the pattern, if any
      if (`vmm_str_match(inst, "^/(.*)/$")) inst = `vmm_str_backref(inst, 0);
      this.inst = inst;
   end

   void'(this.first());
endfunction: new


function void vmm_xactor_iter::move_iterator();
   string xa_name;
   string xa_inst;
`ifdef NO_STATIC_METHODS
   int n;

   if (_vmm_xactor == null) begin
      _vmm_xactor = new("vmm_xactor_iter::_vmm_xactor", "static");

      // Make sure it is the first one on the list of known transactors
      if (_vmm_xactor._vmm_available_xactor[0] == null) begin
         void'(_vmm_xactor._vmm_available_xactor.pop_back());
         _vmm_xactor._vmm_available_xactor[0] = _vmm_xactor;
      end
   end
   n = _vmm_xactor._vmm_available_xactor.size();
`else
   int n = vmm_xactor::_vmm_available_xactor.size();
`endif

   if (this.idx >= n || n <= 1) return;

   for (int x = this.idx+1; x < n; x++) begin
`ifdef NO_STATIC_METHODS
      xa_name = _vmm_xactor._vmm_available_xactor[x].log.get_name();
      xa_inst = _vmm_xactor._vmm_available_xactor[x].log.get_instance();
`else
      xa_name = vmm_xactor::_vmm_available_xactor[x].log.get_name();
      xa_inst = vmm_xactor::_vmm_available_xactor[x].log.get_instance();
`endif

      if (`vmm_str_match(xa_name, this.name) &&
          `vmm_str_match(xa_inst, this.inst)) begin
         this.idx = x;
         return;
      end
   end
   this.idx = 0;
endfunction


function vmm_xactor vmm_xactor_iter::xactor();
`ifdef NO_STATIC_METHODS
   if (_vmm_xactor == null) begin
      _vmm_xactor = new("vmm_xactor_iter::_vmm_xactor", "static");
   end
`endif

   if (this.idx <= 0 ||
`ifdef NO_STATIC_METHODS
       this.idx >= _vmm_xactor._vmm_available_xactor.size())
`else
       this.idx >= vmm_xactor::_vmm_available_xactor.size())
`endif
     return null;

`ifdef NO_STATIC_METHODS
   return _vmm_xactor._vmm_available_xactor[this.idx];
`else
   return vmm_xactor::_vmm_available_xactor[this.idx];
`endif
endfunction


function vmm_xactor vmm_xactor_iter::first();
   this.idx = 0;
   this.move_iterator();
   return this.xactor();
endfunction  

  
function vmm_xactor vmm_xactor_iter::next();
   this.move_iterator();
   return this.xactor();
endfunction  
