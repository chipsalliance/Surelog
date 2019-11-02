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
class vmm_notification_config;
   event      the_event;	
   bit        the_event_bit; //for ON_OFF_TRIGGERING (1:ON, 0:OFF)
   time       stamp;
   int        n_waiting_for;
   event      reset;
   event      abort;
   vmm_notification watch;
   int unsigned     trig_mode;
   vmm_data         status;
   vmm_notify_callbacks cbs[$];
`ifdef VMM_SB_DS_IN_STDLIB
   vmm_sb_ds_registration _vmm_sb_ds[$];
`endif
endclass


function vmm_notify::new(vmm_log log);
`ifdef VMM_NOTIFY_BASE_NEW_CALL
   super.new(`VMM_NOTIFY_BASE_NEW_CALL);
`endif

   this.log = log;
endfunction

function void vmm_notify::display(string prefix = "");
   $write(this.psdisplay(prefix), "\n");
endfunction

function string vmm_notify::psdisplay(string prefix = "");
   int i, ok;
   $sformat(psdisplay, "%sConfigured%s: [",
            prefix, (log == null) ? "" : `vmm_sformatf(" in %s(%s)",
                                                       log.get_name(),
                                                       log.get_instance()));
   for (ok = this.configs.first(i); 
        ok;
        ok = this.configs.next(i)) begin
      $sformat(psdisplay, "%0s %0d", psdisplay, i);
   end
   psdisplay = {psdisplay, "]"};
endfunction: psdisplay

   
function vmm_notify vmm_notify::copy(vmm_notify to = null);
   int i, ok;

   if (to == null) to = new(this.log);

   to.last_notification_id = this.last_notification_id;
   for (ok = this.configs.first(i); ok;
        ok = this.configs.next(i)) begin

      vmm_notification_config cfg = new;

      cfg.trig_mode     = this.configs[i].trig_mode;
      cfg.stamp         = 0;
      cfg.status        = null;
      cfg.n_waiting_for = 0;
      cfg.watch         = null;
      to.configs[i] = cfg;
   end

   return to;
endfunction : copy

   
function int vmm_notify::configure(int notification_id = -1,
     			           sync_e sync = ONE_SHOT);

   // Warn if an event is being re-configured
   if (this.configs.exists(notification_id))
   begin
      if (log == null) begin
         $write("vmm_notify::WARNING: Reconfiguring notification #%0d...\n",
                notification_id);
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV))
      begin
         string txt;
         $sformat(txt, "Reconfiguring notification #%0d...", notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
   end
   else if (notification_id > 1_000_000)
   begin
      // New notification ID > 1,000,000 are reserved
      if (log == null) begin
         $write("vmm_notify::FATAL: Notification notification IDs > 1,000,000 are reserved\n");
         $finish();
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         void'(this.log.text("Notification notification IDs > 1,000,000 are reserved"));
         this.log.end_msg();
      end
      return -1;
   end

   // Automatically generate a unique notification ID if notification ID
   // is not positive.
   if (notification_id < 0)
   begin
      last_notification_id++;
      notification_id  = last_notification_id;
   end
   configure = notification_id;

`ifdef VMM_DETAILED_MSGS
   if (this.log == null) begin
      $write("vmm_notify::DEBUG: Configuring notification notification #%0d...\n", notification_id);
   end
   else if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
      string txt;
      $sformat(txt, "Configuring notification notification #%0d...", notification_id);
      void'(this.log.text(txt));
      this.log.end_msg();
   end
`endif

   begin
      vmm_notification_config cfg = new;

      cfg.trig_mode     = sync;
      cfg.stamp         = 0;
      cfg.status        = null;
      cfg.n_waiting_for = 0;
      cfg.the_event_bit = 0; 

      this.configs[notification_id] = cfg;
   end
endfunction: configure   

   
function int vmm_notify::is_configured(int notification_id);
   if (!this.configs.exists(notification_id)) return 0;

   is_configured = this.configs[notification_id].trig_mode;
endfunction: is_configured


function bit vmm_notify::is_on(int notification_id);
   vmm_notification_config cfg;
       
   if (!this.configs.exists(notification_id))
   begin
      if (this.log == null) begin
         $write("vmm_notify::FATAL: Checking undefined notification #%0d\n",
                notification_id);
         $finish();
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         string txt;
         $sformat(txt, "Checking undefined notification #%0d", notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return 0;
   end

   cfg = this.configs[notification_id];
       
   if (cfg.trig_mode != ON_OFF) begin
      if (this.log == null) begin
         $write("vmm_notify::WARNING: Cannot check non-ON_OFF notification #%0d\n",
                notification_id);
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV)) begin
         string txt;
         $sformat(txt, "Cannot check non-ON_OFF notification #%0d", notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return 0;
   end

   is_on = cfg.the_event_bit;
endfunction: is_on

   
task vmm_notify::wait_for(int notification_id);
   vmm_notification_config cfg;
       
   if (!this.configs.exists(notification_id))
   begin
      if (this.log == null) begin
         $write("vmm_notify::FATAL Waiting for undefined notification #%0d\n",
                notification_id);
         $finish();
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         string txt;
         $sformat(txt, "Waiting for undefined notification #%0d", notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
   
      return;
   end

   cfg = this.configs[notification_id];
       
   cfg.n_waiting_for++;
   case(cfg.trig_mode)
      ON_OFF   : while (cfg.the_event_bit !== 1) begin
                                 @(cfg.the_event);
                              end
      ONE_SHOT : @(cfg.the_event);
      BLAST    : wait (cfg.the_event.triggered); 
      default  : begin
         if (this.log == null) begin
            $write("Invalid notification type\n");
         end else `vmm_fatal(this.log, "Invalid notification type");
      end
   endcase
   if (cfg.n_waiting_for > 0) cfg.n_waiting_for--;
endtask: wait_for


task vmm_notify::wait_for_off(int notification_id);
   vmm_notification_config cfg;
       
   if (!this.configs.exists(notification_id))
   begin
      if (this.log == null) begin
         $write("vmm_notify::FATAL: Waiting for undefined notification #%0d\n",
                notification_id);
         $finish();
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         string txt;
         $sformat(txt, "Waiting for undefined notification #%0d", notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return;
   end

   cfg = this.configs[notification_id];
       
   cfg.n_waiting_for++;
   case(cfg.trig_mode)
      ON_OFF  : while (cfg.the_event_bit !== 0) begin
                   @(cfg.the_event);
                end
      default : begin
         if (this.log == null) begin
            $write("Cannot use vmm_notify::wait_for_off() on non-ON/OFF notification\n");
         end else `vmm_fatal(this.log, "Cannot use vmm_notify::wait_for_off() on non-ON/OFF notification");
      end
   endcase
   if (cfg.n_waiting_for > 0) cfg.n_waiting_for--;
endtask: wait_for_off


function bit vmm_notify::is_waited_for(int notification_id);
   vmm_notification_config cfg;
       
   if (!this.configs.exists(notification_id))
   begin
      if (this.log == null) begin
         $write("vmm_notify::FATAL: is_waited_for() called for undefined notification #%0d\n",
     	   notification_id);
         $finish();
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         string txt;
         $sformat(txt, "vmm_notify::is_waited_for called for undefined notification #%0d",
     	     notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
     	 
      return 0;
   end

   cfg = this.configs[notification_id];

   is_waited_for = (cfg.n_waiting_for > 0);
endfunction: is_waited_for

   
function void vmm_notify::terminated(int notification_id);
   vmm_notification_config cfg;
       
   if (!this.configs.exists(notification_id))
   begin
      if (this.log == null) begin
         $write("vmm_notify::FATAL: terminated() called for undefined notification #%0d\n",
     	   notification_id);
         $finish();
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         string txt;
         $sformat(txt, "vmm_notify::terminated called for undefined notification #%0d",
     	     notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return;
   end

   cfg = this.configs[notification_id];

   if (cfg.n_waiting_for > 0) cfg.n_waiting_for--;
endfunction: terminated 

function vmm_data vmm_notify::status(int notification_id);
   vmm_notification_config cfg;
       
   if (!this.configs.exists(notification_id))
   begin
      if (this.log == null) begin
         $write("vmm_notify::FATAL: Requesting status for undefined notification #%0d\n",
     	   notification_id);
         $finish();
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         string txt;
         $sformat(txt, "Requesting status for undefined notification #%0d",
     	     notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return null;
   end

   cfg = this.configs[notification_id];
       
   status = cfg.status;
endfunction: status

function time vmm_notify::timestamp(int notification_id);
   vmm_notification_config cfg;
       
   if (!this.configs.exists(notification_id))
   begin
      if (this.log == null) begin
         $write("vmm_notify::FATAL: Requesting timestamp for undefined notification #%0d\n",
     	   notification_id);
         $finish();
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         string txt;
         $sformat(txt, "Requesting timestamp for undefined notification #%0d",
     	     notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return 0;
   end

   cfg = this.configs[notification_id];
       
   timestamp = cfg.stamp;
endfunction: timestamp

function void vmm_notify::indicate(int notification_id,
                 		   vmm_data status = null);
   vmm_notification_config cfg;
       
   if (!this.configs.exists(notification_id))
   begin
      if (this.log == null) begin
         $write("vmm_notify::FATAL: Indicating undefined notification #%0d\n",
     	   notification_id);
         $finish();
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         string txt;
         $sformat(txt, "Indicating undefined notification #%0d",
     	     notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return;
   end

   cfg = this.configs[notification_id];

   if (cfg.trig_mode == ON_OFF) cfg.the_event_bit = 1;
   -> cfg.the_event;
     	 
   cfg.stamp  = $realtime;
   cfg.status = status;

   `foreach (cfg.cbs,i) begin
      cfg.cbs[i].indicated(status);
   end

`ifdef VMM_SB_DS_IN_STDLIB
   `foreach (cfg._vmm_sb_ds,i) begin
      if (cfg._vmm_sb_ds[i].is_in) begin
         cfg._vmm_sb_ds[i].sb.insert(status);
      end

      if (cfg._vmm_sb_ds[i].is_out) begin
         case (cfg._vmm_sb_ds[i].order)
           vmm_sb_ds::IN_ORDER:
             cfg._vmm_sb_ds[i].sb.expect_in_order(status);
           
           vmm_sb_ds::WITH_LOSSES: begin
              vmm_data p;
              vmm_data losses[];
              cfg._vmm_sb_ds[i].sb.expect_with_losses(status, p, losses);
           end
           
           vmm_sb_ds::OUT_ORDER:
             cfg._vmm_sb_ds[i].sb.expect_out_of_order(status);
           
         endcase
      end
   end
`endif
endfunction: indicate


function void vmm_notify::set_notification(int          notification_id,
 				              vmm_notification ntfy = null);
   vmm_notification_config cfg;
       
   if (!this.configs.exists(notification_id))
   begin
      if (this.log == null) begin
         $write("vmm_notify::FATAL: Setting notification on undefined notification #%0d\n",
                notification_id);
         $finish();
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         string txt;
         $sformat(txt, "Setting notification on undefined notification #%0d", notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return;
   end

   cfg = this.configs[notification_id];

   // Was there an event before?
   if (cfg.watch != null)
   begin
      // Terminate it
      ->cfg.abort;
   end
   if (ntfy == null)
   begin
      cfg.watch = null;
      return;
   end

   // Watch for the specified event
   cfg.watch = ntfy;
   fork
      begin
         fork
            while (1)
            begin
               fork
          	  while (1)
                  begin
          	     vmm_data status;
          	     ntfy.indicate(status);
          	     this.indicate(notification_id, status);
          	  end
                  
                  while (cfg.trig_mode == ON_OFF) // persistent?
                  begin
          	     ntfy.reset();
          	     cfg.the_event_bit = 0;
                     -> cfg.the_event;
          	  end
               join_none
                  
               @(cfg.reset);
               disable fork;
            end
         join_none
            
         @(cfg.abort);
         disable fork;
      end
   join_none
endfunction: set_notification

   
function vmm_notification vmm_notify::get_notification(int notification_id);
   if (!this.configs.exists(notification_id))
   begin
      if (this.log == null) begin
         $write("vmm_notify::FATAL: Requesting notification for undefined notification #%0d\n",
     	   notification_id);
         $finish();
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         string txt;
         $sformat(txt, "Requesting notification for undefined notification #%0d",
     	     notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return null;
   end

   get_notification = this.configs[notification_id].watch;
endfunction: get_notification


function void vmm_notify::reset(int     notification_id = -1,
                                reset_e rst_typ = SOFT);
   vmm_notification_config cfg;
       
   if (notification_id < 0)
   begin
      int i, ok;

      for (ok = this.configs.first(i); ok; ok = this.configs.next(i))
      begin
         cfg = this.configs[i];
     		
         if (cfg.trig_mode == ON_OFF) begin
            cfg.the_event_bit = 0;
            ->cfg.the_event;
         end

         if (cfg.watch != null)
         begin
            ->cfg.reset;
            if (rst_typ == HARD)
            begin
     	  ->cfg.abort;
     	  cfg.watch = null;
            end
         end

         if (rst_typ == HARD)
         begin
            cfg.stamp  = 0;
            cfg.status = null;
            cfg.n_waiting_for = 0;
         end
      end
      return;
   end

   if (!this.configs.exists(notification_id))
   begin
      if (this.log == null) begin
         $write("vmm_notify::FATAL: Reseting undefined notification #%0d\n",
                notification_id);
         $finish();
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         string txt;
         $sformat(txt, "Reseting undefined notification #%0d", notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return;
   end

   cfg = this.configs[notification_id];
   ->cfg.the_event;
   cfg.the_event_bit = 0;
   if (cfg.watch != null)
   begin
      ->cfg.reset;
      if (rst_typ == HARD)
      begin
         ->cfg.abort;
         cfg.watch = null;
      end
   end

   if (rst_typ == HARD)
   begin
      cfg.stamp = 0;
      cfg.status = null;
      cfg.n_waiting_for = 0;
   end
endfunction: reset


function void vmm_notify::append_callback(int                  notification_id,
                                          vmm_notify_callbacks cbs);
   if (!this.configs.exists(notification_id))
   begin
      if (log == null) begin
         $write("vmm_notify::ERROR: Unknown notification #%0d to append callback to.\n",
                notification_id);
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV))
      begin
         string txt;
         $sformat(txt, "Unkown notification #%0d to append callback to.",
                  notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return;
   end

   // Append new callback
   this.configs[notification_id].cbs.push_back(cbs);

endfunction: append_callback


function void vmm_notify::unregister_callback(int                  notification_id,
                                              vmm_notify_callbacks cbs);
   if (!this.configs.exists(notification_id))
   begin
      if (log == null) begin
         $write("vmm_notify::ERROR: Unknown notification #%0d to remove callback from.\n",
                notification_id);
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV))
      begin
         string txt;
         $sformat(txt, "Unkown notification #%0d to remove callback from.",
                  notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return;
   end

   begin
      vmm_notification_config cfg = this.configs[notification_id];
      `foreach(cfg.cbs,i) begin
         if (cfg.cbs[i] == cbs) begin
            // Unregister it
            cfg.cbs.delete(i);
            return;
         end
      end
   end

   if (log == null) begin
      $write("vmm_notify::WARNING: Callback was not registered with notification #%0d.\n",
             notification_id);
   end
   else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV))
   begin
      string txt;
      $sformat(txt, "Callback was not registered with notification #%0d.",
               notification_id);
      void'(this.log.text(txt));
      this.log.end_msg();
   end
endfunction: unregister_callback


  



`ifdef VMM_SB_DS_IN_STDLIB
function void vmm_notify::register_vmm_sb_ds(int                   notification_id,
                                             vmm_sb_ds             sb,
                                             vmm_sb_ds::kind_e     kind,
                                             vmm_sb_ds::ordering_e order= vmm_sb_ds::IN_ORDER);
   vmm_sb_ds_registration ds;

   if (!this.configs.exists(notification_id))
   begin
      if (log == null) begin
         $write("vmm_notify::ERROR: Unknown notification #%0d to append callback to.\n",
                notification_id);
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV))
      begin
         string txt;
         $sformat(txt, "Unkown notification #%0d to append callback to.",
                  notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return;
   end

   if(sb == null)
   begin
     `vmm_error(this.log, "Trying to register null reference to register_vmm_sb_ds");
     return;
   end

   `foreach (this.configs[notification_id]._vmm_sb_ds,i) begin
      if (this.configs[notification_id]._vmm_sb_ds[i].sb == sb) begin
         `vmm_warning(this.log, "Data stream scoreboard is already registered");
         return;
      end
   end

   ds = new;
   ds.sb = sb;
   ds.is_in = (kind == vmm_sb_ds::INPUT ||
               kind == vmm_sb_ds::EITHER);
   ds.is_out = (kind == vmm_sb_ds::EXPECT ||
                kind == vmm_sb_ds::EITHER);
   ds.order = order;
   this.configs[notification_id]._vmm_sb_ds.push_back(ds);
endfunction: register_vmm_sb_ds


function void vmm_notify::unregister_vmm_sb_ds(int                   notification_id,
                                               vmm_sb_ds sb);
   if (!this.configs.exists(notification_id))
   begin
      if (log == null) begin
         $write("vmm_notify::ERROR: Unknown notification #%0d to remove callback from.\n",
                notification_id);
      end
      else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV))
      begin
         string txt;
         $sformat(txt, "Unkown notification #%0d to remove callback from.",
                  notification_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return;
   end

   `foreach (this.configs[notification_id]._vmm_sb_ds,i) begin
      if (this.configs[notification_id]._vmm_sb_ds[i].sb == sb) begin
         this.configs[notification_id]._vmm_sb_ds.delete(i);
         return;
      end
   end


   if (log == null) begin
      $write("vmm_notify::WARNING: Scoreboard was not registered with notification #%0d.\n",
             notification_id);
   end
   else if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV))
   begin
      string txt;
      $sformat(txt, "Scoreboard was not registered with notification #%0d.",
               notification_id);
      void'(this.log.text(txt));
      this.log.end_msg();
   end
endfunction: unregister_vmm_sb_ds
`endif
