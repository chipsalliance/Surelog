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


function vmm_scheduler::new(string       name,
                            string       inst,
                            vmm_channel  destination,
                            int          instance_id = -1
                            `VMM_XACTOR_NEW_EXTERN_ARGS);
   super.new(name, inst, instance_id `VMM_XACTOR_NEW_CALL);
   
   if (destination == null) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text("Cannot create vmm_scheduler instance with a NULL destination channel reference"));
         this.log.end_msg();
      end
      return;
   end
   this.out_chan = destination;
   this.log.is_above(this.out_chan.log);

   this.randomized_sched = new;

   this.instance_id = instance_id;
   this.election_count = 0;
endfunction : new


function string vmm_scheduler::psdisplay(string prefix = "");
   psdisplay = super.psdisplay(prefix);
   $sformat(psdisplay, "%s\n%sOutChan: %s(%s) [level=%0d of %0d]",
            psdisplay, prefix, this.out_chan.log.get_name(),
            this.out_chan.log.get_instance(), this.out_chan.level(),
            this.out_chan.full_level());
   `foreach (this.sources,i) begin
      $sformat(psdisplay, "%s\n%sInChan[%0d/%s]: %s(%s) [level=%0d of %0d]",
               psdisplay, prefix, i, (this.is_on[i]) ? "ON " : "OFF",
               this.sources[i].log.get_name(),
               this.sources[i].log.get_instance(), this.sources[i].level(),
               this.sources[i].full_level());
   end
   return psdisplay;
endfunction


function int vmm_scheduler::new_source(vmm_channel channel);
   if (channel == null) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV)) begin
         void'(this.log.text("Attempting to add a NULL source channel"));
         this.log.end_msg();
      end
      return -1;
   end
   
   new_source = this.sources.size();
   
   this.sources.push_back(channel);
   this.is_on.push_back(1);
   if (channel.level() > 0) begin
      -> this.next_cycle;
   end

   // Watch for new additions to the newly added source
   // to potentially trigger new scheduling cycles
   fork 
      while (1) begin
         // The input channel may have been filled
         // before the forked thread has had a chance
         // to wait on the PUT indication
         if (channel.level() > 0) begin
            -> this.next_cycle;
         end
         channel.notify.wait_for(vmm_channel::PUT);
         -> this.next_cycle;
      end
   join_none 
  
endfunction : new_source


task vmm_scheduler::sched_from_input(int channel_id,
                                     int on_off);
   if (channel_id < 0 || channel_id >= this.sources.size()) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV)) begin
         string msg;
         $sformat(msg, "Invalid source channel ID specified in vmm_scheduler::sched_from_input(): %0d", channel_id);
         void'(this.log.text(msg));
         this.log.end_msg();
      end
      return;
   end

   this.is_on[channel_id] = on_off;

   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
      string msg;
      $sformat(msg, "Scheduling from channel #%0d turned %s", channel_id,
              (on_off) ? "ON" : "OFF");
      void'(this.log.text(msg));
      this.log.end_msg();
   end

   if (on_off && this.sources[channel_id].level() > 0) begin
      -> this.next_cycle;
   end
endtask : sched_from_input


task vmm_scheduler::schedule(output vmm_data     obj,
                             input  vmm_channel  sources[$],
                             input  int unsigned input_ids[$]);
   int     id;
   
   this.randomized_sched.instance_id = this.instance_id;
   this.randomized_sched.election_id = this.election_count++;
   this.randomized_sched.n_sources   = sources.size();
   this.randomized_sched.sources     = sources;
   this.randomized_sched.ids         = input_ids;

   // Round-robin scheduler  
   this.randomized_sched.next_idx = 0;
   if (this.randomized_sched.id_history.size() > 0) begin
      int last_id;
      // Find the next ID that follows (numerically) the last one
      // that was picked or use the first ID in the list of IDs.
      // Note: IDs will be stored in increasing numerical values.
      last_id = this.randomized_sched.id_history[$];
      foreach (input_ids[i]) begin
         if (input_ids[i] > last_id) begin
            this.randomized_sched.next_idx = i;
            break;
         end
      end
   end

   obj = null;
   if (!this.randomized_sched.randomize()) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text("Unable to randomize vmm_scheduler::randomized_sched"));
         this.log.end_msg();
      end
      return;
   end
   if (this.randomized_sched.source_idx < 0) return;

   if (this.randomized_sched.source_idx >= input_ids.size()) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text("vmm_scheduler::randomized_sched randomized to an invalid choice"));
         this.log.end_msg();
      end
      return;
   end
   
   id = input_ids[this.randomized_sched.source_idx];

   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
      string msg;
      $sformat(msg, "Scheduled data from source #%0d, offset %0d",
              id, this.randomized_sched.obj_offset);
      void'(this.log.text(msg));
      this.log.end_msg();
   end

   begin
      vmm_channel src = this.sources[id]; 
      if (src == null || src.level() == 0 ||
          src.level() <= this.randomized_sched.obj_offset) begin
         if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
            void'(this.log.text("vmm_scheduler::randomized_sched randomized to an invalid source"));
            this.log.end_msg();
         end
         return;
      end
      this.get_object(obj, src, id, this.randomized_sched.obj_offset);
   end

   this.randomized_sched.id_history.push_back(id);
   this.randomized_sched.obj_history.push_back(obj);
   if (this.randomized_sched.id_history.size() > 10) begin
      void'(this.randomized_sched.id_history.pop_front());
      void'(this.randomized_sched.obj_history.pop_front());
   end
endtask : schedule


task vmm_scheduler::get_object(output vmm_data     obj,
                               input  vmm_channel  source,
                               input  int unsigned input_id,
                               input  int          offset);
   obj = null;

   if (source == null) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text("vmm_scheduler::get_object called with invalid source"));
         this.log.end_msg();
      end
      return;
   end
   
   if (offset >= source.level()) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text("vmm_scheduler::get_object called with invalid offset"));
         this.log.end_msg();
      end
      return;
   end
   
   source.get( obj, offset);
endtask : get_object


function void vmm_scheduler::start_xactor();
   super.start_xactor();
   // This MAY cause a new scheduling cycle
   -> this.next_cycle;
endfunction : start_xactor


function void vmm_scheduler::stop_xactor();
   super.stop_xactor();
endfunction : stop_xactor


function void vmm_scheduler::reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);
   super.reset_xactor(rst_typ);
   
   this.out_chan.flush();
   `foreach (sources,i) begin
      this.sources[i].flush();
   end

   this.instance_id = instance_id;
   this.election_count = 0;

   if (rst_typ == HARD_RST ) begin
      this.randomized_sched = new;
   end
endfunction


task vmm_scheduler::main();
   fork
      super.main();
      this.schedule_cycle();
   join_none
endtask


task vmm_scheduler::schedule_cycle();
   vmm_data          data;
   vmm_channel       srcs[$];
   int unsigned      ids[$];
   
   while (1) begin
`ifdef VCS2006_06
      // Work-around for NYI feature in VCS2006.06
      // but IEEE 1800-2009 compliant
      srcs.delete();
      ids.delete();
`else
`ifdef INCA
      srcs.delete();
      ids.delete();
`else
      // Works in VCS2008.03 or later
      // IEEE 1800-2005 compliant
      srcs = '{};
      ids = '{};
`endif
`endif

      super.wait_if_stopped();

      // Identify all non-empty, active sources
      `foreach (this.sources,i) begin
         if (this.is_on[i] && this.sources[i] != null &&
             this.sources[i].level() > 0) begin
            srcs.push_back(this.sources[i]);
            ids.push_back(i);
         end
      end
      if (srcs.size() == 0) data = null;
      else this.schedule(data, srcs, ids);

      if (data == null) begin
         // Delay the next scheduling cycle until
         // A new channel is added, new data is put into
         // a channel, a channel is turned on or the scheduler
         // is restarted
         `vmm_trace(this.log, "Waiting for next scheduling cycle...");
         @ ( this.next_cycle);
         continue;
      end
      this.out_chan.put(data);
   end
endtask
   
