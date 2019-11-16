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


function vmm_broadcast::new(string      name,
                            string      inst,
                            vmm_channel source,
                            bit         use_references=1,
                            int         mode=AFAP
                            `VMM_XACTOR_NEW_EXTERN_ARGS);
   super.new(name, inst, -1 `VMM_XACTOR_NEW_CALL);
   
   if (source == null) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text("Cannot create vmm_broadcast instance with a NULL source channel reference"));
         this.log.end_msg();
      end
   end

   this.in_chan       = source;
   this.log.is_above(this.in_chan.log);
   this.dflt_use_refs = use_references;
   this.mode          = mode;

   this.n_out_chans = 0;
endfunction : new


function string vmm_broadcast::psdisplay(string prefix = "");
   psdisplay = super.psdisplay(prefix);
   $sformat(psdisplay, "%s [Mode: %s]", psdisplay,
            (this.mode == ALAP) ? "ALAP" : "AFAP");
   $sformat(psdisplay, "%s\n%sInpChan: %s(%s) [level=%0d of %0d]",
            psdisplay, prefix, this.in_chan.log.get_name(),
            this.in_chan.log.get_instance(), this.in_chan.level(),
            this.in_chan.full_level());
   `foreach (this.out_chans,i) begin
      $sformat(psdisplay, "%s\n%sOutChan[%0d/%s/%s]: %s(%s) [level=%0d of %0d]",
               psdisplay, prefix, i, (this.is_on[i]) ? "ON " : "OFF",
               (this.use_refs[i]) ? "ref" : "cpy",
               this.out_chans[i].log.get_name(),
               this.out_chans[i].log.get_instance(), this.out_chans[i].level(),
               this.out_chans[i].full_level());
   end
   return psdisplay;
endfunction


task vmm_broadcast::broadcast_mode(bcast_mode_e mode);
   if (mode != AFAP && mode != ALAP) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text(`vmm_sformatf("Invalid broadcast mode %0d", mode)));
         this.log.end_msg();
      end
      return;
   end
   
   this.mode = mode;
   // This MAY create the opportunity for a new broadcast cycle...
   -> this.new_cycle;
endtask : broadcast_mode


function int vmm_broadcast::new_output(vmm_channel channel,
                                       logic use_references=1'bx);
   int     chan_id = this.n_out_chans++;
   
   if(channel == null) begin
     `vmm_error(this.log,"Null argument provided to vmm_broadcast::new_output");
     return 0;
   end

   this.out_chans.push_back(channel);
   this.is_on.push_back(1);
   this.use_refs.push_back((use_references === 1'bx) ?
                           this.dflt_use_refs : use_references);


   // Trigger a new broadcasting cycle whenever the channel becomes
   // empty while it is ON
   fork
      while (1) begin
         // A new (presumably empty) channel is added creates
         // a broadcast opportunity
         if (this.is_on[chan_id]) -> this.new_cycle;
         channel.notify.wait_for(vmm_channel::GOT);
      end
   join_none

   new_output = chan_id;
endfunction : new_output


function void vmm_broadcast::bcast_on(int unsigned output_id);
   this.bcast_on_off(output_id, 1);
endfunction: bcast_on   


function void vmm_broadcast::bcast_off(int unsigned output_id);
   this.bcast_on_off(output_id, 0);
endfunction: bcast_off


function void vmm_broadcast::bcast_on_off(int     channel_id,
                                          int     on_off);
   if (channel_id < 0 || channel_id >= this.n_out_chans) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP)) begin
         string txt;
         $sformat(txt, "Invalid output channel ID %0d", channel_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return;
   end

   this.is_on[channel_id] = on_off;

   // If a non-full channel is turned back on, this triggers a
   // new broadcasting cycle
   if (on_off && !this.out_chans[channel_id].is_full()) begin
      -> this.new_cycle;
   end

   // If a full channel is turned off, this triggers a
   // new broadcasting cycle
   if (!on_off && this.out_chans[channel_id].is_full()) begin
      -> this.new_cycle;
   end

   // Flush a channel that has been turned off
   if (!on_off) begin
      this.out_chans[channel_id].flush();
   end
endfunction: bcast_on_off


task vmm_broadcast::bcast_to_output(int     channel_id,
                                    int     on_off);
   this.bcast_on_off(channel_id, on_off);
endtask : bcast_to_output


function bit vmm_broadcast::add_to_output(int unsigned decision_id,
                                          int unsigned output_id,
                                          vmm_channel  channel,
                                          vmm_data     obj);
   add_to_output = 1;
endfunction : add_to_output


function void vmm_broadcast::start_xactor();
   super.start_xactor();
endfunction : start_xactor


function void vmm_broadcast::stop_xactor();
   super.stop_xactor();
endfunction : stop_xactor


function void vmm_broadcast::reset_xactor(vmm_xactor::reset_e rst_typ=SOFT_RST);
   super.reset_xactor(rst_typ);
   
   this.in_chan.flush();
   foreach (out_chans[i]) begin
      this.out_chans[i].flush();
   end
endfunction : reset_xactor


task vmm_broadcast::main();
   fork
      super.main();
      this.broadcast();
      this.sink_if_outs();
   join_none
endtask : main


task vmm_broadcast::broadcast();
   bit run_once = 1;
   
   while (1) begin
      int     decision_id = 0;
      int     i;
      int     go;
      
      vmm_data data, cpy;
      vmm_data obj;
      
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
         void'(this.log.text("Waiting for next broadcasting cycle..."));
         this.log.end_msg();
      end
      if (!run_once)  @ this.new_cycle;
      run_once = 0;
      this.wait_if_stopped();

      // OK to broadcast?
      case (this.mode) 

         AFAP: begin
            // OK to broadcast if just one active output channel
            // is not full
            int     i;

            go = 0;
            for (i = 0; i < this.n_out_chans; i++) begin
               if (this.is_on[i] && !this.out_chans[i].is_full()) begin
                  go = 1;
                  break;
               end
            end
         end
         
         ALAP: begin
            // OK to broadcast only if ALL active output channel
            // are not full
            int     i;
            
            go = 1;
            for (i = 0; i < this.n_out_chans; i++) begin
               if (this.is_on[i] && this.out_chans[i].is_full()) begin
                  go = 0;
                  break;
               end
            end
         end

         default: begin
            `vmm_error(this.log, `vmm_sformatf("Internal Error: Invalid broadcasting mode %0d!", this.mode));
            continue;
         end
      endcase
      // No go!
      if (!go) continue;
      
      this.wait_if_stopped();
      this.in_chan.get(data);
      this.wait_if_stopped();
       
`ifdef VMM_DETAILED_MSGS
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
         void'(this.log.text("New broadcasting cycle..."));
         this.log.end_msg();
      end
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::VERBOSE_SEV)) begin
         void'(this.log.text(data.psdisplay("Broadcasting:")));
         this.log.end_msg();
      end
`endif

      for (i = 0; i < this.n_out_chans; i++) begin
         if (this.is_on[i]) begin

            // Copy or reference?
            if (this.use_refs[i]) begin
                obj = data;
            end
            else begin
               // Minimize the number of copies made
               if (cpy == null) cpy = data.copy();
               obj = cpy;
            end
            
            if (this.add_to_output(decision_id++, i, this.out_chans[i], obj)) begin
               this.out_chans[i].sneak(obj);
`ifdef VMM_DETAILED_MSGS
               if (this.log.start_msg(vmm_log::INTERNAL_TYP,
                                      vmm_log::DEBUG_SEV)) begin
                  string msg;
                  $sformat(msg, "Broadcasted to output #%0d", i);
                  void'(this.log.text(msg));
                  this.log.end_msg();
               end
               if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::VERBOSE_SEV)) begin
                  void'(this.log.text(obj.psdisplay("Broadcasted:")));
                  this.log.end_msg();
               end
`endif
               // Mark the copy as having been used.
               if (!this.use_refs[i]) cpy = null;
            end
         end
      end
   end
endtask : broadcast 


task vmm_broadcast::sink_if_outs();
   bit sink;
   vmm_data unused_data;
   
   vmm_data temp_obj;
   // Sink the data from the source channel
   // if there are no active output channels
   while (1) begin
      int     i;

      // Wait for something to be in the source channel
      vmm_data peeked;
      this.in_chan.peek(peeked);

      // Can it go anywhere??
      sink = 1;
      for (i = 0; i < this.n_out_chans; i++) begin
         if (this.is_on[i]) begin
            sink = 0;
            break;
         end
      end

      // Sink it if there is nowhere to go and it has not
      // been removed by some other thread.
      this.in_chan.peek( temp_obj);
      if (sink && this.in_chan.level() > 0 &&
          temp_obj == peeked ) begin
         this.in_chan.get( unused_data);
      end

      if (in_chan.level() > 0) begin
         in_chan.notify.wait_for(vmm_channel::GOT);
      end
   end
endtask : sink_if_outs
