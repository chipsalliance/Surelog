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


// ToDo: Fill level based on bytes

function vmm_channel::new(string       name,
                          string       inst,
                          int unsigned full=1,
                          int unsigned empty=0,
                          bit          fill_as_bytes=1'b0);
`ifdef VMM_CHANNEL_BASE_NEW_CALL
   super.new(`VMM_CHANNEL_BASE_NEW_CALL);
`endif

  if (this.shared_log == null) begin
     this.one_log = _vmm_opts.get_bit("channel_shared_log",
                                      "All VMM channels share the same vmm_log instance");
     this.shared_log = new("VMM Channel", "[shared]");
  end

   if (this.one_log) this.log = shared_log;
   else this.log = new(name, inst);
   this.shared_log = this.log;

   this.notify = new(this.log);
   `VMM_OBJECT_SET_PARENT(this.notify, this)

   void'(this.notify.configure(FULL,  vmm_notify::ON_OFF));
   void'(this.notify.configure(EMPTY, vmm_notify::ON_OFF));
   void'(this.notify.configure(PUT));
   void'(this.notify.configure(GOT));
   void'(this.notify.configure(PEEKED));
   void'(this.notify.configure(ACTIVATED));
   void'(this.notify.configure(ACT_STARTED));
   void'(this.notify.configure(ACT_COMPLETED));
   void'(this.notify.configure(ACT_REMOVED));
   void'(this.notify.configure(LOCKED));
   void'(this.notify.configure(UNLOCKED));
   void'(this.notify.configure(GRABBED));
   void'(this.notify.configure(UNGRABBED));
   void'(this.notify.configure(RECORDING, vmm_notify::ON_OFF));
   void'(this.notify.configure(PLAYBACK, vmm_notify::ON_OFF));
   void'(this.notify.configure(PLAYBACK_DONE, vmm_notify::ON_OFF));

   if (full <= 0) full = 1;
   if (empty < 0 || empty > full) empty = full;

   this.full = full;
   this.empty = empty;
   this.is_sunk  = 0;

   this.active = null;
   this.active_status = INACTIVE;
   this.tee_on = 0;
   this.downstream = null;
   this.locks  = 2'b00;

   this.full_chan = 0;
   this.notify.indicate(EMPTY);

   this.iterator = 0;
   this.is_put = 0;
   this.is_playback = 0;
   this.record_fp = -1;

   //
   // Thread to manage connection requests
   //
   fork: connection_requests
      while (1)
      begin : new_while_loop
         vmm_data data = null;

         // Broken connection?
         if (this.downstream != null)
         begin
            if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV))
            begin
               string txt;
               txt = {"Channel connection established: ",
                      this.log.get_name(),
                      "(", this.log.get_instance(), ") -> ",
                      this.downstream.log.get_name(),
                      "(", this.downstream.log.get_instance(), ")"};

               void'(this.log.text(txt));
               this.log.end_msg();
            end // if debug level

            // Fork the data mover thread
            fork
               while (1)
               begin : inner_while_loop
                  // Simple blocking interface
                  data = null;
                  this.peek(data);
                  this.downstream.put(data);
                  if (this.data.size() > 0 && this.data[0] == data) this.get(data);
               end // inner_while_loop
            join_none
         end // if downstream != null

         // Wait for new connection requests
         @this.new_connection;

         // Stop the data mover thread
         disable fork;

         // Remove any datum that was forwarded
         // to the downstream channel but not removed
         // from this channel because of the blocking
         // model. Otherwise, the same datum will be
         // obtained from this channel twice.
         if (data != null) this.get(data);
     end // while (1)
   join_none // connection_requests
endfunction : new


function void vmm_channel::reconfigure(int   full=-1,
                                       int   empty=-1,
                                       logic fill_as_bytes=1'bx);
   if (full < 0) full = this.full;
   if (full == 0) full = 1;
   if (empty < 0) empty = this.empty;

   if (full < empty)
   begin
      `vmm_error(this.log, "Cannot reconfigure channel with FULL < EMPTY");
      return;
   end

   this.full = full;
   this.empty = empty;

   if (this.level() >= this.full)
   begin
      this.full_chan = 1;
      this.notify.indicate(FULL);
      this.notify.reset(EMPTY);
   end
   else if (this.level() <= this.empty)
   begin
      this.full_chan = 0;
      -> this.item_taken;
      this.notify.indicate(EMPTY);
      this.notify.reset(FULL);
   end
   else
   begin
      this.full_chan = 0;
      -> this.item_taken;
      this.notify.reset(EMPTY);
      this.notify.reset(FULL);
   end
endfunction: reconfigure


function int unsigned vmm_channel::full_level();
   full_level = this.full;
endfunction: full_level


function int unsigned vmm_channel::empty_level();
   empty_level = this.empty;
endfunction: empty_level


function int unsigned vmm_channel::level();
   level = this.data.size() + ((this.active == null) ? 0 : 1);
endfunction: level


function int unsigned vmm_channel::size();
   size = this.data.size() + ((this.active == null) ? 0 : 1);
endfunction : size


function bit vmm_channel::is_full();
   is_full = full_chan;
endfunction : is_full


function void vmm_channel::flush();
   vmm_data obj;
   if (this.downstream != null)
      this.downstream.flush();

`ifdef VCS2006_06
   // Work-around required by VCS 2006.06
   // but IEEE 1800-2009 compliant
   this.data.delete();
   this.tee_data.delete();
`else
`ifdef INCA
   this.data.delete();
   this.tee_data.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.data = '{};
   this.tee_data = '{};
`endif
`endif
   full_chan = 0;
   this.active = null;
   this.active_status = INACTIVE ;
   -> this.item_taken;
   this.notify.reset(FULL);
   this.notify.indicate(EMPTY);
endfunction: flush

`ifndef VMM_GRAB_DISABLED
function void vmm_channel::reset_grabbers();
 `ifdef VCS2006_06
   // Work-around required by VCS 2006.06
   // but IEEE 1800-2009 compliant
   this.grab_owners.delete();
`else
`ifdef INCA
   this.grab_owners.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.grab_owners = '{};
`endif
`endif
endfunction: reset_grabbers
`endif

function void vmm_channel::sink();
   this.flush();
   this.is_sunk = 1;
endfunction: sink


function void vmm_channel::flow();
   this.is_sunk = 0;
endfunction: flow


function void vmm_channel::reset();
   this.flush();
`ifndef VMM_GRAB_DISABLED
   this.reset_grabbers();
`endif
endfunction: reset


function void vmm_channel::lock(bit [1:0] who);
   this.locks |= who;
   this.notify.indicate(LOCKED);
endfunction: lock


function void vmm_channel::unlock(bit [1:0] who);
   this.locks &= ~who;
   this.notify.indicate(UNLOCKED);
   // May cause a consumer or producer to unblock
   -> this.item_taken;
   -> this.item_added;
endfunction: unlock


function bit vmm_channel::is_locked(bit [1:0] who);
   is_locked = (this.locks & who) ? 1 : 0;
endfunction: is_locked


`ifndef VMM_GRAB_DISABLED
function bit vmm_channel::check_grab_owners(`VMM_SCENARIO grabber);
   `VMM_SCENARIO current_parent;

   current_parent = grabber;

   while (current_parent != null) begin
      if (this.grab_owners[0] == current_parent) begin
         return 1;
      end
      current_parent = current_parent.get_parent_scenario();
   end
   return 0;
endfunction: check_grab_owners


function bit vmm_channel::check_all_grab_owners(`VMM_SCENARIO grabber);
   `foreach (this.grab_owners,i) begin
      if (grabber == this.grab_owners[i]) return 1;
   end
   return 0;
endfunction: check_all_grab_owners
`endif


function bit vmm_channel::try_grab(`VMM_SCENARIO grabber);
`ifndef VMM_GRAB_DISABLED
   if (this.notify.is_on(PLAYBACK)) begin
      `vmm_warning(this.log, "Cannot grab a channel during playback");
      return 0;
   end

   if (this.check_all_grab_owners(grabber)) begin
      `vmm_warning(this.log, "Cannot grab a channel that is already grabbed by you");
      return 0;
   end
   
   if ((this.grab_owners.size() == 0) ||
       (this.check_grab_owners(grabber))) begin
        this.grab_owners.push_front(grabber);
        this.notify.indicate(GRABBED);
      return 1;
   end

   return 0;
`else
   `vmm_error(this.log, "grab/ungrab functionality is not enabled");
`endif
endfunction: try_grab


task vmm_channel::grab(`VMM_SCENARIO grabber);
`ifndef VMM_GRAB_DISABLED
   if (this.notify.is_on(PLAYBACK)) begin
       this.notify.wait_for(vmm_channel::PLAYBACK_DONE);
   end

   if (this.grab_owners.size()==0) begin
      this.grab_owners.push_front(grabber);
      this.notify.indicate(GRABBED);
   end
   else begin
      if (this.check_all_grab_owners(grabber)) begin
         `vmm_error(this.log, "Cannot grab a channel that is already grabbed by you");
      end
      else if (this.check_grab_owners(grabber)) begin
         this.grab_owners.push_front(grabber);
         this.notify.indicate(GRABBED);
      end
      else begin
         this.notify.wait_for(vmm_channel::UNGRABBED);
         this.grab(grabber);
      end
   end
`else
   `vmm_error(this.log, "grab/ungrab functionality is not enabled");
`endif
endtask: grab


function void vmm_channel::ungrab(`VMM_SCENARIO grabber);
`ifndef VMM_GRAB_DISABLED
   if (this.grab_owners.size()==0) begin
      `vmm_error(this.log, "Cannot ungrab a channel that is not grabbed!");
   end
   else begin
      if (grabber == this.grab_owners[0]) begin
         void'(this.grab_owners.pop_front());
         this.notify.indicate(UNGRABBED);
      end
      else begin
         `vmm_error(this.log, "Cannot ungrab a channel that you did not grab!");
      end
   end
`else
   `vmm_error(this.log, "grab/ungrab functionality is not enabled");
`endif
endfunction: ungrab


function bit vmm_channel::is_grabbed();
`ifndef VMM_GRAB_DISABLED
   return (this.grab_owners.size() > 0);
`else
   `vmm_error(this.log, "grab/ungrab functionality is not enabled");
   return 0;
`endif
endfunction: is_grabbed


function void vmm_channel::display(string prefix="");
   $display(this.psdisplay(prefix));
endfunction: display


function string vmm_channel::psdisplay(string prefix="");
   $sformat(psdisplay, "%sChannel %s(%s): Level = %0d of %0d (empty=%0d)",
            prefix, this.log.get_name(), this.log.get_instance(),
            this.level(), this.full, this.empty);
   case (this.locks)
      SOURCE+SINK : psdisplay = {psdisplay, " [src+snk locked]"};
      SOURCE:       psdisplay = {psdisplay, " [src locked]"};
      SINK:         psdisplay = {psdisplay, " [snk locked]"};
   endcase
   if (this.is_sunk) psdisplay = {psdisplay, " (sunk)"};
`ifndef VMM_GRAB_DISABLED
   if (this.is_grabbed()) psdisplay = {psdisplay, " (grabbed by %s)",
                                       this.grab_owners[0].scenario_name(0)};
`endif

   `foreach(this.data,i) begin
      $sformat(psdisplay, "%s\n%s", psdisplay, this.data[i].psdisplay(`vmm_sformatf("%s   [%0d] ",
                                                                                    prefix, i)));
   end
endfunction: psdisplay


`ifndef VMM_GRAB_DISABLED
task vmm_channel::put(vmm_data obj,
                      int offset=-1,
                      `VMM_SCENARIO grabber=null);
`else
task vmm_channel::put(vmm_data obj,
                      int offset=-1);
`endif
   if (obj == null)
   begin
      `vmm_error(this.log, "Attempted to put null instance into channel");
      return;
   end // if obj == null
   sem.get();

   if (offset >= 0 && this.full_chan) begin
      `vmm_warning(this.log, `vmm_sformatf("Cannot put at offset %0d in a full channel. Will appends at the end.", offset));
      offset = -1;
   end

`ifndef VMM_GRAB_DISABLED
   this.block_producer(grabber);
   this.is_put = 1'b1;
   this.sneak(obj, offset, grabber);
   this.is_put = 1'b0;
   this.block_producer(grabber);
`else
   this.block_producer();
   this.is_put = 1'b1;
   this.sneak(obj, offset);
   this.is_put = 1'b0;
   this.block_producer();
`endif
   sem.put();
endtask: put


`ifndef VMM_GRAB_DISABLED
function void vmm_channel::sneak(vmm_data obj,
                                 int offset=-1,
                                 `VMM_SCENARIO grabber=null);
`else
function void vmm_channel::sneak(vmm_data obj,
                                 int offset=-1);
`endif
   string txt;
   time diff_time;

   if (obj == null)
   begin
      `vmm_error(this.log, "Attempted to sneak null instance into channel");
      return;
   end // obj == null

`ifndef VMM_GRAB_DISABLED
   if (this.grab_owners.size() &&
       (this.check_grab_owners(grabber) == 0)) begin
      `vmm_error(this.log, "Attempted to sneak in a grabbed channel from a scenario that is not a current grabber");
      return;
   end
`endif

   if (this.is_sunk == 0)
   begin

     if (offset == -1 || (offset == 0 && this.data.size() == 0))
     begin
        this.data.push_back(obj);
     end
     else
     begin
        int idx = this.index(offset, "sneak()");
        if (idx < 0) return;

        this.data.insert(offset, obj);
     end // if offset

     if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV))
     begin
       $sformat(txt, "New instance added to channel @%0d (level %0d of %0d/%0d)\n%s",
                offset, this.level(), this.full, this.empty,
                obj.psdisplay("    "));
        void'(this.log.text(txt));
        this.log.end_msg();
     end // if dbg

     this.notify.indicate(PUT, obj);

     if (this.level() >= this.full)
     begin
        this.full_chan = 1;
        this.notify.indicate(FULL);
     end

     if (this.level() > this.empty)
     begin
        this.notify.reset(EMPTY);
     end
   end
   else
   begin
     //To make sure process watching channel do not get affected by sunk
     this.notify.indicate(PUT, obj);
     this.notify.indicate(GOT, obj);
   end

   //recording
   if(this.notify.is_on(RECORDING))
   begin

     diff_time = $time - this.last_record_time;
     if(this.is_put == 1'b0)
       this.Xrecord_to_fileX(8'h02,offset,diff_time);
     else
       this.Xrecord_to_fileX(8'h01,offset,diff_time);

     //save object
     obj.save(this.record_fp);
     this.last_record_time = $time;
   end

   //Playback
   if(this.notify.is_on(PLAYBACK) && !this.is_playback)
   begin
     `vmm_warning(this.log,"vmm_channel::sneak accessed by source while playback is ON");
   end

   -> this.item_added;
endfunction: sneak


function vmm_data vmm_channel::unput(int offset=-1);

   time diff_time;

   if (this.size() == 0)
   begin
      `vmm_error(this.log, "Cannot unput from an empty channel");
      return null;
   end // if size == 0

   if (offset == -1)
   begin
     unput = this.data.pop_back();
   end
   else
   begin
     int idx = this.index(offset, "unput()");
     if (idx < 0)
     begin
        unput = null;
     end
     else
     begin
        unput = this.data[idx];
        this.data.delete(idx);
     end
   end // if offset != -1

   if (unput != null) begin
      this.notify.indicate(GOT, unput);
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV))
      begin
         string txt;
         $sformat(txt, "Instance unput from channel @%0d (level %0d of %0d/%0d)\n%s",
                  offset, this.level(), this.full, this.empty,
                  unput.psdisplay("    "));
         void'(this.log.text(txt));
         this.log.end_msg();
      end // if dbg_lvl

      //recording
      if(this.notify.is_on(RECORDING))
      begin
        diff_time = $time - this.last_record_time;
        this.Xrecord_to_fileX(8'h03,offset,diff_time);
        this.last_record_time = $time;
      end

   end

   this.unblock_producer();
endfunction: unput

function void vmm_channel::Xrecord_to_fileX(bit [7:0] op_code,
                                            int offset,
                                            time diff_time);

   bit [7:0] bytes[13];
   bit [63:0] bit_conv;

   bytes[0] = op_code;

   bit_conv[31:0] = offset;
   bytes[1] = bit_conv[7:0];
   bytes[2] = bit_conv[15:8];
   bytes[3] = bit_conv[23:16];
   bytes[4] = bit_conv[31:24];

   bit_conv[63:0] = diff_time;
   bytes[5] = bit_conv[7:0];
   bytes[6] = bit_conv[15:8];
   bytes[7] = bit_conv[23:16];
   bytes[8] = bit_conv[31:24];
   bytes[9] = bit_conv[39:32];
   bytes[10] = bit_conv[47:40];
   bytes[11] = bit_conv[55:48];
   bytes[12] = bit_conv[63:56];

   //<1byte type><4byte offset><8byte time>
   `foreach_sa(bytes,13,i) begin
     $fwrite(this.record_fp, "%c", bytes[i]);
   end
   //space
   if(op_code == 8'h03)
     $fwrite(this.record_fp, "\n");
   else
     $fwrite(this.record_fp, " ");

endfunction: Xrecord_to_fileX

function void vmm_channel::XgetX(output vmm_data obj,
                                 input  int      offset=0);
   this.X_getX(obj, offset);
   this.unblock_producer();
endfunction: XgetX

function void vmm_channel::X_getX(output vmm_data obj,
                                  input  int      offset=0);
   if (offset == 0)
   begin
      obj = this.data.pop_front();
   end
   else
   begin
      int idx = this.index(offset, "get()");
      if (idx < 0)
      begin
         obj = null;
      end
      else
      begin
         obj = this.data[idx];
         this.data.delete(idx);
      end // else if idx < 0
    end // else if offset

   if (obj != null)
   begin
      this.notify.indicate(GOT, obj);
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV))
      begin
         string txt;
         $sformat(txt, "New instance removed from channel @%0d (level %0d of %0d/%0d)\n%s",
                  offset, this.level(), this.full, this.empty,
                  obj.psdisplay("    "));
         void'(this.log.text(txt));
         this.log.end_msg();
      end // if dbg_lvl

      if (this.tee_on)
      begin
         this.tee_data.push_back(obj);
         -> this.teed;
      end // tee_on

`ifdef VMM_SB_DS_IN_STDLIB
      `foreach (this._vmm_sb_ds,i) begin
         if (this._vmm_sb_ds[i].is_in) begin
            this._vmm_sb_ds[i].sb.insert(obj);
         end

         if (this._vmm_sb_ds[i].is_out) begin
            case (this._vmm_sb_ds[i].order)
              vmm_sb_ds::IN_ORDER:
                this._vmm_sb_ds[i].sb.expect_in_order(obj);

              vmm_sb_ds::WITH_LOSSES: begin
                 vmm_data p;
                 vmm_data losses[];
                 this._vmm_sb_ds[i].sb.expect_with_losses(obj, p, losses);
              end

              vmm_sb_ds::OUT_ORDER:
                this._vmm_sb_ds[i].sb.expect_out_of_order(obj);

            endcase
         end
      end
`endif
   end // if obj != null
endfunction: X_getX

task vmm_channel::get(output vmm_data obj,
                      input  int      offset=0);
   this.block_consumer();
   this.XgetX(obj, offset);
endtask: get

task vmm_channel::peek(output vmm_data obj,
                       input  int      offset=0);
   string txt;
   int    idx;

   this.block_consumer();

   idx = this.index(offset, "peek()");
   if (idx < 0)
   begin
      obj = null;
   end
   else
   begin
      obj = this.data[idx];
   end

   if (obj != null)
   begin
      this.notify.indicate(PEEKED, obj);
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV))
      begin
         $sformat(txt, "New instance peeked from channel @%0d (level %0d of %0d/%0d)\n%s",
                  offset, this.level(), this.full, this.empty,
                  obj.psdisplay("    "));
         void'(this.log.text(txt));
         this.log.end_msg();
      end // if dbg_lvl
   end // obj != null

   this.unblock_producer();
endtask: peek


function vmm_data vmm_channel::try_peek(int offset = 0);
   string txt;
   int    idx;

   if (this.size() == 0 || this.is_locked(SINK)) return null;

   idx = this.index(offset, "try_peek()");
   if (idx < 0) return null;

   try_peek = this.data[idx];

   if (try_peek != null)
   begin
      this.notify.indicate(PEEKED, try_peek);
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV))
      begin
         $sformat(txt, "New instance peeked from channel @%0d (level %0d of %0d/%0d)\n%s",
                  offset, this.level(), this.full, this.empty,
                  try_peek.psdisplay("    "));
         void'(this.log.text(txt));
         this.log.end_msg();
      end
   end
endfunction: try_peek


task vmm_channel::activate(output vmm_data obj,
                           input  int      offset=0);
   string txt;

   // Empty the active slot
   if (active != null)
      void'(this.remove());

   while (this.size() == 0)
      @this.item_added;

   if (offset == 0)
   begin
      obj = this.data.pop_front();
   end
   else
   begin
      int idx = this.index(offset, "activate()");
      if (idx < 0)
      begin
        obj = null;
      end
      else
      begin
        obj = this.data[idx];
        this.data.delete(idx);
      end
   end // else if offset == 0


   if (obj != null)
   begin
      this.active = obj;
      this.active_status = PENDING ;
      this.notify.indicate(ACTIVATED, obj);
      this.notify.indicate(PEEKED, obj);

      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV))
      begin
         $sformat(txt, "New instance activated from channel @%0d (level %0d of %0d/%0d)\n%s",
                  offset, this.level(), this.full, this.empty,
                  obj.psdisplay("    "));
         void'(this.log.text(txt));
         this.log.end_msg();
      end // if dbg_lvl

      if (this.tee_on)
      begin
         this.tee_data.push_back(obj);
         -> this.teed;
      end
   end // if obj != null
endtask: activate


function vmm_data vmm_channel::active_slot();
   active_slot = this.active;
endfunction: active_slot


function vmm_data vmm_channel::start();
   if (this.active == null)
   begin
      `vmm_fatal(this.log, "Cannot start() without prior activate()");
      return null;
   end // if active == null

   if (this.active_status == STARTED)
   begin
      `vmm_warning(this.log, "Active slot already start()'ed");
   end // if STARTED

   this.active_status = STARTED;
   this.notify.indicate(ACT_STARTED, this.active);
   this.active.notify.indicate(vmm_data::STARTED);
   start = this.active;
endfunction: start


function vmm_data vmm_channel::complete(vmm_data status=null);
   if (this.active == null)
   begin
      `vmm_fatal(this.log, "Cannot complete() without prior activate()");
      return null;
   end
   if (this.active_status != STARTED)
   begin
      `vmm_warning(this.log, "complete() called without start()");
   end

   this.active_status = COMPLETED;
   this.notify.indicate(ACT_COMPLETED, this.active);
   this.active.notify.indicate(vmm_data::ENDED, status);
   complete = this.active;
endfunction: complete


function vmm_data vmm_channel::remove();
   if (this.active == null)
   begin
      `vmm_fatal(this.log, "Cannot remove() without prior activate()");
      return null;
   end

   // OK to remove if not started or completed
   if (this.active_status == STARTED)
   begin
      `vmm_warning(this.log, "remove() called without complete()");
   end

   this.notify.indicate(ACT_REMOVED, this.active);
   this.notify.indicate(GOT, this.active);
   if (this.active_status != COMPLETED)
   begin
      this.active.notify.indicate(vmm_data::ENDED);
   end
   this.active_status = INACTIVE;
   remove = this.active;
   this.active = null;

   this.unblock_producer();
endfunction: remove


function vmm_channel::active_status_e vmm_channel::status();
   status = this.active_status;
endfunction: status


function bit vmm_channel::tee_mode(bit is_on);
   string txt;
   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV))
   begin
      $sformat(txt, "tee branch turned %0s", (is_on) ? "ON" : "OFF");
      void'(this.log.text(txt));
      this.log.end_msg();
   end

   tee_mode = this.tee_on;
   this.tee_on = is_on;
endfunction: tee_mode


task vmm_channel::tee(output vmm_data obj);
   string txt;
   while (this.tee_data.size() == 0)
      @this.teed;

   obj = this.tee_data.pop_front();

   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV))
   begin
      $sformat(txt, "New instance teed from channel (level %0d of %0d/%0d)\n%s",
                  this.level(), this.full, this.empty,
                  obj.psdisplay("    "));
      void'(this.log.text(txt));
      this.log.end_msg();
   end
endtask: tee


function void vmm_channel::connect(vmm_channel downstream);
   // Do not disrupt an already-established connection
   if (this.downstream == downstream) return;

   // Indicate a new connection
   this.downstream = downstream;
   -> this.new_connection;
endfunction: connect


function vmm_data vmm_channel::for_each(bit reset=0);
   if (reset) this.iterator = 0;
   else this.iterator++;

   if (this.iterator >= this.data.size()) for_each = null;
   else for_each = this.data[this.iterator];
endfunction: for_each


function int unsigned vmm_channel::for_each_offset();
   for_each_offset = this.iterator;
endfunction: for_each_offset


function bit vmm_channel::record(string filename);
   if (filename == "")
   begin
      if(this.notify.is_on(RECORDING))
      begin
        $fclose(this.record_fp);
        this.notify.reset(RECORDING);
        return 1;
      end
      else
      begin
        `vmm_warning(this.log,"A valid 'filename' must be specified to start recording. vmm_channel::record() is ignoring call");
        return 0;
      end
   end
   else
   begin
     if(this.notify.is_on(RECORDING))
     begin
       `vmm_warning(this.log,"vmm_channel::record() is already started. Ignoring call");
       return 0;
     end
     else
     begin
       this.record_fp = $fopen(filename,"wb");
       if(this.record_fp == 0)
       begin
         `vmm_error(this.log,$psprintf("vmm_channel::record() is not able to open file: %s for recording",filename));
         this.record_fp = -1;
         return 0;
       end
       this.notify.indicate(RECORDING);
       this.last_record_time = $time;
       return 1;
     end
   end

endfunction: record

`ifndef VMM_GRAB_DISABLED
task vmm_channel::playback(output bit      success,
                           input  string   filename,
                           input  vmm_data factory,
                           input  bit      metered=0,
                           `VMM_SCENARIO   grabber=null);
`else
task vmm_channel::playback(output bit      success,
                           input  string   filename,
                           input  vmm_data factory,
                           input  bit      metered=0);
`endif
   int playback_fp;
   bit [7:0] bytes[14];
   bit [7:0] op_code;
   bit [63:0] bit_conv;
   int offset;
   time time_delay;
   int data_id = 0;

`ifndef VMM_GRAB_DISABLED
   if (this.grab_owners.size() &&
      (this.check_grab_owners(grabber) == 0)) begin
      `vmm_error(this.log, "Cannot playback on a grabbed channel");
      return;
   end
`endif

   this.notify.indicate(PLAYBACK);

   if(filename == "")
   begin
     success = 0;
     `vmm_error(this.log,"vmm_channel::playback() found null on input argument filename");
     this.notify.reset(PLAYBACK);
     this.notify.indicate(PLAYBACK_DONE);
     return;
   end

   if(factory == null)
   begin
     success = 0;
     `vmm_error(this.log,"vmm_channel::playback() found null on input argument factory");
     this.notify.reset(PLAYBACK);
     this.notify.indicate(PLAYBACK_DONE);
     return;
   end

   playback_fp = $fopen(filename,"rb");

   if(playback_fp == 0)
   begin
     success = 0;
     `vmm_error(this.log,$psprintf("vmm_channel::playback() can not open file %s: file does not exist",filename));
     this.notify.reset(PLAYBACK);
     this.notify.indicate(PLAYBACK_DONE);
     return;
   end

   if($feof(playback_fp))
   begin
     $fclose(playback_fp);
     success = 0;
     `vmm_error(this.log,$psprintf("vmm_channel::playback() file %s is empty",filename));
     this.notify.reset(PLAYBACK);
     this.notify.indicate(PLAYBACK_DONE);
     return;
   end

   success = 1;

   this.lock(SOURCE);

   while(!$feof(playback_fp))
   begin
     `foreach_sa(bytes,13,i)
     begin
       int c = $fgetc(playback_fp);
       bytes[i] = c;
     end

     if(bytes[0] == 8'hff)
       break;

     op_code    = bytes[0];
     offset     = {bytes[4],bytes[3],bytes[2],bytes[1]};
     time_delay = {bytes[12],bytes[11],bytes[10],bytes[9],bytes[8],bytes[7],bytes[6],bytes[5]};

     if(op_code == 8'h01)
     begin
       if(!factory.load(playback_fp))
       begin
         `vmm_error(this.log,"vmm_data::load() failed");
         success = 0;
         break;
       end
       factory.data_id = data_id++;

       if(metered)
       begin
         #time_delay;
         this.is_playback = 1'b1;
         // If channel was sunk too fast, do our best
         if (offset >= this.size()) offset = -1;
`ifndef VMM_GRAB_DISABLED
         this.sneak(factory.copy(), offset, grabber);
`else
         this.sneak(factory.copy(), offset);
`endif
         this.is_playback = 1'b0;
       end
       else
         while (this.full_chan) @this.item_taken;
        // If channel was sunk too fast, do our best
        if (offset >= this.size()) offset = -1;
        this.is_playback = 1'b1;
`ifndef VMM_GRAB_DISABLED
        this.sneak(factory.copy(), offset, grabber);
`else
        this.sneak(factory.copy(), offset);
`endif
        this.is_playback = 1'b0;
        while (this.full_chan) @this.item_taken;
     end
     else if(op_code == 8'h02)
     begin
       if(!factory.load(playback_fp))
       begin
         `vmm_error(this.log,"vmm_data::load() failed");
         success = 0;
         break;
       end
       factory.data_id = data_id++;

       if(metered)
         #time_delay;

       this.is_playback = 1'b1;
       // If channel was sunk too fast, do our best
       if (offset >= this.size()) offset = -1;
`ifndef VMM_GRAB_DISABLED
       this.sneak(factory.copy(),offset, grabber);
`else
       this.sneak(factory.copy(),offset);
`endif
       this.is_playback = 1'b0;
     end
     else if(op_code == 8'h03)
     begin
       if(metered)
         #time_delay;
         // If channel was sunk too fast, do our best
         if (offset >= this.size()) offset = -1;
       if(this.unput(offset) == null)
         `vmm_warning(this.log,"vmm_channel::playback() found improper offset for unput operation");
     end
     else
     begin
       `vmm_error(this.log,$psprintf("vmm_channel::playback() file %s is corrupted",filename));
       success = 0;
       break;
     end
   end

   $fclose(playback_fp);
   this.unlock(SOURCE);
   this.notify.reset(PLAYBACK);
   this.notify.indicate(PLAYBACK_DONE);

endtask: playback


function int vmm_channel::index(int    offset,
                                string from);
   string txt;
   index = offset;
   if (offset < 0) index += this.data.size() + offset + 1;
   if (index < 0 || index >= this.data.size())
   begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         $sformat(txt, "Invalid offset %0d specified in %s. Not in {0:%0d}.\n",
                  offset, from, this.data.size()-1);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      index = -1;
   end
endfunction: index


`ifndef VMM_GRAB_DISABLED
task vmm_channel::block_producer(`VMM_SCENARIO grabber);
    while (this.full_chan || this.is_locked(SOURCE) ||
          (this.grab_owners.size() &&
           (this.check_grab_owners(grabber) == 0))) begin
       fork
          begin
             if (this.grab_owners.size() &&
                 (this.check_grab_owners(grabber) == 0)) begin
                this.notify.wait_for(vmm_channel::UNGRABBED);
             end
          end
          begin
             if(this.full_chan || this.is_locked(SOURCE)) begin
                @this.item_taken;
             end
          end
       join
   end
`else
task vmm_channel::block_producer();
    while (this.full_chan || this.is_locked(SOURCE))
       @this.item_taken;
`endif
endtask : block_producer


task vmm_channel::block_consumer();
   while (this.size() == 0 || this.is_locked(SINK))
      @this.item_added;
endtask: block_consumer


function void vmm_channel::unblock_producer();
   if (this.level() <= this.empty)
   begin
      this.full_chan = 0;
      this.notify.indicate(EMPTY);
   end

   if (this.level() < this.full)
   begin
      this.notify.reset(FULL);
   end

   -> this.item_taken;
endfunction: unblock_producer


function vmm_xactor vmm_channel::get_producer();
   get_producer = this.producer;
endfunction: get_producer


function vmm_xactor vmm_channel::get_consumer();
   get_consumer = this.consumer;
endfunction: get_consumer


function void vmm_channel::set_producer(vmm_xactor producer);
   if (producer == null && this.producer == null) begin
      `vmm_error(this.log, "Attempted to set null producer");
      return;
   end

   if (this.producer == producer) return;
   
   if (this.producer != null) begin
      if(producer != null) begin
	 `vmm_warning(this.log, "Producer is already set");
      end
      `foreach(this.producer.Xoutput_chansX,i) begin  
	 if (this.producer.Xoutput_chansX[i] == this) begin
	    this.producer.Xoutput_chansX.delete(i);
    	    break;
	 end
      end
   end
   this.producer = producer;
   if(producer != null) begin
     this.producer.Xoutput_chansX.push_back(this);
   end
endfunction: set_producer


function void vmm_channel::set_consumer(vmm_xactor consumer);
   if (consumer == null && this.consumer == null) begin
      `vmm_error(this.log, "Attempted to set null consumer");
      return;
   end
   
   if (this.consumer == consumer) return;

   if (this.consumer != null) begin
      if (consumer != null) begin
	`vmm_warning(this.log, "Consumer is already set");
      end
      `foreach(this.consumer.Xinput_chansX,i) begin
	 if (this.consumer.Xinput_chansX[i] == this) begin
    	    this.consumer.Xinput_chansX.delete(i);
    	    break;
	 end
      end
   end
   this.consumer = consumer;
   if (consumer != null) begin
      this.consumer.Xinput_chansX.push_back(this);
   end
endfunction: set_consumer


function void vmm_channel::kill();
   if (this.consumer != null) begin
      `foreach(this.consumer.Xinput_chansX,i) begin
         if(this.consumer.Xinput_chansX[i] == this) begin
    	    this.consumer.Xinput_chansX.delete(i);
    	    break;
         end
      end
   end

   if (this.producer != null) begin
      `foreach(this.producer.Xoutput_chansX,i) begin  
         if (this.producer.Xoutput_chansX[i] == this) begin
	    this.producer.Xoutput_chansX.delete(i);
    	    break;
         end
      end
   end

   this.downstream = null;
   -> this.new_connection;

   this.producer = null;
   this.consumer = null;

   if (this.shared_log == null) this.log.kill();
endfunction: kill   





`ifdef VMM_SB_DS_IN_STDLIB
function void vmm_channel::register_vmm_sb_ds(vmm_sb_ds             sb,
                                              vmm_sb_ds::kind_e     kind,
                                              vmm_sb_ds::ordering_e order=vmm_sb_ds::IN_ORDER);
   vmm_sb_ds_registration ds;

   if(sb == null) begin
     `vmm_error(this.log, "Trying to register null scoreboard");
     return;
   end 

   `foreach (this._vmm_sb_ds,i) begin
      if (this._vmm_sb_ds[i].sb == sb) begin
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
   this._vmm_sb_ds.push_back(ds);
endfunction: register_vmm_sb_ds


function void vmm_channel::unregister_vmm_sb_ds(vmm_sb_ds sb);
   `foreach (this._vmm_sb_ds,i) begin
      if (this._vmm_sb_ds[i].sb == sb) begin
         this._vmm_sb_ds.delete(i);
         return;
      end
   end

   `vmm_error(this.log, "Data stream scoreboard is not registered");
endfunction: unregister_vmm_sb_ds
`endif

