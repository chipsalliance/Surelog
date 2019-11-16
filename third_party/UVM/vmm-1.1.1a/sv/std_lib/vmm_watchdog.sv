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


interface vmm_watchdog_port(input logic pin);
endinterface: vmm_watchdog_port


typedef class vmm_watchdog_sig;
typedef class vmm_watchdog_channel;
typedef class vmm_watchdog_xactor;


class vmm_watchdog extends `VMM_XACTOR;

   typedef enum {TIMEOUT} notifications_e;

   local vmm_watchdog_sig     sigs[$];
   local vmm_watchdog_xactor  xactors[$];
   local vmm_watchdog_channel channels[$];
   
   local int        fuse_length;
   local bit        run_fuse;
   local reg [63:0] fuse_lit;
   local event      new_fuse;
   local event      force_firing;

   static int n_busy = 0;


   extern function new(string                    inst,
                       virtual vmm_watchdog_port sigs = null,
                       int                       fuse = 1000
                       `VMM_XACTOR_NEW_ARGS);

   extern virtual function void reset_fuse(bit hold = 0);
   extern virtual function int fuse(int reset_fuse = -1);

   extern virtual function void start_xactor();
   extern virtual function void stop_xactor();
   extern virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);

   extern virtual function void watch_signal(virtual vmm_watchdog_port sig,
                                             string                    name);
   extern virtual function void unwatch_signal(virtual vmm_watchdog_port sig);
   
   extern virtual function void watch_xactor(vmm_xactor xact);
   extern virtual function void unwatch_xactor(vmm_xactor xact);
   
   extern virtual function void watch_channel(vmm_channel chan,
                                              bit         is_empty=1);
   extern virtual function void unwatch_channel(vmm_channel chan);

   extern function void display(string prefix = "");
   extern virtual function string psdisplay(string prefix = "");

   extern protected virtual task main();
endclass: vmm_watchdog



class vmm_watchdog_channel;
   vmm_channel   chan;
   vmm_watchdog  dog;
   event         abort;

   function new(vmm_channel  chan,
                vmm_watchdog dog,
                bit          is_empty=1);
      this.chan = chan;
      this.dog = dog;

      fork
      begin
         fork
            forever begin
               if(is_empty)
               begin
                 dog.n_busy++;
                 dog.reset_fuse(1);
                 chan.notify.wait_for(vmm_channel::EMPTY);
                 dog.n_busy--;
                 if (dog.n_busy == 0) dog.reset_fuse();
                 chan.notify.wait_for_off(vmm_channel::EMPTY);
               end
               else
               begin
                 if(dog.n_busy > 0) dog.n_busy--;
                 if(dog.n_busy == 0) dog.reset_fuse();
                 fork 
                    chan.notify.wait_for_t(chan.PUT);
                    chan.notify.wait_for_t(chan.GOT);
                    chan.notify.wait_for_t(chan.PEEKED);
                    chan.notify.wait_for_t(chan.ACTIVATED);
                    chan.notify.wait_for_t(chan.STARTED);
                    chan.notify.wait_for_t(chan.REMOVED);
                    chan.notify.wait_for_t(chan.COMPLETED);
                 join_any
                 disable fork;
                 dog.n_busy++;
                 dog.reset_fuse(1);
               end
            end
         join_none
         @(this.abort);
         disable fork;

         if (!chan.notify.is_on(vmm_channel::EMPTY)) begin
            dog.n_busy--;
            if (dog.n_busy == 0) dog.reset_fuse();
         end
      end
      join_none
   endfunction: new
endclass: vmm_watchdog_channel
   

class vmm_watchdog_xactor;
   vmm_xactor    xact;
   vmm_watchdog  dog;
   event abort;

   function new(vmm_xactor    xact,
                vmm_watchdog  dog);
      this.xact = xact;
      this.dog = dog;

      fork
      begin
         fork
            forever begin
               dog.n_busy++;
               dog.reset_fuse(1);
               xact.notify.wait_for(vmm_xactor::XACTOR_IDLE);
               dog.n_busy--;
               if (dog.n_busy == 0) dog.reset_fuse();
               xact.notify.wait_for_off(vmm_xactor::XACTOR_IDLE);
            end
         join_none
         @(this.abort);
         disable fork;

         if (!xact.notify.is_on(vmm_xactor::XACTOR_IDLE)) begin
            dog.n_busy--;
            if (dog.n_busy == 0) dog.reset_fuse();
         end
      end
      join_none
   endfunction: new
endclass: vmm_watchdog_xactor


function vmm_watchdog::new(string inst,
                           virtual vmm_watchdog_port sigs = null,
                           int                       fuse = 1000
                           `VMM_XACTOR_NEW_EXTERN_ARGS);
   super.new("Watchdog Timer", inst, -1 `VMM_XACTOR_NEW_CALL);
   
   void'(this.notify.configure(TIMEOUT, vmm_notify::ONE_SHOT));

   if (sigs != null) this.watch_signal(sigs, "(Unknown)");
   this.fuse_length = fuse;
   this.run_fuse = 1;
endfunction: new


function void vmm_watchdog::reset_fuse(bit hold = 0);
   if (hold) this.run_fuse = 0;
   else this.run_fuse = 1;
   -> this.new_fuse;
endfunction: reset_fuse


function int vmm_watchdog::fuse(int reset_fuse = -1);
   if ((^this.fuse_lit) === 1'bx) fuse = this.fuse_length;
   else fuse = this.fuse_length - ($time - this.fuse_lit);

   if (reset_fuse > 0) begin
      this.fuse_length = reset_fuse;
      -> this.new_fuse;
   end
   else if (reset_fuse == 0) begin
      -> this.force_firing;
   end
endfunction: fuse


function void vmm_watchdog::start_xactor();
   super.start_xactor();
endfunction: start_xactor


function void vmm_watchdog::stop_xactor();
   this.reset_xactor();
endfunction: stop_xactor


function void vmm_watchdog::reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);
   super.reset_xactor(rst_typ);

   if (rst_typ == HARD_RST) begin
      this.reset_fuse();
`ifdef VCS2006_06
      // Work-around for NYI feature in VCS2006.06
      // but IEEE 1800-2009 compliant
      this.sigs.delete();
      this.xactors.delete();
      this.channels.delete();
`else
`ifdef INCA
      this.sigs.delete();
      this.xactors.delete();
      this.channels.delete();
`else
      // Works in VCS2008.03 or later
      // IEEE 1800-2005 compliant
      this.sigs = '{};
      this.xactors = '{};
      this.channels = '{};
`endif
`endif
   end
endfunction: reset_xactor


function void vmm_watchdog::watch_xactor(vmm_xactor xact);
   if (xact == null) return;

   // Is the xactor already watched?
   `foreach (this.xactors,i) begin
      if (this.xactors[i].xact == xact) begin
         `vmm_warning(this.log, "Transactor is already watched");
         return;
      end
   end

   begin
      vmm_watchdog_xactor wx = new(xact, this);
      this.xactors.push_back(wx);
   end
endfunction: watch_xactor


function void vmm_watchdog::unwatch_xactor(vmm_xactor xact);
   if (xact == null) return;

   // Is the xactor watched?
   `foreach (this.xactors,i) begin
      if (this.xactors[i].xact == xact) begin
         -> this.xactors[i].abort;
         this.xactors.delete(i);
         return;
      end
   end
   `vmm_warning(this.log, "Transactor is not watched");
endfunction: unwatch_xactor


function void vmm_watchdog::watch_channel(vmm_channel chan,
                                          bit         is_empty=1);
   if (chan == null) return;

   // Is the channel already watched?
   `foreach (this.channels,i) begin
      if (this.channels[i].chan == chan) begin
         `vmm_warning(this.log, "Channel is already watched");
         return;
      end
   end

   begin
      vmm_watchdog_channel wc = new(chan, this, is_empty);
      this.channels.push_back(wc);
   end
endfunction: watch_channel


function void vmm_watchdog::unwatch_channel(vmm_channel chan);
   if (chan == null) return;

   // Is the channel watched?
   `foreach (this.channels,i) begin
      if (this.channels[i].chan == chan) begin
         -> this.channels[i].abort;
         this.channels.delete(i);
         return;
      end
   end
   `vmm_warning(this.log, "Channel is not watched");
endfunction: unwatch_channel


function void vmm_watchdog::display(string prefix = "");
   $write(this.psdisplay(prefix), "\n");
endfunction: display


function string vmm_watchdog::psdisplay(string prefix = "");
   psdisplay = "";
   if (this.sigs.size() > 0) begin
      bit [63:0] whence = $time;
      if (whence > this.fuse_length) whence -= this.fuse_length;
      else whence = 0;
      
      $sformat(psdisplay, "%sWatched signals:", prefix);
      `foreach (this.sigs,i) begin
         $sformat(psdisplay, "%s\n%s   %s %s", psdisplay, prefix,
                  (whence > this.sigs[i].stamp) ? " IDLE " : "ACTIVE", this.sigs[i].name);
      end
   end

   if (this.channels.size() > 0) begin
      if (psdisplay.len() > 0) $sformat(psdisplay, "%s\n", psdisplay);
      $sformat(psdisplay, "%s%sWatched channels:", psdisplay, prefix);
      `foreach (this.channels,i) begin
         if (this.channels[i].chan.notify.is_on(vmm_channel::EMPTY)) begin
            $sformat(psdisplay, "%s\n%s   EMPTY    ", psdisplay, prefix);
         end
         else begin
            $sformat(psdisplay, "%s\n%s   Non-EMPTY", psdisplay, prefix);
         end
         $sformat(psdisplay, "%s %s(%s)", psdisplay,
                 this.channels[i].chan.log.get_name(),
                 this.channels[i].chan.log.get_instance());
      end
   end

   if (this.xactors.size() > 0) begin
      if (psdisplay.len() > 0) $sformat(psdisplay, "%s\n", psdisplay);
      $sformat(psdisplay, "%s%sWatched transactors:", psdisplay, prefix);
      `foreach (this.xactors,i) begin
         if (this.xactors[i].xact.notify.is_on(vmm_xactor::XACTOR_IDLE)) begin
            $sformat(psdisplay, "%s\n%s   IDLE", psdisplay, prefix);
         end
         else begin
            $sformat(psdisplay, "%s\n%s   BUSY", psdisplay, prefix);
         end
         $sformat(psdisplay, "%s %0s(%0s)", psdisplay,
                 this.xactors[i].xact.log.get_name(),
                 this.xactors[i].xact.log.get_instance());
      end
   end
endfunction: psdisplay


task vmm_watchdog::main();
   fork
      super.main();

      forever begin
         @(this.force_firing);
         this.notify.indicate(TIMEOUT);
         if (this.log.start_msg(vmm_log::FAILURE_TYP,
                                vmm_log::WARNING_SEV)) begin
            void'(this.log.text("Timer has expired"));
            this.log.end_msg();
         end
      end
   join_none

   forever begin
      fork
      begin
         this.fuse_lit = $time;
         fork
            begin
               wait (this.run_fuse);
               #(this.fuse_length);
               -> this.force_firing;
            end
            @(this.new_fuse);
         join_any
         disable fork;
      end
      join
   end
endtask: main
