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


class eth_mac_cfg;
   rand bit [47:0]   addr;
   rand bit          promiscuous;
   rand bit          full_duplex;
   rand int unsigned rate;
   rand time         slot_time;    // In local timeunits (ns)
   rand time         ifg;          // In local timeunits (ns)
   rand time         ifg_part1;    // In local timeunits (ns)
   rand int unsigned attempt_limit;
   rand int unsigned backoff_limit;

   constraint local_unicast_addr {
      addr[47:46] == 2'b00;
   }
   constraint eth_mac_cfg_valid {
      rate inside {1, 10, 100, 1000};
      ifg_part1 < ifg;
   }
   constraint default_values {
      if (rate == 1) {
         slot_time     == 512 * 1000;
         ifg           == 96000;
         ifg_part1     == ifg * 2 / 3;
         attempt_limit == 16;
         backoff_limit == 10;
      }
      if (rate == 10) {
         slot_time     == 512 * 100;
         ifg           == 9600;
         ifg_part1     == ifg * 2 / 3;
         attempt_limit == 16;
         backoff_limit == 10;
      }
      if (rate == 100) {
         slot_time     == 512 * 10;
         ifg           == 960;
         ifg_part1     == ifg * 2 / 3;
         attempt_limit == 16;
         backoff_limit == 10;
      }
      if (rate == 1000) {
         slot_time     == 4096 * 1;
         ifg           == 96;
         ifg_part1     == ifg * 2 / 3;
         attempt_limit == 16;
         backoff_limit == 10;
      }
   }
   constraint supported {
      rate != 1000;
   }

   function string psdisplay(string prefix);
      $sformat(psdisplay, "%sMAC Addr: %h.%h.%h.%h.%h.%h", prefix,
               addr[47:40], addr[39:32], addr[31:24], addr[23:16], addr[15:8], addr[7:0]);
      $sformat(psdisplay, "%s\n%s%0s%0s duplex, %0d Mb/s", psdisplay, prefix,
               (this.promiscuous) ? "promiscuous, " : "",
               (this.full_duplex) ? "full" : "half", this.rate);
      $sformat(psdisplay, "%s\n%sSlotTime=%0d, ifg=%0d/%0d, %0d attempts, %0d backOff", psdisplay, prefix,
               this.slot_time, this.ifg, this.ifg_part1, this.attempt_limit, this.backoff_limit);
   endfunction

endclass: eth_mac_cfg
                    

class eth_frame_tx_status extends vmm_data;
   static vmm_log log = new("eth_frame_tx_status", "class");

   bit          successful;
   int unsigned n_attempts;

   function new();
      super.new(this.log);
   endfunction: new
endclass: eth_frame_tx_status


typedef class eth_mac;

virtual class eth_mac_callbacks extends vmm_xactor_callbacks;
   virtual task pre_frame_tx(eth_mac       xactor,
                             ref eth_frame frame,
                             ref bit       drop);
   endtask

   virtual task pre_frame_tx_attempt(eth_mac      xactor,
                                     eth_frame    frame,
                                     int unsigned attempt_count,
                                     ref bit      drop);
   endtask

   virtual task post_frame_tx(eth_mac             xactor,
                              eth_frame           frame,
                              eth_frame_tx_status status);
   endtask

   virtual function void post_frame_rx(eth_mac   xactor,
                                       eth_frame frame);
   endfunction
endclass: eth_mac_callbacks


class eth_mac extends vmm_xactor;

   eth_frame_channel tx_chan;
   eth_frame_channel rx_chan;

   eth_frame_channel   pls_tx_chan;
   eth_frame_channel   pls_rx_chan;
   // Example 4-82
   eth_pls_indications indications;

   local eth_mac_cfg cfg;

   local eth_mac_cfg hard_rst_cfg;

   // Example 4-83
   function new(string              inst,
                int unsigned        stream_id = -1,
                eth_mac_cfg         cfg,
                eth_frame_channel   tx_chan         = null,
                eth_frame_channel   rx_chan         = null,
                eth_frame_channel   pls_tx_chan     = null,
                eth_frame_channel   pls_rx_chan     = null,
                eth_pls_indications indications     = null);
      super.new("Ethernet MAC Layer", inst, stream_id);

      this.cfg = cfg;

      if (tx_chan == null) tx_chan = new({this.log.get_name(), " Tx frames"}, inst);
      this.tx_chan = tx_chan;
      if (rx_chan == null) rx_chan = new({this.log.get_name(), " Rx frames"}, inst);
      this.rx_chan = rx_chan;

      if (pls_tx_chan == null) pls_tx_chan = new({this.log.get_name(), " PHY->MAC frames"}, inst);
      this.pls_tx_chan = pls_tx_chan;
      if (pls_rx_chan == null) pls_rx_chan = new({this.log.get_name(), " MAC->PHY frames"}, inst);
      this.pls_rx_chan = pls_rx_chan;
      if (indications == null) indications = new(this.log);
      this.indications = indications;
       
      this.hard_rst_cfg = cfg;
   endfunction: new
     
   extern virtual function void reconfigure(eth_mac_cfg cfg);
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);

   extern protected virtual task main();

   extern local task tx_driver();
   extern local task rx_monitor();

   local int unsigned maxBackOff;
   extern local task back_off(int unsigned n_attempts);
   local bit transmitting;
   local event transmitting_e;
   local bit deferring;
   local event deferring_e;
   extern local task deference();
   extern local task defer();

endclass: eth_mac

typedef class eth_mac_monitor;
virtual class eth_mac_monitor_callbacks extends vmm_xactor_callbacks;
   typedef enum {TO_MAC, TO_PHY} directions_e;
  
   virtual function void post_frame_rx(eth_mac_monitor      xactor,
                                       eth_mac_monitor_callbacks::directions_e direction,
                                       eth_frame    frame);
   endfunction
endclass: eth_mac_monitor_callbacks


class eth_mac_monitor extends vmm_xactor;

   eth_frame_channel to_phy_chan;
   eth_frame_channel to_mac_chan;

   eth_frame_channel   pls_to_phy_chan;
   eth_frame_channel   pls_to_mac_chan;
   eth_pls_indications indications;

   local eth_mac_cfg cfg;

   local eth_mac_cfg hard_rst_cfg;

   function new(string              inst,
                int unsigned        stream_id = -1,
                eth_mac_cfg         cfg,
                eth_frame_channel   to_phy_chan     = null,
                eth_frame_channel   to_mac_chan     = null,
                eth_frame_channel   pls_to_phy_chan = null,
                eth_frame_channel   pls_to_mac_chan = null,
                eth_pls_indications indications     = null);
      super.new("Ethernet MAC Layer Monitor", inst, stream_id);

      this.cfg = cfg;

      if (to_phy_chan == null) to_phy_chan = new({this.log.get_name(), " ->MAC frames"}, inst);
      this.to_phy_chan = to_phy_chan;
      if (to_mac_chan == null) to_mac_chan = new({this.log.get_name(), " <-MAC frames"}, inst);
      this.to_mac_chan = to_mac_chan;

      if (pls_to_phy_chan == null) pls_to_phy_chan = new({this.log.get_name(), " PHY->MAC frames"}, inst);
      this.pls_to_phy_chan = pls_to_phy_chan;
      if (pls_to_mac_chan == null) pls_to_mac_chan = new({this.log.get_name(), " MAC->PHY frames"}, inst);
      this.pls_to_mac_chan = pls_to_mac_chan;
      if (indications == null) indications = new(this.log);
      this.indications = indications;
       
      this.hard_rst_cfg = cfg;
   endfunction: new

   extern virtual function void reconfigure(eth_mac_cfg cfg);
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);

   extern protected virtual task main();
   
   extern protected task to_phy_monitor();
   extern protected task to_mac_monitor();
endclass: eth_mac_monitor


   //
   // eth_mac
   //


function void eth_mac::reconfigure(eth_mac_cfg cfg);
   this.cfg = cfg;
endfunction: reconfigure

   
function void eth_mac::reset_xactor(reset_e rst_typ = SOFT_RST);
   super.reset_xactor(rst_typ);

   this.tx_chan.flush();
   this.rx_chan.flush();
   this.pls_tx_chan.flush();
   this.pls_rx_chan.flush();
   this.indications.reset();

   if (rst_typ >= FIRM_RST) begin
      this.indications.reset(, vmm_notify::HARD );
   end

   if (rst_typ >= HARD_RST) begin
      this.cfg        = this.hard_rst_cfg;
   end
endfunction: reset_xactor
   

task eth_mac::main();
   fork
      super.main();

      this.tx_driver();
      this.rx_monitor();
      this.deference();
   join_none
endtask: main


task eth_mac::tx_driver();
   eth_frame fr;

   while (1) begin
      bit do_break = 0;
      bit do_continue = 0;
      bit drop = 0;
      eth_frame_tx_status status = new;

      status.successful = 0;
      status.n_attempts = 0;

      this.transmitting = 0;
      
      this.wait_if_stopped_or_empty(this.tx_chan);
      this.tx_chan.activate(fr);

      `vmm_callback(eth_mac_callbacks,
                    pre_frame_tx(this,
                                 fr,
                                 drop));
      if (drop) begin
         void'(this.tx_chan.remove());
         fr.notify.indicate(vmm_data::ENDED , status);
         do_continue = 1;
      end
      
     if (!do_continue) begin

      void'(this.tx_chan.start());

      do_break = 0;

      while (!do_break && status.n_attempts < this.cfg.attempt_limit && !status.successful) begin
         bit col = 0;

         `vmm_callback(eth_mac_callbacks,
                       pre_frame_tx_attempt(this,
                                            fr,
                                            status.n_attempts,
                                            drop));
        if (drop) do_break = 1;

        if (!do_break) begin

         if (log.start_msg(vmm_log::DEBUG_TYP , vmm_log::TRACE_SEV )) begin
            string prefix;
            void'(log.text("Attempting to transmitting frame..."));
            $sformat(prefix, "   Attempt #%0d: ", status.n_attempts);
            void'(log.text(fr.psdisplay(prefix)));
            log.end_msg();
         end
      
         if (status.n_attempts > 0) this.back_off(status.n_attempts);
         this.defer();

         // Watch for collisions
         if (!this.cfg.full_duplex) begin
            fork
               begin
                  this.indications.wait_for(eth_pls_indications::COLLISION);
                  col = 1;
                  `vmm_debug(this.log, "Collision!");
               end
            join_none
         end

         // PLS Tx channel has a blocking model
         this.transmitting = 1;
         this.pls_tx_chan.put(fr);
         this.transmitting = 0;
         disable fork;
         status.n_attempts++;

         // If there were no collisions, success!
         if (!col) begin
            status.successful = 1;
            do_break = 1;
         end
        end // if !do_break
      end
      
      if (log.start_msg(vmm_log::DEBUG_TYP , vmm_log::TRACE_SEV )) begin
         string prefix;
         void'(log.text("Done transmitting frame..."));
         $sformat(prefix, "   %0s: ", (status.successful) ? "Success" : "Failure");
         void'(log.text(fr.psdisplay(prefix)));
         log.end_msg();
      end
      
      void'(this.tx_chan.complete());

      `vmm_callback(eth_mac_callbacks,
                    post_frame_tx(this,
                                  fr,
                                  status));

      fr.notify.indicate(vmm_data::ENDED , status);

      void'(this.tx_chan.remove());
     end // if !do_continue
   end
endtask: tx_driver         
   

task eth_mac::rx_monitor();
   eth_frame fr;

   while (1) begin
      this.pls_rx_chan.get(fr);

      `vmm_callback(eth_mac_callbacks,
                    post_frame_rx(this,
                                  fr));

      if (log.start_msg(vmm_log::DEBUG_TYP , vmm_log::TRACE_SEV )) begin
         void'(log.text("Received frame..."));
         void'(log.text(fr.psdisplay("   ")));
         log.end_msg();
      end
      
      if (this.cfg.promiscuous ||
          this.cfg.addr === fr.dst ||
          fr.dst[47] === 1'b1) begin
         this.rx_chan.sneak(fr);
      end else begin
         `vmm_debug(this.log, "Frame ignored because of wrong unicast address");
      end
   end
endtask: rx_monitor
   

task eth_mac::back_off(int unsigned n_attempts);
   int unsigned n;

   if (n_attempts == 1) this.maxBackOff = 2;
   else if (n_attempts < this.cfg.backoff_limit) this.maxBackOff *= 2;
   n = $random % this.maxBackOff;
   `vmm_debug(this.log, $psprintf("Backing off for %0d slotTimes...", n));
   #(this.cfg.slot_time * n);
endtask: back_off


task eth_mac::deference();
   forever begin
      this.deferring = 0;
      `vmm_debug(this.log, "Deference: not active");
      if (this.cfg.full_duplex) begin

         wait (this.transmitting === 1'b1);
         this.deferring = 1;
         wait (this.transmitting === 1'b0);
         #(this.cfg.ifg);

      end else begin
         bit wasTransmitting;

         `vmm_debug(this.log, "Deference: Waiting for CRS");
         this.indications.wait_for(eth_pls_indications::CARRIER);
         wasTransmitting = this.transmitting;
         this.deferring = 1;
         `vmm_debug(this.log, "Deference: ACTIVE. Waiting for ~CRS");
         this.indications.wait_for_off(eth_pls_indications::CARRIER);
         wait (this.transmitting === 1'b0);
         `vmm_debug(this.log, "Deference: IFG");

         if (wasTransmitting) begin
            #(this.cfg.ifg_part1);
         end else begin: interFrameSpacingPart1
            forever begin
               fork
                  begin
                     #(this.cfg.ifg_part1);
                     disable interFrameSpacingPart1;
                  end
               join_none
               this.indications.wait_for(eth_pls_indications::CARRIER);
               disable fork;
               this.indications.wait_for_off(eth_pls_indications::CARRIER);
            end
         end
         #(this.cfg.ifg - this.cfg.ifg_part1);
      end
   end
endtask: deference


task eth_mac::defer();
  `vmm_debug(this.log, "Deferring...");
   wait(this.deferring === 1'b0);
  `vmm_debug(this.log, "Deferred.");
endtask: defer


   //
   // eth_mac_monitor
   //

   

function void eth_mac_monitor::reconfigure(eth_mac_cfg cfg);
   this.cfg = cfg;
endfunction: reconfigure

   
function void eth_mac_monitor::reset_xactor(reset_e rst_typ = SOFT_RST);
   super.reset_xactor(rst_typ);

   this.to_phy_chan.flush();
   this.to_mac_chan.flush();
   this.pls_to_phy_chan.flush();
   this.pls_to_mac_chan.flush();
   this.indications.reset();

   if (rst_typ >= FIRM_RST) begin
      this.indications.reset(, vmm_notify::HARD );
   end

   if (rst_typ >= HARD_RST) begin
      this.cfg = this.hard_rst_cfg;
   end
endfunction: reset_xactor
   

task eth_mac_monitor::main();
   fork
      super.main();

      this.to_phy_monitor();
      this.to_mac_monitor();
   join_none
endtask: main


task eth_mac_monitor::to_phy_monitor();
   eth_frame fr;

   while (1) begin
      this.pls_to_phy_chan.get(fr);

      `vmm_callback(eth_mac_monitor_callbacks,
                    post_frame_rx(this,
                                  eth_mac_monitor_callbacks::TO_PHY,
                                  fr));

      this.to_phy_chan.sneak(fr);
   end
endtask: to_phy_monitor
   

task eth_mac_monitor::to_mac_monitor();
   eth_frame fr;

   while (1) begin
      this.pls_to_mac_chan.get(fr);

      `vmm_callback(eth_mac_monitor_callbacks,
                    post_frame_rx(this,
                                  eth_mac_monitor_callbacks::TO_MAC,
                                  fr));
      
      this.to_mac_chan.sneak(fr);
   end
endtask: to_mac_monitor
