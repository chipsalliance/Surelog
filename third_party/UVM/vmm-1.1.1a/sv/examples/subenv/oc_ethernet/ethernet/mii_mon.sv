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


typedef class mii_monitor;
virtual class mii_monitor_callbacks extends vmm_xactor_callbacks;
   typedef enum {TO_MAC, TO_PHY} direction_e;
   
   virtual function void post_frame_rx(mii_monitor           xactor,
                                       /*const*/ mii_monitor_callbacks::direction_e     direction,
                                       /*const*/ eth_frame          frame,
                                       /*const*/ ref logic [7:0]    bytes[],
                                       /*const*/ input int unsigned n_bytes);
   endfunction

   virtual function void post_symbol_rx(mii_monitor        xactor,
                                        /*const*/ mii_monitor_callbacks::direction_e  direction,
                                        /*const*/ int unsigned nibble_count,
                                        /*const*/ logic [3:0]  symbol,
                                        /*const*/ logic        dv,
                                        /*const*/ logic        err);
   endfunction

endclass: mii_monitor_callbacks


class mii_monitor extends vmm_xactor;

   virtual mii_if.passive sigs;

   eth_frame_channel   to_phy_chan;
   eth_frame_channel   to_mac_chan;
   eth_pls_indications indications;

   local mii_cfg   cfg;
   local eth_frame to_phy_factory;
   local eth_frame to_mac_factory;

   local mii_cfg   hard_rst_cfg;
   local eth_frame hard_rst_to_phy_factory;
   local eth_frame hard_rst_to_mac_factory;

   local int to_mac_count;
   local int to_phy_count;

   local eth_utils utils;

   local bit [1:0] busy;

   function new(string                   inst,
                int unsigned             stream_id = -1,
                mii_cfg                  cfg,
                virtual mii_if.passive   sigs,
                eth_frame_channel        to_phy_chan    = null,
                eth_frame_channel        to_mac_chan    = null,
                eth_pls_indications      indications    = null,
                eth_frame                to_phy_factory = null,
                eth_frame                to_mac_factory = null);
      super.new("MII Monitor", inst, stream_id);

      this.cfg = cfg;
      this.sigs = sigs;

      if (to_phy_chan == null) to_phy_chan = new({this.log.get_name(), " MAC->PHY frames"}, inst);
      this.to_phy_chan = to_phy_chan;
      if (to_mac_chan == null) to_mac_chan = new({this.log.get_name(), " PHY->MAC frames"}, inst);
      this.to_mac_chan = to_mac_chan;

      this.log.is_above(this.to_phy_chan.log);
      this.log.is_above(this.to_mac_chan.log);

      if (indications == null) indications = new(this.log);
      this.indications = indications;

      if (to_phy_factory == null) to_phy_factory = new;
      this.to_phy_factory = to_phy_factory;
      if (to_mac_factory == null) to_mac_factory = new;
      this.to_mac_factory = to_mac_factory;
       
      this.hard_rst_cfg            = cfg;
      this.hard_rst_to_phy_factory = to_phy_factory;
      this.hard_rst_to_mac_factory = to_mac_factory;

      this.to_mac_count = 0;
      this.to_phy_count = 0;

      this.utils = new;

      this.busy = 2'b00;
   endfunction: new



   extern virtual function void reconfigure(mii_cfg   cfg            = null,
                                            eth_frame to_phy_factory = null,
                                            eth_frame to_mac_factory = null);

   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);

   extern protected virtual task main();
   
   extern local task to_phy_monitor();
   extern local task to_mac_monitor();
   extern local task crs_monitor();
   extern local task col_monitor();

endclass: mii_monitor



function void mii_monitor::reconfigure(mii_cfg   cfg            = null,
                                       eth_frame to_phy_factory = null,
                                       eth_frame to_mac_factory = null);
   if (cfg != null) this.cfg = cfg;
   if (to_phy_factory != null) this.to_phy_factory = to_phy_factory;
   if (to_mac_factory != null) this.to_phy_factory = to_mac_factory;
endfunction: reconfigure

   
function void mii_monitor::reset_xactor(reset_e rst_typ = SOFT_RST);
   super.reset_xactor(rst_typ);

   this.to_phy_chan.flush();
   this.to_mac_chan.flush();
   this.indications.reset();

   this.to_mac_count = 0;
   this.to_phy_count = 0;

   if (rst_typ >= FIRM_RST) begin
      this.indications.reset( , vmm_notify::HARD );
   end

   if (rst_typ >= HARD_RST) begin
      this.cfg            = this.hard_rst_cfg;
      this.to_phy_factory = this.hard_rst_to_phy_factory;
      this.to_mac_factory = this.hard_rst_to_mac_factory;
   end

   this.busy = 2'b00;
endfunction: reset_xactor


task mii_monitor::main();
   fork
      super.main();

      this.to_phy_monitor();
      this.to_mac_monitor();
      this.crs_monitor();
      this.col_monitor();

      begin
         this.notify.reset(vmm_xactor::XACTOR_BUSY);
         this.notify.indicate(vmm_xactor::XACTOR_IDLE);

         forever begin
            wait (this.busy);
            this.notify.indicate(vmm_xactor::XACTOR_BUSY);
            this.notify.reset(vmm_xactor::XACTOR_IDLE);
            
            wait (!this.busy);
            // Wait for interface to be quiet for "a while"
            // before declaring the entire xactor idle
            repeat (100) @(this.sigs.ptx);
            if (!this.busy) begin
               this.notify.reset(vmm_xactor::XACTOR_BUSY);
               this.notify.indicate(vmm_xactor::XACTOR_IDLE);
            end
         end
      end
      
   join_none
endtask: main


task mii_monitor::to_phy_monitor();
   logic [7:0] bytes[];
   integer     n_bytes;
   bit         err;

   bytes = new [1600];

   // Has the monitor been started in the middle of a frame being received?
   if (this.sigs.ptx.tx_en) begin
      `vmm_warning(this.log, "Monitor started in the middle of a MAC->PHY transfer");
      wait (this.sigs.ptx.tx_en === 1'b0);
   end

   while (1) begin
      logic [7:0] a_byte;

      this.busy[0] = 0;

      // Wait for the start of the frame
      wait (this.sigs.ptx.tx_en === 1'b1);

      this.busy[0] = 1;

      `vmm_debug(this.log, "Started to receive symbols...");

     // Wait for the SFD
      while (this.sigs.ptx.txd !== 4'b1101) begin
         if (this.sigs.ptx.tx_en !== 1'b1) begin
            // Indicate a false carrier
            // ToDo...
            this.indications.reset(eth_pls_indications::CARRIER);
            break;
         end
         @(this.sigs.ptx);
      end

      `vmm_debug(this.log, "Started to receive a frame...");
      @(this.sigs.ptx); // Skip SFD...

      // Collect nibbles into bytes (LS first)
      // until tx_en is deasserted
      n_bytes = 0;
      err     = 0;
      while (this.sigs.ptx.tx_en === 1'b1) begin
         a_byte[3:0] = this.sigs.ptx.txd;
         if (this.sigs.ptx.tx_err !== 1'b0) err = 1;

         `vmm_callback(mii_monitor_callbacks,
                       post_symbol_rx(this,
                                      mii_monitor_callbacks::TO_PHY,
                                      n_bytes * 2,
                                      this.sigs.ptx.txd,
                                      1'b1,
                                      this.sigs.ptx.tx_err));
         
         @this.sigs.ptx;
         if (this.sigs.ptx.tx_en !== 1'b1) break;
         a_byte[7:4] = this.sigs.ptx.txd;
         if (this.sigs.ptx.tx_err !== 1'b0) err = 1;

         `vmm_callback(mii_monitor_callbacks,
                       post_symbol_rx(this,
                                      mii_monitor_callbacks::TO_PHY,
                                      n_bytes * 2 + 1,
                                      this.sigs.ptx.txd,
                                      1'b1,
                                      this.sigs.ptx.tx_err));

         // Increase byte buffer if necessary
         if (n_bytes >= bytes.size()) begin
            bytes = new [bytes.size() * 2] (bytes);
         end
         bytes[n_bytes++] = a_byte;
         
         @this.sigs.ptx;
      end

      // End of frame. Unpack and forward it
      if (!err) begin
         eth_frame fr = this.utils.bytes_to_frame(this.log, bytes, n_bytes,
                                                  this.to_phy_factory);
         if (fr == null) continue;
         
         fr.stream_id = this.stream_id;
         fr.data_id   = this.to_phy_count++;
         
         if (log.start_msg(vmm_log::DEBUG_TYP , vmm_log::TRACE_SEV )) begin
            void'(log.text("Observed Mac->Phy frame..."));
            void'(log.text(fr.psdisplay("   ")));
            log.end_msg();
         end

         `vmm_callback(mii_monitor_callbacks,
                       post_frame_rx(this,
                                     mii_monitor_callbacks::TO_PHY,
                                     fr,
                                     bytes,
                                     n_bytes));

         this.to_phy_chan.sneak(fr);
      end
   end
endtask: to_phy_monitor


task mii_monitor::to_mac_monitor();
   logic [7:0] bytes[];
   integer     n_bytes;
   bit         err;

   bytes = new [1600];

   // Has the monitor been started in the middle of a frame being received?
   if (this.sigs.mrx.rx_dv) begin
      `vmm_warning(this.log, "Monitor started in the middle of a PHY->MAC transfer");
      this.busy[1] = 1;
      wait (this.sigs.mrx.rx_dv === 1'b0);
   end

   while (1) begin
      logic [7:0] a_byte;

      this.busy[1] = 0;

      // Wait for the start of the frame
      wait (this.sigs.mrx.rx_dv === 1'b1);

      this.busy[1] = 1;

      `vmm_debug(this.log, "Started to receive symbols...");

     // Wait for the SFD
      while (this.sigs.mrx.rxd !== 4'b1101) begin
         if (this.sigs.mrx.rx_dv !== 1'b1) begin
            // Indicate a false carrier
            // ToDo...
            this.indications.reset(eth_pls_indications::CARRIER);
            break;
         end
         @(this.sigs.mrx);
      end

      `vmm_debug(this.log, "Started to receive a frame...");
      @(this.sigs.mrx); // Skip SFD...

      // Collect nibbles into bytes (LS first)
      // until tx_en is deasserted
      n_bytes = 0;
      err     = 0;
      while (this.sigs.mrx.rx_dv === 1'b1) begin
         a_byte[3:0] = this.sigs.mrx.rxd;
         if (this.sigs.mrx.rx_err !== 1'b0) err = 1;

         `vmm_callback(mii_monitor_callbacks,
                       post_symbol_rx(this,
                                      mii_monitor_callbacks::TO_MAC,
                                      n_bytes * 2,
                                      this.sigs.mrx.rxd,
                                      1'b1,
                                      this.sigs.mrx.rx_err));

         @this.sigs.mrx;
         if (this.sigs.mrx.rx_dv !== 1'b1) break;
         a_byte[7:4] = this.sigs.mrx.rxd;
         if (this.sigs.mrx.rx_err !== 1'b0) err = 1;

         `vmm_callback(mii_monitor_callbacks,
                       post_symbol_rx(this,
                                      mii_monitor_callbacks::TO_MAC,
                                      n_bytes * 2 + 1,
                                      this.sigs.mrx.rxd,
                                      1'b1,
                                      this.sigs.mrx.rx_err));

         // Increase byte buffer if necessary
         if (n_bytes >= bytes.size()) begin
            bytes = new [bytes.size() * 2] (bytes);
         end
         bytes[n_bytes++] = a_byte;
         
         @this.sigs.mrx;
      end

      // End of frame. Unpack and forward it
      if (!err) begin
         eth_frame fr = this.utils.bytes_to_frame(this.log, bytes, n_bytes,
                                                  this.to_mac_factory);
         if (fr == null) continue;
         
         fr.stream_id = this.stream_id;
         fr.data_id   = this.to_mac_count++;
         
         if (log.start_msg(vmm_log::DEBUG_TYP , vmm_log::TRACE_SEV )) begin
            void'(log.text("Observed Phy->Mac frame..."));
            void'(log.text(fr.psdisplay("   ")));
            log.end_msg();
         end

         `vmm_callback(mii_monitor_callbacks,
                       post_frame_rx(this,
                                     mii_monitor_callbacks::TO_MAC,
                                     fr,
                                     bytes,
                                     n_bytes));

         this.to_mac_chan.sneak(fr);
      end
   end
endtask: to_mac_monitor

   
task mii_monitor::crs_monitor();
   while (1) begin
      wait (this.sigs.crs === 1'b1);
      this.indications.indicate(eth_pls_indications::CARRIER);
      wait (this.sigs.crs === 1'b0);
      this.indications.reset(eth_pls_indications::CARRIER);
   end
endtask: crs_monitor

   
task mii_monitor::col_monitor();
   while (1) begin
      wait (this.sigs.col === 1'b1);
      this.indications.indicate(eth_pls_indications::COLLISION);
      wait (this.sigs.col === 1'b0);
      this.indications.reset(eth_pls_indications::COLLISION);
   end
endtask: col_monitor
