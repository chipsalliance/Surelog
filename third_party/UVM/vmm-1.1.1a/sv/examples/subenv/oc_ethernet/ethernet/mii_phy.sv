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


typedef class mii_phy_layer;

// Example 5-15
class mii_phy_collision;
   typedef enum {NONE, EARLY, LATE} kind_e;
   rand kind_e       kind;
   rand int unsigned on_symbol;
  
   // Example 5-16
   eth_frame    frame;

   constraint mii_phy_collision_valid {
      on_symbol < 1500 * 2 + 16;
   }

   constraint early_collision {
      if (kind == EARLY) on_symbol < 112;
   }
   constraint late_collision {
      if (kind == LATE) {
         on_symbol >= 112;
      }
   }
   constraint no_collision {
      kind == NONE;
   }
endclass: mii_phy_collision


virtual class mii_phy_layer_callbacks extends vmm_xactor_callbacks;
   virtual task pre_frame_tx(mii_phy_layer   xactor,
                             /*const*/ eth_frame frame,
                             mii_phy_collision col,
                             ref logic [7:0] bytes[]);
   endtask

   virtual task pre_symbol_tx(mii_phy_layer         xactor,
                              /*const*/ eth_frame       frame,
                              /*const*/ ref logic [7:0] bytes[],
                              /*const*/ input int       nibble_no,
                              ref logic [3:0]       symbol,
                              ref logic             dv,
                              ref logic             err,
                              ref bit               drop);
   endtask

   virtual task post_frame_tx(mii_phy_layer         xactor,
                              /*const*/ eth_frame       frame,
                              /*const*/ ref logic [7:0] bytes[],
                              /*const*/ input bit       error);
   endtask

   virtual task post_symbol_rx(mii_phy_layer      xactor,
                               /*const*/ int unsigned nibble_count,
                               /*const*/ logic [3:0]  symbol,
                               /*const*/ logic        dv,
                               /*const*/ logic        err);
   endtask

   virtual task post_frame_rx(mii_phy_layer            xactor,
                              /*const*/ eth_frame          frame,
                              /*const*/ ref logic [7:0]    bytes[],
                              /*const*/ input int unsigned n_bytes);
   endtask

endclass: mii_phy_layer_callbacks


// Example 4-1
// Example 4-32
// Example 4-48
class mii_phy_layer extends vmm_xactor;

   virtual mii_if.phy_layer sigs;

   eth_frame_channel   tx_chan;
   eth_frame_channel   rx_chan;
   eth_pls_indications indications;

   // Example 5-18
   mii_phy_collision randomized_col;

   local eth_utils utils;

   local mii_cfg   cfg;
   // Example 4-62
   local eth_frame rx_factory;

   local mii_cfg   hard_rst_cfg;
   local eth_frame hard_rst_rx_factory;

   local int frame_count;
   local bit txing;
   local bit rxing;

   // Example 4-62
   function new(string                   inst,
                int unsigned             stream_id = -1,
                mii_cfg                  cfg,
                virtual mii_if.phy_layer sigs,
                eth_frame_channel        tx_chan     = null,
                eth_frame_channel        rx_chan     = null,
                eth_pls_indications      indications = null,
                eth_frame                rx_factory  = null);
      super.new("MII PHY Layer", inst, stream_id);

      this.cfg = cfg;
      this.sigs = sigs;

      if (tx_chan == null) tx_chan = new({this.log.get_name(), " PHY->MAC frames"}, inst);
      this.tx_chan = tx_chan;
      if (rx_chan == null) rx_chan = new({this.log.get_name(), " MAC->PHY frames"}, inst);
      this.rx_chan = rx_chan;

      this.log.is_above(this.tx_chan.log);
      this.log.is_above(this.rx_chan.log);

      if (indications == null) indications = new(this.log);
      this.indications = indications;

      // Example 4-62
      if (rx_factory == null) rx_factory = new;
      this.rx_factory = rx_factory;
       
      this.hard_rst_cfg        = cfg;
      this.hard_rst_rx_factory = rx_factory;

      this.randomized_col = new;

      this.frame_count = 0;
      this.txing = 0;
      this.rxing = 0;

      this.utils = new;

      this.sigs.prx.rxd    <= 4'h0;
      this.sigs.prx.rx_dv  <= 1'b0;
      this.sigs.prx.rx_err <= 1'b0;
      this.sigs.crs        <= 1'b0;
      this.sigs.col        <= 1'b0;
   endfunction: new

   extern virtual function void reconfigure(mii_cfg   cfg        = null,
                                            eth_frame rx_factory = null);
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);

   extern protected virtual task main();
   
   extern local task tx_driver();
   extern local task rx_monitor();
   extern local task crs_driver();
   extern local task col_driver();

endclass: mii_phy_layer



function void mii_phy_layer::reconfigure(mii_cfg   cfg = null,
                                         eth_frame rx_factory = null);
   if (cfg != null) this.cfg = cfg;
   if (rx_factory != null) this.rx_factory = rx_factory;
endfunction: reconfigure

   
function void mii_phy_layer::reset_xactor(reset_e rst_typ = SOFT_RST);
   super.reset_xactor(rst_typ);

   this.sigs.prx.rxd    <= 4'h0;
   this.sigs.prx.rx_dv  <= 1'b0;
   this.sigs.prx.rx_err <= 1'b0;
   this.sigs.crs    <= 1'b0;
   this.sigs.col    <= 1'b0;

   this.tx_chan.flush();
   this.rx_chan.flush();
   this.indications.reset();

   this.frame_count = 0;
   this.txing = 0;
   this.rxing = 0;

   if (rst_typ >= FIRM_RST) begin
      this.indications.reset(, vmm_notify::HARD );
   end

   if (rst_typ >= HARD_RST) begin
      this.cfg        = this.hard_rst_cfg;
      this.rx_factory = this.hard_rst_rx_factory;
   end
endfunction: reset_xactor


task mii_phy_layer::main();
   fork
      super.main();

      this.tx_driver();
      this.rx_monitor();
      this.crs_driver();
      this.col_driver();

      begin
         this.notify.reset(vmm_xactor::XACTOR_BUSY);
         this.notify.indicate(vmm_xactor::XACTOR_IDLE);

         forever begin
            wait (this.txing || this.rxing);
            this.notify.indicate(vmm_xactor::XACTOR_BUSY);
            this.notify.reset(vmm_xactor::XACTOR_IDLE);
            
            wait (!this.txing && !this.rxing);
            // Wait for interface to be quiet for "a while"
            // before declaring the entire xactor idle
            repeat (100) @(this.sigs.prx);
            if (!this.txing && !this.rxing) begin
               this.notify.reset(vmm_xactor::XACTOR_BUSY);
               this.notify.indicate(vmm_xactor::XACTOR_IDLE);
            end
         end
      end
      
   join_none
endtask: main


task mii_phy_layer::tx_driver();
   logic [7:0] bytes[];
   while (1) begin
      bit do_break = 0;
      eth_frame fr;
      bit         error = 0;
      bit         col   = 0;
      
      this.wait_if_stopped_or_empty(this.tx_chan);
      this.tx_chan.activate(fr);

      this.utils.frame_to_bytes(fr, bytes);

      // Example 5-18
      this.randomized_col.frame = fr;
      if (!this.randomized_col.randomize()) begin
         `vmm_fatal(this.log, "Cannot find solution for collision descriptor");
         this.randomized_col.kind = mii_phy_collision::NONE;
      end

      `vmm_callback(mii_phy_layer_callbacks,
                    pre_frame_tx(this,
                                 fr,
                                 this.randomized_col,
                                 bytes));

      if (log.start_msg(vmm_log::DEBUG_TYP , vmm_log::TRACE_SEV )) begin
         void'(log.text("Transmitting frame..."));
         void'(log.text(fr.psdisplay("   ")));
         log.end_msg();
      end

      // Wait for a frame to be received to force a collision
      if (this.randomized_col.kind != mii_phy_collision::NONE) begin
         `vmm_trace(this.log, $psprintf("Forcing a collision on symbol #%0d...",
                                        this.randomized_col.on_symbol));

         @ (posedge this.sigs.crs);
         repeat (this.randomized_col.on_symbol) @ (this.sigs.ptx);
      end

      void'(this.tx_chan.start());
      this.indications.indicate(eth_pls_indications::CARRIER);
      this.txing = 1;
      `foreach (bytes,i) begin
         logic [3:0] nibble0, nibble1;
         logic       en;
         logic       err;
         bit         drop;

         {nibble1, nibble0} = bytes[i];
         en     = 1'b1;
         err    = 1'b0;
         drop   = 1'b0;
         `vmm_callback(mii_phy_layer_callbacks,
                       pre_symbol_tx(this,
                                     fr,
                                     bytes,
                                     i*2,
                                     nibble0,
                                     en,
                                     err,
                                     drop));

         if (!drop) begin
            @this.sigs.prx;
            this.sigs.prx.rxd    <= nibble0;
            this.sigs.prx.rx_dv  <= en;
            this.sigs.prx.rx_err <= err;

            error |= err;
            if (this.sigs.col) col = 1;
         end

         en     = 1'b1;
         err    = 1'b0;
         drop   = 1'b0;
         
         `vmm_callback(mii_phy_layer_callbacks,
                       pre_symbol_tx(this,
                                     fr,
                                     bytes,
                                     i*2 + 1,
                                     nibble1,
                                     en,
                                     err,
                                     drop));

         if (!drop) begin
            @this.sigs.prx;
            this.sigs.prx.rxd    <= nibble1;
            this.sigs.prx.rx_dv  <= en;
            this.sigs.prx.rx_err <= err;

            error |= err;
            if (this.sigs.col) col = 1;
         end

         if (col && !this.cfg.full_duplex) begin
            error = 1;

            `vmm_debug(this.log, "Jamming...");

            // Jam the transmission
            for (int j = 0; j < 8; j++) begin
               nibble0 = $random;
               en      = 1'b1;
               err     = 1'b0;
               drop    = 1'b0;
         
               `vmm_callback(mii_phy_layer_callbacks,
                             pre_symbol_tx(this,
                                           fr,
                                           bytes,
                                           i*2 + 2 + j,
                                           nibble0,
                                           en,
                                           err,
                                           drop));

               if (!drop) begin
                  @this.sigs.prx;
                  this.sigs.prx.rxd    <= nibble0;
                  this.sigs.prx.rx_dv  <= en;
                  this.sigs.prx.rx_err <= err;
               end
            end
            i = bytes.size();
         end
      end
      this.txing = 0;
      void'(this.tx_chan.complete());

      if (log.start_msg(vmm_log::DEBUG_TYP , vmm_log::TRACE_SEV )) begin
         void'(log.text("Transmitted frame..."));
         void'(log.text(fr.psdisplay("   ")));
         log.end_msg();
      end

      @this.sigs.prx;
      this.sigs.prx.rxd    <= 4'b0;
      this.sigs.prx.rx_dv  <= 1'b0;
      this.sigs.prx.rx_err <= 1'b0;

      // Make sure CRS stays asserted for >1 cycle
      fork
         begin: hold_crs
            repeat (2) @this.sigs.prx;
            if (!this.txing && !this.rxing) begin
               this.indications.reset(eth_pls_indications::CARRIER);
            end
         end
      join_none

      `vmm_callback(mii_phy_layer_callbacks,
                    post_frame_tx(this,
                                  fr,
                                  bytes,
                                  error));

      void'(this.tx_chan.remove());
   end
endtask: tx_driver


task mii_phy_layer::rx_monitor();
   logic [7:0] bytes[];
   integer     n_bytes;
   bit         err;

   bytes = new [1600];

   // Has the monitor been started in the middle of a frame being received?
   if (this.sigs.ptx.tx_en) begin
      `vmm_warning(this.log, "Transactor started in the middle of a MAC->PHY transfer");
      this.indications.indicate(eth_pls_indications::CARRIER);
      wait (this.sigs.ptx.tx_en === 1'b0);
   end
   if (!this.txing) this.indications.reset(eth_pls_indications::CARRIER);

   forever begin
      bit do_break;
      bit do_continue;
      logic [7:0] a_byte;

      // Wait for the start of the frame
      wait (this.sigs.ptx.tx_en === 1'b1);
      this.indications.indicate(eth_pls_indications::CARRIER);

      `vmm_debug(this.log, "Started to receive symbols...");

      this.rxing = 1;

     // Wait for the SFD
      do_break = 0;
      while (!do_break && this.sigs.ptx.txd !== 4'b1101) begin
         if (this.sigs.ptx.tx_en !== 1'b1) begin
            // Indicate a false carrier
            // ToDo...
            this.indications.reset(eth_pls_indications::CARRIER);
            do_break = 1;
         end
         if (!do_break)
           @(this.sigs.ptx);
      end

      `vmm_debug(this.log, "Started to receive a frame...");
      @(this.sigs.ptx); // Skip SFD...

      // Collect nibbles into bytes (LS first)
      // until tx_en is deasserted
      n_bytes = 0;
      err     = 0;
      do_break = 0;
      while (this.sigs.ptx.tx_en === 1'b1) begin
         a_byte[3:0] = this.sigs.ptx.txd;
         if (this.sigs.ptx.tx_err !== 1'b0) err = 1;

         `vmm_callback(mii_phy_layer_callbacks,
                       post_symbol_rx(this,
                                      n_bytes * 2,
                                      this.sigs.ptx.txd,
                                      1'b1,
                                      this.sigs.ptx.tx_err));

         @this.sigs.ptx;
         if (this.sigs.ptx.tx_en !== 1'b1) break;
        if (!do_break) begin
         a_byte[7:4] = this.sigs.ptx.txd;
         if (this.sigs.ptx.tx_err !== 1'b0) err = 1;

         `vmm_callback(mii_phy_layer_callbacks,
                       post_symbol_rx(this,
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
        end // if !do_break
      end
      this.rxing = 0;

      // Make sure CRS stays asserted for >1 cycle
      fork
         begin
            repeat (2) @this.sigs.prx;
            if (!this.txing && !this.rxing) begin
               this.indications.reset(eth_pls_indications::CARRIER);
            end
         end
      join_none

      // End of frame. Unpack and forward it
      do_continue = 0;
      if (!err) begin
         eth_frame fr = this.utils.bytes_to_frame(this.log, bytes, n_bytes,
                                                  this.rx_factory);
         if (fr == null)  do_continue=1;

        if (!do_continue) begin
         fr.stream_id = this.stream_id;
         fr.data_id   = this.frame_count++;
         
         if (log.start_msg(vmm_log::DEBUG_TYP , vmm_log::TRACE_SEV )) begin
            void'(log.text("Received frame..."));
            void'(log.text(fr.psdisplay("   ")));
            log.end_msg();
         end

         `vmm_callback(mii_phy_layer_callbacks,
                       post_frame_rx(this,
                                     fr,
                                     bytes,
                                     n_bytes));
         
         this.rx_chan.sneak(fr);
        end // if !do_continue
      end
   end
endtask: rx_monitor

   
task mii_phy_layer::crs_driver();
   while (1) begin
      this.indications.wait_for(eth_pls_indications::CARRIER);
      this.sigs.crs <= 1'b1;
      this.indications.wait_for_off(eth_pls_indications::CARRIER);
      this.sigs.crs <= 1'b0;
   end
endtask: crs_driver

   
task mii_phy_layer::col_driver();
   fork
      while (1) begin
         wait (this.sigs.ptx.tx_en === 1'b1 && this.txing);
         this.indications.indicate(eth_pls_indications::COLLISION);
         wait (this.sigs.ptx.tx_en !== 1'b1 || !this.txing);
         if (this.sigs.ptx.tx_en === 1'b1 && !this.txing) begin
            // Hold COL pass RX_DV deassert
            repeat (2) @this.sigs.prx;
         end
         this.indications.reset(eth_pls_indications::COLLISION);
      end
   join_none

   while (1) begin
      this.indications.wait_for(eth_pls_indications::COLLISION);
      this.sigs.col <= 1'b1;
      this.indications.wait_for_off(eth_pls_indications::COLLISION);
      this.sigs.col <= 1'b0;
   end
endtask: col_driver
