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


// Example 4-84
typedef class mii_mac_layer;
virtual class mii_mac_layer_callbacks extends vmm_xactor_callbacks;
   virtual task pre_frame_tx(mii_mac_layer     xactor,
                             /*const*/ eth_frame         frame,
                             ref logic [7:0]   bytes[]);
   endtask

   virtual task pre_symbol_tx(mii_mac_layer         xactor,
                              /*const*/ eth_frame       frame,
                              /*const*/ ref logic [7:0] bytes[],
                              /*const*/ input integer   nibble_no,
                              ref logic [3:0]       symbol,
                              ref logic             en,
                              ref logic             err,
                              ref bit               drop);
   endtask

   virtual task post_frame_tx(mii_mac_layer         xactor,
                              /*const*/ eth_frame       frame,
                              /*const*/ ref logic [7:0] bytes[],
                              ref bit               error);
   endtask


   virtual function void post_frame_rx(mii_mac_layer      xactor,
                                       /*const*/ eth_frame    frame,
                                       /*const*/ logic [7:0]  bytes[],
                                       /*const*/ int unsigned n_bytes);
   endfunction

   virtual function void post_symbol_rx(mii_mac_layer      xactor,
                                        /*const*/ int unsigned nibble_count,
                                        /*const*/ logic [3:0]  symbol,
                                        /*const*/ logic        dv,
                                        /*const*/ logic        err);
   endfunction

endclass: mii_mac_layer_callbacks


// Example 4-13
// Example 4-48
class mii_mac_layer extends vmm_xactor;

   // Example 4-55
   virtual mii_if.mac_layer sigs;

   // Example 4-57
   // Example 4-61
   eth_frame_channel   tx_chan;
   eth_frame_channel   rx_chan;
   eth_pls_indications indications;

   local mii_cfg   cfg;
   local eth_frame rx_factory;

   local mii_cfg   hard_rst_cfg;
   local eth_frame hard_rst_rx_factory;

   local int frame_count;

   local eth_utils utils;

   // Example 4-54
   // Example 4-61
   function new(string                   inst,
                int unsigned             stream_id = -1,
                mii_cfg                  cfg,
                virtual mii_if.mac_layer sigs,
                eth_frame_channel        tx_chan     = null,
                eth_frame_channel        rx_chan     = null,
                eth_pls_indications      indications = null,
                eth_frame                rx_factory  = null);

      super.new("MII MAC Layer", inst, stream_id);

      this.cfg = cfg;
      // Example 4-55
      this.sigs = sigs;

      if (tx_chan == null) begin
         tx_chan = new({this.log.get_name(), " MAC->PHY frames"}, inst);
      end
      this.tx_chan = tx_chan;
      if (rx_chan == null) rx_chan = new({this.log.get_name(), " PHY->MAC frames"}, inst);
      this.rx_chan = rx_chan;

      this.log.is_above(this.tx_chan.log);
      this.log.is_above(this.rx_chan.log);

      if (indications == null) indications = new(this.log);
      this.indications = indications;

      if (rx_factory == null) rx_factory = new;
      this.rx_factory = rx_factory;
       
      this.hard_rst_cfg        = cfg;
      this.hard_rst_rx_factory = rx_factory;

      this.frame_count = 0;

      this.utils = new;

      this.sigs.mtx.txd    <= 4'h0;
      this.sigs.mtx.tx_en  <= 1'b0;
      this.sigs.mtx.tx_err <= 1'b0;
   endfunction: new

   extern virtual function void reconfigure(mii_cfg   cfg        = null,
                                            eth_frame rx_factory = null);
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);

   extern protected virtual task main();
   
   extern local task tx_driver();
   extern local task rx_monitor();
   extern local task crs_monitor();
   extern local task col_monitor();

endclass: mii_mac_layer



function void mii_mac_layer::reconfigure(mii_cfg   cfg = null,
                                         eth_frame rx_factory = null);
   if (cfg != null) this.cfg = cfg;
   if (rx_factory != null) this.rx_factory = rx_factory;
endfunction: reconfigure

   
// Example 4-52
function void mii_mac_layer::reset_xactor(reset_e rst_typ = SOFT_RST);
   super.reset_xactor(rst_typ);

   this.sigs.mtx.txd    <= 4'h0;
   this.sigs.mtx.tx_en  <= 1'b0;
   this.sigs.mtx.tx_err <= 1'b0;

   this.tx_chan.flush();
   this.rx_chan.flush();
   this.indications.reset();

   this.frame_count = 0;

   if (rst_typ >= FIRM_RST) begin
      this.indications.reset( , vmm_notify::HARD );
   end

   if (rst_typ >= HARD_RST) begin
      this.cfg        = this.hard_rst_cfg;
      this.rx_factory = this.hard_rst_rx_factory;
   end
endfunction: reset_xactor


// Example 4-51
task mii_mac_layer::main();
   fork
      super.main();

      this.tx_driver();
      this.rx_monitor();
      this.crs_monitor();
      this.col_monitor();
      
   join_none
endtask: main


task mii_mac_layer::tx_driver();
   logic [7:0] bytes[];

   while (1) begin
      eth_frame fr;
      bit       error = 0;
      bit       col   = 0;
      
      this.wait_if_stopped_or_empty(this.tx_chan);
      this.tx_chan.activate(fr);

      this.utils.frame_to_bytes(fr, bytes);

      // Example 4-85
      `vmm_callback(mii_mac_layer_callbacks,
                    pre_frame_tx(this,
                                 fr,
                                 bytes));

      // Example 4-25
      if (log.start_msg(vmm_log::DEBUG_TYP , vmm_log::TRACE_SEV )) begin
         void'(log.text("Transmitting frame..."));
         void'(log.text(fr.psdisplay("   ")));
         log.end_msg();
      end

      void'(this.tx_chan.start());
      // Example 4-7
      foreach (bytes[i]) begin
         logic [3:0] nibble0, nibble1;
         logic       en;
         logic       err;
         bit         drop;

         {nibble1, nibble0} = bytes[i];
         en     = 1'b1;
         err    = 1'b0;
         drop   = 1'b0;
         
         `vmm_callback(mii_mac_layer_callbacks,
                       pre_symbol_tx(this,
                                     fr,
                                     bytes,
                                     i*2,
                                     nibble0,
                                     en,
                                     err,
                                     drop));
         
         if (!drop) begin
            // Example 4-7
            // Example 4-56
            @this.sigs.mtx;
            this.sigs.mtx.txd    <= nibble0;
            this.sigs.mtx.tx_en  <= en;
            this.sigs.mtx.tx_err <= err;

            error |= err;
            if (this.sigs.col == 1'b1) col = 1;
         end

         en     = 1'b1;
         err    = 1'b0;
         drop   = 1'b0;
         
         `vmm_callback(mii_mac_layer_callbacks,
                       pre_symbol_tx(this,
                                     fr,
                                     bytes,
                                     i*2 + 1,
                                     nibble1,
                                     en,
                                     err,
                                     drop));

         if (!drop) begin
            // Example 4-7 
            @this.sigs.mtx;
            this.sigs.mtx.txd    <= nibble1;
            this.sigs.mtx.tx_en  <= en;
            this.sigs.mtx.tx_err <= err;

            error |= err;
            if (this.sigs.col == 1'b1) col = 1;
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
         
               `vmm_callback(mii_mac_layer_callbacks,
                             pre_symbol_tx(this,
                                           fr,
                                           bytes,
                                           i*2 + 2 + j,
                                           nibble0,
                                           en,
                                           err,
                                           drop));

               if (!drop) begin
                  @this.sigs.mtx;
                  this.sigs.mtx.txd    <= nibble0;
                  this.sigs.mtx.tx_en  <= en;
                  this.sigs.mtx.tx_err <= err;
               end
            end
            break;
         end
      end
      void'(this.tx_chan.complete());

      if (log.start_msg(vmm_log::DEBUG_TYP , vmm_log::TRACE_SEV )) begin
         void'(log.text("Transmitted frame..."));
         void'(log.text(fr.psdisplay("   ")));
         log.end_msg();
      end

      @this.sigs.mtx;
      this.sigs.mtx.txd    <= 4'b0;
      this.sigs.mtx.tx_en  <= 1'b0;
      this.sigs.mtx.tx_err <= 1'b0;

      `vmm_callback(mii_mac_layer_callbacks,
                    post_frame_tx(this,
                                  fr,
                                  bytes,
                                  error));

      void'(this.tx_chan.remove());
   end
endtask: tx_driver


task mii_mac_layer::rx_monitor();
   logic [7:0] bytes[];
   integer     n_bytes;
   bit         err;

   bytes = new [1600];

   // Has the monitor been started in the middle of a frame being received?
   if (this.sigs.mrx.rx_dv) begin
      `vmm_warning(this.log, "Monitor started in the middle of a PHY->MAC transfer");
      wait (this.sigs.mrx.rx_dv === 1'b0);
   end

   while (1) begin
      logic [7:0] a_byte;

      // Wait for the start of the frame
      wait (this.sigs.mrx.rx_dv === 1'b1);

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

      // Collect nibbles into bytes (MS first)
      // until tx_en is deasserted
      n_bytes = 0;
      err     = 0;
      while (this.sigs.mrx.rx_dv === 1'b1) begin
         a_byte[3:0] = this.sigs.mrx.rxd;
         if (this.sigs.mrx.rx_err !== 1'b0) err = 1;

         `vmm_callback(mii_mac_layer_callbacks,
                       post_symbol_rx(this,
                                      n_bytes * 2,
                                      this.sigs.mrx.rxd,
                                      1'b1,
                                      this.sigs.mrx.rx_err));

         // Example 4-56
         @this.sigs.mrx;
         if (this.sigs.mrx.rx_dv !== 1'b1) break;
         a_byte[7:4] = this.sigs.mrx.rxd;
         if (this.sigs.mrx.rx_err !== 1'b0) err = 1;

         `vmm_callback(mii_mac_layer_callbacks,
                       post_symbol_rx(this,
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
                                                  this.rx_factory);
         if (fr == null) continue;

         fr.stream_id = this.stream_id;
         fr.data_id   = this.frame_count++;
         
         if (log.start_msg(vmm_log::DEBUG_TYP , vmm_log::TRACE_SEV )) begin
            void'(log.text("Received frame..."));
            void'(log.text(fr.psdisplay("   ")));
            log.end_msg();
         end

         `vmm_callback(mii_mac_layer_callbacks,
                       post_frame_rx(this,
                                     fr,
                                     bytes,
                                     n_bytes));

         this.rx_chan.sneak(fr);
      end
   end
endtask: rx_monitor

   
task mii_mac_layer::crs_monitor();
   while (1) begin
      wait (this.sigs.crs === 1'b1);
      this.indications.indicate(eth_pls_indications::CARRIER);
      wait (this.sigs.crs === 1'b0);
      this.indications.reset(eth_pls_indications::CARRIER);
   end
endtask: crs_monitor

   
task mii_mac_layer::col_monitor();
   while (1) begin
      wait (this.sigs.col === 1'b1);
      this.indications.indicate(eth_pls_indications::COLLISION);
      wait (this.sigs.col === 1'b0);
      this.indications.reset(eth_pls_indications::COLLISION);
   end
endtask: col_monitor
