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


`ifndef ETH_SUBENV__SV
`define ETH_SUBENV__SV

`include "vmm_ral.sv"
`include "vmm_subenv.sv"

`include "mii.sv"

class oc_eth_subenv_cfg;
   rand mii_cfg       mii;

   rand bit [47:0] dut_addr;
   rand bit [ 7:0] n_tx_bd;
   rand bit [15:0] max_frame_len;

   // Stop when both limits are reached
   rand int unsigned run_for_n_frames;
      
   bit [31:0] avail_txbd[$];
   vmm_mam_region dma_bfrs[*]; // Indexed by BD offset

   constraint test_cfg_valid {
      mii.is_10Mb == 0;
      mii.full_duplex == 0;

      n_tx_bd > 1;
      n_tx_bd <= 128;
   }

   constraint coverage_driven {
      max_frame_len inside {1500, 1518, 'h0600};
   }

   constraint reasonable {
      run_for_n_frames < 100;
   }

   function new();
      this.mii = new;
   endfunction: new

   function string psdisplay(string prefix = "");
      $sformat(psdisplay, "%sDUT MAC Addr: %h.%h.%h.%h.%h.%h", prefix,
               dut_addr[47:40], dut_addr[39:32], dut_addr[31:24], dut_addr[23:16], dut_addr[15:8], dut_addr[7:0]);
      $sformat(psdisplay, "%s\n%s%0d TxBD\n", psdisplay, prefix, this.n_tx_bd);
      $sformat(psdisplay, "%s\n%s%0d bytes max frame length", psdisplay,
               prefix, this.max_frame_len);
      $sformat(psdisplay, "%s\n%sfor %0d Tx frames", psdisplay, prefix,
               this.run_for_n_frames);
   endfunction
endclass: oc_eth_subenv_cfg


//
// Self-Checking Structure
//
class scoreboard;
   oc_eth_subenv_cfg cfg;
   vmm_log  log;

   eth_frame to_phy_side[$];

   function new(string            inst,
                oc_eth_subenv_cfg cfg);
      this.cfg = cfg;
      this.log = new("Scoreboard", inst);
   endfunction: new

   function void sent_from_mac_side(eth_frame fr);
      // Is it too long?
      if (fr.byte_size() > this.cfg.max_frame_len) return;

      // Will it be accepted by the PHY-side MAC layer?
      if (fr.fcs) return;// Not if it has a bad FCS

      to_phy_side.push_back(fr);
   endfunction

   function void received_by_phy_side(eth_frame fr);
      eth_frame exp;
      string diff;

      if (this.cfg.run_for_n_frames > 0) begin
         this.cfg.run_for_n_frames--;
      end


      if (this.to_phy_side.size() == 0) begin
         `vmm_error(this.log, $psprintf("Unexpected frame received on PHY side (none expected):\n%s",
                                        fr.psdisplay("   ")));
         return;
      end

      exp = this.to_phy_side.pop_front();
      if (!fr.compare(exp, diff)) begin
         `vmm_error(this.log, $psprintf("Unexpected frame received on PHY side: %s:\n%s\n%s",
                                        diff, fr.psdisplay("   Actual: "),
                                        exp.psdisplay("   Expect: ")));
         return;
      end

      `vmm_note(this.log, $psprintf("Expected frame received on PHY side (%0d left):\n%s",
                                    this.cfg.run_for_n_frames,
                                    fr.psdisplay("   ")));
   endfunction

endclass: scoreboard


typedef class frmwr_emulator;
virtual class frmwr_emulator_callbacks extends vmm_xactor_callbacks;
   virtual task pre_frame_tx(frmwr_emulator   xactor,
                             ref eth_frame frame,
                             ref bit       drop);
   endtask

   virtual function void post_frame_rx(frmwr_emulator         xactor,
                                       /*const*/ eth_frame frame);
   endfunction
endclass: frmwr_emulator_callbacks


class frmwr_emulator extends vmm_xactor;

   eth_frame_channel tx_chan;
   scoreboard sb;

   local oc_eth_subenv_cfg              cfg;
   local ral_block_oc_ethernet ral;
   local wb_ram                ram;
   local vmm_mam               dma_mam;

   local bit [31:0] busy_txbd[$];

   function new(string            inst,
                int unsigned      stream_id = -1,
                oc_eth_subenv_cfg cfg,
                eth_frame_channel tx_chan,
                scoreboard        sb,
                ral_block_oc_ethernet ral,
                wb_ram            dma_ram,
                vmm_mam           dma_mam);
      super.new("FRMWR Emulator", inst, stream_id);
      this.tx_chan = tx_chan;
      this.sb   = sb;
      this.cfg  = cfg;
      this.ral  = ral;
      this.ram  = dma_ram;
      this.dma_mam = dma_mam;

      this.reset_xactor();
   endfunction: new

   function void reset_xactor(reset_e rst_typ = SOFT_RST );
      super.reset_xactor(rst_typ);
      tx_chan.flush();
   endfunction: reset_xactor

   virtual task main();
      fork
         super.main();
         this.tx_driver();
      join
   endtask: main

   local task tx_driver();
      logic [ 7:0] bytes[];

      forever begin
         eth_frame        fr;
         bit              drop = 0;
         vmm_rw::status_e status;

         // Wait for a free Tx buffer if none available
         wait (this.cfg.avail_txbd.size() > 0);
         
         this.wait_if_stopped_or_empty(this.tx_chan);
         this.tx_chan.activate(fr);

         `vmm_callback(frmwr_emulator_callbacks,
                       pre_frame_tx(this, fr, drop));

         if (!drop) begin
            vmm_mam_region bfr;
            int            len;
            bit            wrap = 0;
            int            bd_addr;

            void'(this.tx_chan.start());

            bfr = dma_mam.request_region(fr.byte_size());

            // Write the frame in the DMA RAM
            `vmm_trace(this.log, $psprintf("Buffering TX Frame at 'h%h:\n%s",
                                           bfr.get_start_offset(),
                                           fr.psdisplay("   ")));
            
            // We need full DWORDs
            len = fr.byte_size();
            bytes = new [len + (4 - len % 4)];
            void'(fr.byte_pack(bytes));
            for (int i = 0; i < len; i += 4) begin
               this.ram.write(bfr.get_start_offset() + i,
                              {bytes[i], bytes[i+1], bytes[i+2], bytes[i+3]});
            end

            // Set the TxBD accordingly
            `vmm_debug(this.log, $psprintf("Updating TxBD at 'h%h",
                                           bd_addr));

            bd_addr = this.cfg.avail_txbd.pop_front();
            ral.TxBD[bd_addr].PTR.write(status, bfr.get_start_offset());
            if (status !== vmm_rw::IS_OK) begin
               `vmm_error(this.log, $psprintf("Unable to set TxBD[%0d].PTR",
                                              bd_addr));
            end
            cfg.dma_bfrs[bd_addr] = bfr;

            ral.TxBD[bd_addr].LEN.set(len);
            ral.TxBD[bd_addr].RD.write(status, 1);
            if (status !== vmm_rw::IS_OK) begin
               `vmm_error(this.log, $psprintf("Unable to mark TxBD[%0d] ready",
                                              bd_addr));
            end


            this.busy_txbd.push_back(bd_addr);

            void'(this.tx_chan.complete());

            this.sb.sent_from_mac_side(fr);
         end // drop
         
         void'(this.tx_chan.remove());
      end
   endtask: tx_driver
      
   task service_irq();
      vmm_rw::status_e status;
      bit [31:0]       val;
      bit              ignore_fr;
      bit              TXE, TXB;

      ignore_fr = 0;

      this.ral.INT_SOURCE.mirror(status);
      if (status != vmm_rw::IS_OK) begin
         `vmm_fatal(this.log, "Unable to read INT_SOURCE");
      end

      // Save the interesting flags because the mirror
      // will be cleared on write-back
      TXE = this.ral.TXE.get();
      TXB = this.ral.TXB.get();

      // Do an immediate write-back to clear the interrupts
      // so we won't miss one
      this.ral.INT_SOURCE.write(status, this.ral.INT_SOURCE.get());
      if (status != vmm_rw::IS_OK) begin
         `vmm_fatal(this.log, "Unable to write-back INT_SOURCE");
      end

      // Analyze the cause(s) for the interrupt
      if (TXE) begin
         `vmm_error(this.log, "An error occured during the transmission of a frame");
      end
      
      if (TXE || TXB) begin
         integer n = 0;

         if (this.busy_txbd.size() == 0) begin
            `vmm_fatal(this.log, "Internal error: TXE/TXB indicated but no TxBD are busy");
         end

         // A frame has been transmitted, check the transmit buffers...
         while (this.busy_txbd.size() > 0) begin
            int bd_addr = this.busy_txbd[0];
            bit RD;

            // Check if that TxBD has been transmitted
            ral.TxBD[bd_addr].RD.read(status, RD);
            if (status != vmm_rw::IS_OK) begin
               `vmm_fatal(this.log,$psprintf("Unable to READ TxBD[%0d]",
                                             bd_addr));
            end

            // Has this frame been transmitted?
            if (RD) begin
               // No. This implies the subsequent frames have not
               // been transmitted either
               if (n == 0) `vmm_error(this.log, "No transmitted TxBD were found");
               break;
            end

            `vmm_trace(this.log, $psprintf("Frame from TxBD[%0d] was transmitted",
                                           bd_addr));

            // What errors happened when the frame was transmitted?
            if (ral.TxBD[bd_addr].UR.get()
                || ral.TxBD[bd_addr].RL.get()
                || ral.TxBD[bd_addr].LC.get()) begin
               string descr = "";
               string separator = " ";
               if (ral.TxBD[bd_addr].UR.get()) begin
                  descr = " Under-run";
                  separator = "/";
               end
               if (ral.TxBD[bd_addr].RL.get()) begin
                  descr = {descr, separator, "Retry Limit"};
                  separator = "/";
               end
               if (ral.TxBD[bd_addr].LC.get()) begin
                  descr = {descr, separator, "Late Coll"};
               end

               `vmm_warning(this.log, {"Frame was transmitted with following errors:", descr});
            end
                
            // What non-errors happened?
            `vmm_trace(this.log, $psprintf("Frame was transmitted with %0d attempts%s%s",
                                           ral.TxBD[bd_addr].RTRY.get(),
                                           (ral.TxBD[bd_addr].DF.get()
) ? ",ferred" : "",
                                           (ral.TxBD[bd_addr].CS.get()) ? ", carrier lost" : ""));
            

            // Indicate this TxBD is now available
            // and free the DMA memory
            n++;
            this.cfg.avail_txbd.push_back(bd_addr);
            void'(this.busy_txbd.pop_front());
            this.dma_mam.release_region(this.cfg.dma_bfrs[bd_addr]);
         end
      end // TXB
   endtask: service_irq
endclass


class oc_eth_subenv extends vmm_subenv;
   oc_eth_subenv_cfg      cfg;
   virtual mii_if.passive mii_sigs;
   eth_frame_channel      tx_chan;

   ral_block_oc_ethernet  ral;
   wb_ram                 dma_ram;
   vmm_mam                dma_mam;

   scoreboard             sb;

   eth_frame_atomic_gen   src;
   mii_monitor            mon;
   frmwr_emulator         frmwr;

   function new(string                 inst,
                oc_eth_subenv_cfg      cfg,
                vmm_consensus          end_test,
                virtual mii_if.passive mii_sigs,
                eth_frame_channel      tx_chan,
                ral_block_oc_ethernet  ral,
                wb_ram                 dma_ram,
                vmm_mam                dma_mam);
      super.new("OcEth SubEnv", inst, end_test);

      this.cfg      = cfg;
      this.mii_sigs = mii_sigs;

      if (tx_chan == null) begin
         this.src = new("OcEth SubEnv Src");
         tx_chan = this.src.out_chan;

         this.src.stop_after_n_insts = this.cfg.run_for_n_frames;

         // Make sure the frame generators generate frames with the
         // correct SA
         this.src.randomized_obj.src = this.cfg.dut_addr;
         this.src.randomized_obj.src.rand_mode(0);
      end
      this.tx_chan  = tx_chan;

      this.ral = ral;
      this.dma_ram = dma_ram;
      this.dma_mam = dma_mam;

      this.sb = new(inst, this.cfg);

      this.mon = new(inst, 0, this.cfg.mii, this.mii_sigs);
      this.frmwr = new(inst, 0, this.cfg, tx_chan, this.sb, this.ral,
                       this.dma_ram, this.dma_mam);
   endfunction: new

   task configure();
      vmm_rw::status_e status;

      ral.HUGEN.set(0);
      ral.CRCEN.set(0);
      ral.FULLD.set(1);
      ral.PRO.set(1);
      ral.TXE_M.set(1);
      ral.TXB_M.set(1);
      ral.IPGT.set(16'h15);
      ral.MINFL.set(16'h000F);
      ral.MAXFL.set(cfg.max_frame_len);
      ral.TXFLOW.set(1);
      ral.RXFLOW.set(1);
      ral.PASSALL.set(1);
      ral.MAC_ADDR.set(cfg.dut_addr);
      ral.TX_BD_NUM.set(cfg.n_tx_bd);
      ral.update(status);
      if (status !== vmm_rw::IS_OK) begin
         `vmm_error(this.log, $psprintf("Unable to configure \"%s\".",
                                        ral.get_name()));
      end

      // Initialize the required number of buffer descriptors
      begin
         int bd_addr = 0;

         `vmm_trace(this.log, $psprintf("Configuring %0d TxBD starting at BD[%0d]",
                                        cfg.n_tx_bd, bd_addr));
         repeat (cfg.n_tx_bd) begin
            ral.TxBD[bd_addr].TxBD_CTRL.set(32'h0000_0000);
            ral.TxBD[bd_addr].IRQ.set(1);
            if (bd_addr == cfg.n_tx_bd-1) ral.TxBD[bd_addr].WR.set(1'b1);
            
            ral.TxBD[bd_addr].RD.write(status, 0);
            if (status !== vmm_rw::IS_OK) begin
               `vmm_error(this.log, $psprintf("Unable to initialize (Tx)BD[%0d] in \"%s\".",
                                              bd_addr, ral.get_name()));
            end

            cfg.avail_txbd.push_back(bd_addr);
            
            bd_addr++;
         end
      end

      `vmm_trace(this.log, "Enabling Tx paths...");
      ral.TXEN.write(status, 1);
      if (status !== vmm_rw::IS_OK) begin
         `vmm_error(this.log, $psprintf("Unable to configure \"%s\".",
                                        ral.get_name()));
      end

      super.configured();
   endtask: configure

   virtual task start();
      super.start();
      
      if (this.cfg.run_for_n_frames > 0 && this.src != null) begin
         this.src.start_xactor();
      end
      this.frmwr.start_xactor();
      this.mon.start_xactor();

      fork
         forever begin
            eth_frame fr;
            this.mon.to_phy_chan.get(fr);
            this.sb.received_by_phy_side(fr);
         end
      join_none

      if (this.src != null) begin
         this.end_test.register_notification(this.src.notify,
                                             eth_frame_atomic_gen::DONE);
      end
      this.end_test.register_channel(this.tx_chan);
      this.end_test.register_channel(this.mon.to_phy_chan);
      this.end_test.register_xactor(this.frmwr);
      this.end_test.register_xactor(this.mon);
   endtask: start

   virtual task stop();
      super.stop();
      
      if (this.src != null) this.src.stop_xactor();
   endtask: stop

   virtual task cleanup();
      super.cleanup();

      if (this.cfg.run_for_n_frames > 0) begin
         `vmm_error(this.log,
                    $psprintf("%0d frames were not seen by the scoreboard",
                              this.cfg.run_for_n_frames));
      end
   endtask: cleanup
endclass: oc_eth_subenv

`endif
