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


`include "vmm_ral.sv"

`include "wishbone.sv"
`include "mii.sv"

`include "ral_oc_ethernet.sv"
`include "eth_subenv.sv"

class test_cfg;
   rand oc_eth_subenv_cfg eth;

   rand wb_slave_cfg  ram;
   rand vmm_mam_cfg   mam;

   constraint test_cfg_valid {
      ram.port_size   == wb_cfg::DWORD;
      ram.granularity == wb_cfg::BYTE; 
      ram.cycles      == wb_cfg::CLASSIC;
      ram.min_addr    == 32'h0000_0000;
      ram.max_addr    == 32'hFFFF_FFFF;

      mam.n_bytes      == 1;
      mam.start_offset == ram.min_addr;
      mam.end_offset   == ram.max_addr;
   }

   function new();
      this.eth = new;
      this.ram = new;
      this.mam = new;
   endfunction: new

   function string psdisplay(string prefix = "");
      psdisplay = this.eth.psdisplay(prefix);
      $sformat(psdisplay, "%s\n%s", psdisplay, this.ram.psdisplay(prefix));
   endfunction
endclass: test_cfg


class wb_cycle_resp_no_wss extends wb_cycle_resp;
   function new(wb_cycle     req,
                wb_slave_cfg cfg);
      super.new(req, cfg);
   endfunction

   constraint no_wss {
      n_wss == 0;
   }

   function vmm_data copy(vmm_data to);
      wb_cycle_resp_no_wss tr;

      if (to == null) tr = new(null, null);
      else if (!$cast(tr, to)) begin
         `vmm_fatal(this.log, "Unable to copy to non-wb_cycle_resp_no_wss instance");
         return null;
      end

      return super.copy(tr);
   endfunction: copy

endclass


class ral_to_wb extends vmm_rw_xactor;
   wb_master bfm;
   wb_cfg    cfg;

   function new(string        inst,
                int unsigned  stream_id,
                wb_master     bfm,
                wb_cfg        cfg);
      super.new("WishBone RAL Master", inst, stream_id);

      this.bfm = bfm;
      this.cfg = cfg;
   endfunction: new

   virtual function void start_xactor();
      super.start_xactor();
      this.bfm.start_xactor();
   endfunction

   virtual function void stop_xactor();
      super.stop_xactor();
      this.bfm.stop_xactor();
   endfunction

   virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = vmm_xactor::SOFT_RST);
      super.reset_xactor(rst_typ);
      this.bfm.reset_xactor(rst_typ);
   endfunction

   virtual task execute_single(vmm_rw_access tr);
      wb_cycle cyc;
      bit ok;
      
      cyc = new(this.cfg);

      if (tr.kind == vmm_rw::WRITE) begin
         ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                    // BYTE granularity in DWORD bus size
                                    addr == tr.addr << 2;
                                    data == tr.data;
                                    sel  == 4'hF;
                                    lock == 1'b0;};
      end
      else begin
         ok = cyc.randomize() with {kind == wb_cycle::READ;
                                    // BYTE granularity in DWORD bus size
                                    addr == tr.addr << 2;
                                    sel  == 4'hF;
                                    lock == 1'b0;};
      end
      if (!ok) begin
         `vmm_fatal(this.log, {"Unable to translate generic RW access into WB cycle:\n",
                               tr.psdisplay("   "), "\n",
                               this.cfg.psdisplay("   ")});
         tr.status = vmm_rw::ERROR;
         return;
      end

      this.bfm.exec_chan.put(cyc);

      if (tr.kind == vmm_rw::READ) begin
         tr.data = cyc.data;
      end
      tr.status = (cyc.status == wb_cycle::ACK) ? vmm_rw::IS_OK : vmm_rw::ERROR;
   endtask: execute_single
endclass: ral_to_wb


//
// DMA Regions must start on a DWORD boundary
//
class allocate_on_dword extends vmm_mam_allocator;
   constraint dword_aligned {
      start_offset[1:0] == 2'b00;
   }
endclass: allocate_on_dword


class blk_env extends vmm_ral_env;
   test_cfg cfg;

   oc_eth_subenv eth;

   ral_block_oc_ethernet ral_model;

   wb_slave  slv;
   wb_ram    ram;
   vmm_mam   dma_mam;

   mii_phy_layer phy;

   wb_master host;
   ral_to_wb ral_xlate;

   function new();
      super.new();
      this.cfg = new;

      this.ral_model = new(0);
      this.ral.set_model(this.ral_model);

      $timeformat(-9, 0, "ns", 1);
   endfunction: new

   virtual function void gen_cfg();
      bit ok;
      super.gen_cfg();

      ok = this.cfg.randomize();
      if (!ok) begin
         `vmm_fatal(log, "Failed to randomize test configuration");
      end
   endfunction: gen_cfg


   virtual function void build();
      super.build();

      `vmm_note(this.log, this.cfg.psdisplay());

      this.phy = new("PHY Side", 0, this.cfg.eth.mii,
                     blk_top.mii.phy_layer);
      this.phy.tx_chan.sink();
      begin
         wb_cycle_resp_no_wss no_wss_resp = new(null, this.cfg.ram);
         this.ram  = new("RAM",  1, null, null, no_wss_resp);
      end
      this.slv  = new("Slave",  1, this.cfg.ram, blk_top.wb_ma,
                      this.ram.req_chan, this.ram.resp_chan);

      this.dma_mam = new("WB DMA", this.cfg.mam);
      begin
         allocate_on_dword alloc = new;
         this.dma_mam.default_alloc = alloc;
      end

      this.host = new("Host", 1, this.cfg.ram, blk_top.wb_sl);
      this.ral_xlate = new("RAL<->WB", 0, this.host, this.cfg.ram);
      this.ral.add_xactor(this.ral_xlate);

      this.eth = new("Eth", this.cfg.eth, this.end_vote,
                     blk_top.mii.passive, null,
                     this.ral_model, this.ram, this.dma_mam);

      this.log.disable_types(vmm_log::INTERNAL_TYP , "/./", "/./");

      this.eth.log.set_verbosity(vmm_log::TRACE_SEV);
      this.phy.log.set_verbosity(vmm_log::DEBUG_SEV);
      this.eth.mon.log.set_verbosity(vmm_log::DEBUG_SEV);
      this.eth.frmwr.log.set_verbosity(vmm_log::TRACE_SEV);
   endfunction: build


   virtual task hw_reset();
      blk_top.rst <= 1;
      repeat (3) @ (posedge blk_top.wb_clk);
      blk_top.rst <= 0;
   endtask: hw_reset

      
   virtual task cfg_dut();
      super.cfg_dut();
      this.eth.configure();
   endtask: cfg_dut

   virtual task start();
      super.start();

      fork
         forever begin
            wait(blk_top.wb_int);
            this.eth.frmwr.service_irq();
         end
      join_none

      this.phy.start_xactor();
      this.slv.start_xactor();
      this.ram.start_xactor();
      this.eth.start();

      this.end_vote.register_channel(this.host.exec_chan);
      this.end_vote.register_xactor(this.phy);
      this.end_vote.register_xactor(this.host);
   endtask: start

   virtual task wait_for_end();
      super.wait_for_end();

      // Give enough time for the first frame to start coming out
      // and make the PHY busy
      repeat (100) @ (blk_top.tx_clk);

      this.end_vote.wait_for_consensus();
   endtask: wait_for_end

   virtual task stop();
      super.stop();
      this.eth.stop();
   endtask: stop

   virtual task cleanup();
      super.cleanup();
      this.eth.cleanup();
   endtask: cleanup
endclass: blk_env
