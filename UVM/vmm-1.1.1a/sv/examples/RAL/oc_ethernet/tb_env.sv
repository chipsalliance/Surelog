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
`include "ral_oc_ethernet.sv"

class test_cfg;
   rand wb_slave_cfg  wb;
      
   constraint test_cfg_valid {
      wb.port_size   == wb_cfg::DWORD;
      wb.granularity == wb_cfg::BYTE; 
      wb.cycles      == wb_cfg::CLASSIC;
   }

   function new();
      this.wb  = new;
   endfunction: new
endclass: test_cfg


class wb_ral_master extends vmm_rw_xactor;
   wb_cfg    cfg;
   wb_master wb;

   function new(string                inst,
                int unsigned          stream_id,
                wb_cfg                cfg,
                virtual wb_if.master  sigs,
                vmm_rw_access_channel exec_chan = null);
      super.new("Wishbone RAL Master", inst, stream_id, exec_chan);

      this.cfg = cfg;
      this.wb = new(inst, stream_id, cfg, sigs);
   endfunction: new

   
   virtual task execute_single(vmm_rw_access tr);
      wb_cycle cyc;
      bit      ok;
      
      // Translate the generic RW into a wishbone RW
      cyc = new(this.cfg);

      cyc.data_id     = tr.data_id;
      cyc.scenario_id = tr.scenario_id;
      cyc.stream_id   = tr.stream_id;
      
      // Avoid randomization failures
      if (tr.kind == vmm_rw::READ) tr.data = 0;
      ok = cyc.randomize() with {
         cyc.addr == tr.addr << 2; // BYTE granularity in DWORD bus size
         cyc.sel  == 4'hF;         // 32-bit bus
         cyc.lock == 0;
         if (tr.kind == vmm_rw::WRITE) {
            cyc.kind == wb_cycle::WRITE;
            cyc.data == tr.data;
         } else {
            cyc.kind == wb_cycle::READ;
         }
      };
      if (!ok) begin
        `vmm_error(this.log, "Cannot translate RAL R/W cycle into equivalent Wishbone R/W cycle");
         tr.status = vmm_rw::ERROR;
         return;
      end

      this.wb.exec_chan.put(cyc);

      // Send the result back to the RAL
      case (cyc.status)
         wb_cycle::ACK: tr.status = vmm_rw::IS_OK;
         wb_cycle::RTY: tr.status = vmm_rw::RETRY;
         default      : tr.status = vmm_rw::ERROR;
      endcase
      if (tr.kind == vmm_rw::READ) begin
         tr.data = cyc.data;
      end
      else begin
         // Let the assignment to registers physically happen
         // to make sure an immediate back-door readback will
         // read the just-written value
         #2;
      end
   endtask: execute_single

   virtual function void start_xactor();
      super.start_xactor();
      this.wb.start_xactor();
   endfunction: start_xactor

   virtual function void stop_xactor();
      super.stop_xactor();
      this.wb.stop_xactor();
   endfunction: stop_xactor

   virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
      super.reset_xactor(rst_typ);
      this.wb.reset_xactor(rst_typ);
   endfunction: reset_xactor
endclass: wb_ral_master


class tb_env extends vmm_ral_env;
   test_cfg cfg;
   wb_ral_master host;

   ral_block_oc_ethernet ral_model;

   function new();
      super.new();
      this.cfg = new;
      this.ral_model = new();
      super.ral.set_model(this.ral_model);
      $timeformat(-9, 0, "ns", 1);
   endfunction: new

   virtual function void gen_cfg();
      super.gen_cfg();

      this.cfg.wb.max_addr = 32'hFFFF_FFFF;
      this.cfg.wb.min_addr = 32'h0000_0000;
      this.cfg.wb.max_addr.rand_mode(0);
      this.cfg.wb.min_addr.rand_mode(0);

      if (!this.cfg.randomize()) begin
         `vmm_fatal(log, "Failed to randomize test configuration");
      end
   endfunction: gen_cfg


   virtual function void build();
      super.build();

      this.host = new("Host", 1, this.cfg.wb, tb_top.wb_sl);
      super.ral.add_xactor(this.host);
   endfunction: build


   virtual task hw_reset();
      tb_top.rst <= 1;
      repeat (3) @ (posedge tb_top.wb_clk);
      tb_top.rst <= 0;
   endtask: hw_reset
   
      
   virtual task cfg_dut();
      super.cfg_dut();
   endtask: cfg_dut


   virtual task start();
      super.start();
   endtask: start


   virtual task wait_for_end();
      super.wait_for_end();
      repeat (100) @ (posedge tb_top.wb_clk);
   endtask: wait_for_end


   virtual task stop();
      super.stop();
   endtask: stop


   virtual task cleanup();
      super.cleanup();
   endtask: cleanup
endclass: tb_env
