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


`include "wishbone.sv"

module top;

initial $timeformat(0, 0, "ns", 1);

wb_if if0();

reg clk;
assign if0.clk = clk;
always begin
   #10;
   clk = 1'b0;
   #10;
   clk = 1'b1;
end

endmodule


program test;

class wb_env extends vmm_env;
   wb_slave_cfg cfg;
   wb_master master;
   wb_slave  slave;
   wb_ram    ram;

   wb_cycle tr;

   function new();
      this.cfg = new;
   endfunction: new


   virtual function void gen_cfg();
      super.gen_cfg();
      if (!this.cfg.randomize()) begin
         `vmm_fatal(this.log, "Unable to randomize configuration");
      end
      this.cfg.display("Using CFG: ");
      this.tr = new(this.cfg);
   endfunction: gen_cfg


   virtual function void build();
      super.build();
      this.master = new("0", 32'd0, this.cfg, top.if0.master);
      this.ram    = new("0", 32'd0);
      this.slave  = new("0", 32'd0, this.cfg, top.if0.slave,
                        this.ram.req_chan, this.ram.resp_chan);

      this.master.log.set_verbosity(vmm_log::DEBUG_SEV);
//      this.ram.log.set_verbosity(vmm_log::DEBUG_SEV);
      this.slave.log.set_verbosity(vmm_log::DEBUG_SEV);
   endfunction: build

   virtual task start();
      super.start();
      this.master.start_xactor();
      this.slave.start_xactor();
      this.ram.start_xactor();
   endtask: start
     
   virtual task wait_for_end();
      bit [63:0] tmp;
      int ok;

      wb_slave_cfg slv_cfg;

      super.wait_for_end();

      slv_cfg = this.cfg;
      for (int i = 0; i < 100; i++) begin
         this.tr.data_id = i;
         ok = this.tr.randomize() with { slv_cfg.min_addr <= addr &&
                                         addr <= slv_cfg.max_addr; };
         if (!ok) begin
            `vmm_fatal(log, "Unable to randomize a Wishbone cycle");
         end

         if (tr.kind == wb_cycle::READ ) begin
            tmp = tr.data;
            this.ram.write(tr.addr, tmp);
            tr.data = 64'hx;
         end

         this.master.exec_chan.put(this.tr);

         if (tr.kind == wb_cycle::WRITE ) begin
            tmp = this.ram.read(tr.addr);
            if (tmp !== tr.data) begin
               `vmm_error(this.log, $psprintf("RAM[%h] == %h, not %h after %0s cycle",
                                              tr.addr, tmp, tr.data, tr.kind.name()));
            end
         end

         $write("---------------------------------------------------------\n");
         tr.display();
         $write("=========================================================\n");


         // If there was a timeout, leave enough time for the salve to recover
         if (tr.status == wb_cycle::TIMEOUT ) repeat (10) @(top.if0.mck);
      end
   endtask: wait_for_end
     
endclass


wb_env env = new;

initial
begin
   env.run();
end

endprogram
