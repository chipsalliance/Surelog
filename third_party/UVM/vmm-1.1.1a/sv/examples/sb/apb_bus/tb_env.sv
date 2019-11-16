// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2008-2009 Mentor Graphics Corporation
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


`ifndef TB_ENV__SV
`define TB_ENV__SV

`include "vmm.sv"

`include "apb.sv"

`include "vmm_sb.sv"

class m2s_sb extends vmm_sb_ds;
   function new();
      super.new("Master->Slave");

      this.define_stream(0, "Master",  INPUT);
      this.define_stream(0, "Slave 0", EXPECT);
      this.define_stream(1, "Slave 1", EXPECT);
      this.define_stream(2, "Slave 2", EXPECT);
   endfunction: new

   virtual function bit transform(input  vmm_data in_pkt,
                                  output vmm_data out_pkts[]);
      apb_rw tr;

      $cast(tr, in_pkt.copy());
      tr.addr[31:8] = '0;
      out_pkts = new [1];
      out_pkts[0] = tr;
      return 0;
   endfunction: transform

   virtual function bit compare(vmm_data actual,
                                vmm_data expected);
      apb_rw act, exp;
      $cast(act, actual);
      $cast(exp, expected);

      if (act.kind == apb_rw::WRITE) begin
         string diff;
         return act.compare(exp, diff);
      end

      return (act.kind == exp.kind) &&
             (act.addr == exp.addr);
   endfunction: compare
endclass: m2s_sb


class s2m_sb extends vmm_sb_ds;
   function new();
      super.new("Slave->Master");

      this.define_stream(0, "Slave 0", INPUT);
      this.define_stream(1, "Slave 1", INPUT);
      this.define_stream(2, "Slave 2", INPUT);
      this.define_stream(0, "Master",  EXPECT);
   endfunction: new

   virtual function bit compare(vmm_data actual,
                                vmm_data expected);
      apb_rw act, exp;
      $cast(act, actual);
      $cast(exp, expected);

      if (act.kind == apb_rw::WRITE) return 1;

      return (act.data == exp.data);
   endfunction: compare
endclass: s2m_sb


class apb_master_to_sb extends apb_master_cbs;
   m2s_sb m2s;
   s2m_sb s2m;

   function new(m2s_sb m2s, s2m_sb s2m);
      this.m2s = m2s;
      this.s2m = s2m;
   endfunction: new

   virtual task pre_cycle(apb_master xactor,
                          apb_rw     cycle,
                          ref bit    drop);
      // Don't add to scoreboard if the address
      // won't match a slave
      if (cycle.addr[9:8] == 2'b11) return;

      void'(this.m2s.insert(cycle, vmm_sb_ds::INPUT,
                            .exp_stream_id(cycle.addr[9:8])));
   endtask: pre_cycle

   virtual task post_cycle(apb_master xactor,
                           apb_rw     cycle);
      // Don't check scoreboard if the address
      // didn't match a slave
      if (cycle.addr[9:8] == 2'b11) return;

      // Nor if this was a WRITE cycle
      if (cycle.kind == apb_rw::WRITE) return;

      void'(this.s2m.expect_in_order(cycle,
                                     .inp_stream_id(cycle.addr[9:8])));
   endtask: post_cycle

endclass: apb_master_to_sb


class tb_env extends `VMM_ENV;
   m2s_sb m2s = new;
   s2m_sb s2m = new;

   apb_rw_atomic_gen gen;
   apb_master        mst;
   apb_slave         slv[3];
   apb_rw_channel    resp_chan[3];

   int n_insts;

   function new();
     super.new("APB Env");
   endfunction

   function void gen_cfg();
     super.gen_cfg();
     n_insts = 100;
   endfunction

   virtual function void build();
      super.build();
      this.gen = new("APB Gen", 0);
      this.gen.stop_after_n_insts = n_insts;

      this.mst = new("Master", 0, tb_top.m, this.gen.out_chan);
      begin
         apb_master_to_sb cbs = new(this.m2s, this.s2m);
         this.mst.append_callback(cbs);
      end

      this.resp_chan[0] = new("Response", "0");
      this.resp_chan[1] = new("Response", "1");
      this.resp_chan[2] = new("Response", "2");

      this.slv[0] = new("Slave #0", 0, tb_top.s0, , this.resp_chan[0]);
      this.slv[1] = new("Slave #1", 1, tb_top.s1, , this.resp_chan[1]);
      this.slv[2] = new("Slave #2", 2, tb_top.s2, , this.resp_chan[2]);

      `ifdef VMM_OVM_INTEROP
      this.ovm_build();
      `endif
   endfunction: build

   virtual task start();
      super.start();
      this.gen.start_xactor();
      this.mst.start_xactor();
      `foreach_sa(this.slv,3,i) this.slv[i].start_xactor;

      `foreach_sa (this.resp_chan,3,i) begin
         int j = i;
         fork
            forever begin
               apb_rw tr;
               this.resp_chan[j].peek(tr);

               `vmm_debug(this.log, $psprintf("Request to Slave #%0d:\n%s",
                                              j, tr.psdisplay("   ")));

               void'(this.m2s.expect_in_order(tr, j));
               if (tr.kind == apb_rw::READ) begin
                  tr.data = $random; // Poor random strategy!
                  void'(this.s2m.insert(tr, vmm_sb_ds::INPUT,
                                        .inp_stream_id(j)));
               end

               `vmm_trace(this.log, $psprintf("Response from Slave #%0d:\n%s",
                                              j, tr.psdisplay("   ")));

               this.resp_chan[j].get(tr);
            end
         join_none
      end
   endtask: start

   virtual task wait_for_end();
      super.wait_for_end();
      this.gen.notify.wait_for(apb_rw_atomic_gen::DONE);
   endtask: wait_for_end

endclass: tb_env

`endif
