// 
// -------------------------------------------------------------
//    Original file had no explicit Synopsys copyright
//    Copyright 2009 Mentor Graphics Corporation
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
`include "vmm_perf.sv"

`include "bus_tr.sv"
`include "bus_slave.sv"
`include "bus_model.sv"


class test_cfg;
   rand bus_cfg      bus          = new;
   rand int unsigned run_for      = 100;
   rand int unsigned max_latency  = 1;
   rand int unsigned max_interval = 1;

   bit perf_on = 0;

   constraint test_cfg_valid {
      max_latency  > 10;
      max_interval > 30;
   }

   constraint reasonable {
      max_latency  < 20;
      max_interval < 100;
      run_for      < 1000;
   }
endclass


typedef class tb_env;

class master_interval extends bus_tr_atomic_gen_callbacks;
   tb_env env;

   function new(tb_env env);
      this.env = env;
   endfunction: new

   virtual task post_inst_gen(bus_tr_atomic_gen gen,
                              bus_tr            obj,
                              ref bit           drop);
      #($random % this.env.cfg.max_interval);
   endtask
endclass: master_interval


class bus_tr_tenure extends bus_tr_atomic_gen_callbacks;
   tb_env env;

   function new(tb_env env);
      this.env = env;
   endfunction: new

   virtual task post_inst_gen(bus_tr_atomic_gen gen,
                              bus_tr            obj,
                              ref bit           drop);
      bus_tr tr = obj;
      fork
         // Measure transaction throughput performance
         begin
            vmm_perf_tenure tenure = new(gen.stream_id,
                                         tr.addr[31:16] % this.env.cfg.bus.n_slaves,
                                         tr);
            tr.notify.wait_for(vmm_data::STARTED);
            this.env.bus_perf.start_tenure(tenure);

            tr.notify.wait_for(vmm_data::ENDED);
            if (tr.status != bus_tr::IS_OK) this.env.bus_perf.abort_tenure(tenure);
            else this.env.bus_perf.end_tenure(tenure);
         end

         // Measure bus request performance
         begin
            vmm_perf_tenure tenure = new(gen.stream_id, -1, tr);
            this.env.arb_perf.start_tenure(tenure);
            tr.notify.wait_for(vmm_data::STARTED);
            this.env.arb_perf.end_tenure(tenure,
                                         $psprintf("%0d", $time));
         end
      join_none
   endtask
endclass: bus_tr_tenure


class tb_env extends vmm_env;
   test_cfg cfg;

   bus_tr_atomic_gen masters[];
   bus_slave         slaves[];

   bus_model bus;

   vmm_sql_db  db;
   vmm_perf_analyzer bus_perf;
   vmm_perf_analyzer arb_perf;

   function new();
      super.new();
      this.cfg = new;
   endfunction: new

   virtual function void gen_cfg();
      super.gen_cfg();
      if (!this.cfg.randomize()) begin
         `vmm_fatal(log, "Cannot randomize test configuration");
      end
   endfunction: gen_cfg

   virtual function void build();
      master_interval interval_cb = new(this);
      bus_tr_tenure   perf_cb     = new(this);

      super.build();

      this.bus = new("SoC Bus", this.cfg.bus);

      if (this.cfg.perf_on) begin
`ifdef USE_SQLITE
         vmm_sql_db_sqlite db = new("sql_data.db");
`endif
`ifdef USE_SQLTXT
         vmm_sql_db_ascii db = new("sql_data.sql");
`endif
         this.db = db;

         // Save the environment/DUT configuration to DB
         begin
            vmm_sql_table cfg_tbl = db.create_table("cfg",
                                                    "num_mstrs INTEGER, num_slvs INTEGER");
            cfg_tbl.insert($psprintf("%0d, %0d",
                                     this.cfg.bus.n_masters,
                                     this.cfg.bus.n_slaves));
            db.commit();
         end

         this.bus_perf = new("Bus", db);
         this.arb_perf = new("Arb", db, 0, 0, this.masters.size(), "stamp BIGINT");
      end

      this.masters = new [this.cfg.bus.n_masters];
      `foreach (this.masters,i) begin
         int j = i;
         this.masters[i] = new($psprintf("%0d", i), j,
                               this.bus.master_chan[i]);
         this.masters[i].append_callback(interval_cb);

         if (this.cfg.perf_on) this.masters[i].append_callback(perf_cb);
      end

      this.slaves  = new [this.cfg.bus.n_slaves];
      `foreach (this.slaves,i) begin
         int j = i;
         this.slaves[i] = new($psprintf("%0d", i), j,
                               this.bus.slave_chan[i],
                               this.cfg.max_latency);
      end
   endfunction: build

   virtual task start();
      super.start();

      this.bus.start_xactor;
      `foreach (this.masters,i) begin
         this.masters[i].start_xactor();
      end
      `foreach (this.slaves,i) begin
         this.slaves[i].start_xactor();
      end
   endtask: start

   virtual task wait_for_end();
      super.wait_for_end();

      repeat (this.cfg.run_for) begin
         this.bus.notify.wait_for(this.bus.EXECUTED);
      end
   endtask: wait_for_end

   virtual task stop();
      super.stop();

      `foreach (this.masters,i) begin
         this.masters[i].stop_xactor();
      end

      // Wait until all master channels are empty
      repeat (3) begin
         `foreach (this.bus.master_chan,i) begin
            this.bus.master_chan[i].notify.wait_for(vmm_channel::EMPTY);
         end
      end
      #0; // need to give chance for "tenure" process to wake up on vmm_data::ENDED
   endtask: stop

   virtual task report();
      if (this.cfg.perf_on) begin
         this.bus_perf.save_db();
         this.bus_perf.report();

         this.arb_perf.save_db();
         this.arb_perf.report();
      end
      super.report();
   endtask: report

endclass: tb_env

`endif
