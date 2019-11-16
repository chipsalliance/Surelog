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



`include "vmm.sv"
`ifdef VCS_SEP_COMP
import alu_pkg::*;
`else
`include "alu_data.sv"
`include "alu_driver.sv"
`include "alu_mon.sv"
`include "alu_cfg.sv"
`include "alu_sb.sv"
`include "alu_mon2sb_connector.sv"
`include "alu_cov.sv"
`include "alu_mon2cov_connector.sv"
`endif

class alu_env extends vmm_env;
   
   vmm_log log;

   alu_driver            drv;
   alu_mon               mon;
   alu_data_atomic_gen   gen;
   alu_cfg               cfg;
   alu_data_channel      alu_chan;
   alu_sb                sb;
   alu_mon2sb_connector  mon2sb;
   alu_cov               cov;
   alu_mon2cov_connector mon2cov;
   virtual alu_if.drvprt alu_drv_port;
   virtual alu_if.monprt alu_mon_port;

   function new(virtual alu_if.drvprt alu_drv_port, 
                virtual alu_if.monprt alu_mon_port);
     log = new ("alu_env", "class");
     cfg = new;
     this.alu_drv_port = alu_drv_port;
     this.alu_mon_port = alu_mon_port;
   endfunction

   virtual function void gen_cfg();
      super.gen_cfg();  
      void'(cfg.randomize());
   endfunction

   virtual function void build();
      super.build();
      alu_chan = new ("ALU", "channel");
      drv = new("Driver", 0, alu_drv_port, alu_chan);
      gen = new("Gen", 0, alu_chan);
      gen.stop_after_n_insts = cfg.num_scenarios;
      if (cfg.monitor_en) begin
        mon = new("Mon", 0, alu_mon_port);
        sb = new;
        mon2sb = new(sb);
        mon.append_callback(mon2sb);
        cov = new;
        mon2cov = new(cov);
        mon.append_callback(mon2cov);
      end
   endfunction

   virtual task reset_dut();
     super.reset_dut();
     alu_drv_port.rst_n <= 0;
     repeat (5) @(alu_drv_port.cb);
     alu_drv_port.rst_n <= 1;
   endtask

   virtual task cfg_dut();
      super.cfg_dut();
   endtask

   virtual task start() ;
      super.start;
      drv.start_xactor();
      gen.start_xactor();
      if (cfg.monitor_en) mon.start_xactor();
   endtask

   virtual task wait_for_end() ;
      super.wait_for_end;
      this.gen.notify.wait_for(alu_data_atomic_gen::DONE);
      #100;
   endtask

   virtual task cleanup();
      super.cleanup();
      if (this.sb != null) this.sb.report();
   endtask
endclass


