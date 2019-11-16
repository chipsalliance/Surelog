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

//
// Description : FIFO Testbench vmm_environment class
//
// This class instantiates all the permanent testbench top-level components
//   * FIFO Atomic Generator
//   * FIFO Master
//   * FIFO Monitor
//   * Scoreboard
//


`ifndef TB_ENV__SV
`define TB_ENV__SV

// Move to test.sv. tb_env contains references to tb_top. It must be `included
// inside a program block. So any include files here can not contain
// interface,module,program,etc. fifo_vip contains interfaces
//`include "tb_top.v"
`include "fifo_vip.sv"
`include "dut_sb.sv"
`include "sb_callbacks.sv"

class env_cfg;

  bit on_emulator = 0;

  // How many transactions to generate before test ends?
  rand int trans_cnt;

  constraint env_cfg_valid {
    trans_cnt > 5;
  }

  constraint reasonable {
    if (on_emulator) {
        trans_cnt >   10000000;
        trans_cnt < 1000000000;
    } else {
        trans_cnt < 1000;
    }
  }

  constraint emulation {
    
  }
endclass: env_cfg


class tb_env extends vmm_env ;

  vmm_log log;

  vmm_hw_arch arch;
  env_cfg cfg;                                 
                                               
  vmm_hw_in_port  reset_req_prt;
  vmm_hw_out_port reset_ack_prt;

  fifo_trans_channel gen2mas;                 
  fifo_trans_channel mon2scb;               
                                           
  fifo_trans_atomic_gen gen;              
                                         
  fifo_master            mst;           
  fifo_monitor           mon;         

  dut_sb                scb;     
                                  
  // Constructor
  extern function new();

  // VMM Environment Steps
  extern virtual function void gen_cfg();
  extern virtual function void build();
  extern virtual task reset_dut();
  extern virtual task cfg_dut();
  extern virtual task start();
  extern virtual task wait_for_end();
  extern virtual task stop();
  extern virtual task cleanup();
  extern virtual task report();

endclass: tb_env


  
function tb_env::new();
   super.new("TB_ENV");
    
   log = new("dut", "env");                                             
   this.cfg = new() ;

`ifdef VMM_HW_ARCH_NULL
  begin
     vmm_hw_arch_null a = new;
     this.arch = a;
  end
`endif

endfunction


//-----------------------------------------------------------------------------
// gen_cfg() - Generate a randomized testbench configuration
//-----------------------------------------------------------------------------
    
function void tb_env::gen_cfg() ;
  super.gen_cfg() ;

  if (cfg.randomize() == 0)                                              
    `vmm_fatal(log, "Failed to randomize testbench configuration");      
endfunction


//-----------------------------------------------------------------------------
// build() - Build the testbench, xactors, scoreboard, callbacks
//-----------------------------------------------------------------------------
    
function void tb_env::build() ;
   vmm_hw_in_port ip;
   vmm_hw_out_port op;

   super.build() ;

   arch.clk_control(tb_top.tb_clk.vitf, tb_top.hw_rst.bfm.tb_ctl.vitf);
   arch.clk_control(tb_top.tb_clk.vitf, tb_top.bfm_write.clk1.vitf);

   this.reset_req_prt = arch.create_in_port(tb_top.hw_rst.bfm.reset_req_if.vitf, "");
   this.reset_ack_prt = arch.create_out_port(tb_top.hw_rst.bfm.reset_ack_if.vitf, "");

   gen2mas = new ("FIFO Trans Channel", "gen2mas") ;                       
   mon2scb = new ("FIFO Trans Channel", "mon2scb") ;                       
   gen = new ("FIFO Atomic Gen", 1, gen2mas) ;
   ip = arch.create_in_port(tb_top.bfm_write.msg1.vitf, "");
   mst = new ("FIFO trans master", 1, ip, gen2mas);
   op = arch.create_out_port(tb_top.bfm_write.msg2.vitf, "");
   mon = new ("FIFO trans monitor", 1, op, mon2scb);

   scb = new(cfg.trans_cnt);
   begin
     fifo_master_sb_callbacks  fifo_mst_sb_cb  = new(scb);
     fifo_monitor_sb_callbacks  fifo_mon_sb_cb  = new(scb);
     mst.append_callback(fifo_mst_sb_cb);
     mon.append_callback(fifo_mon_sb_cb);
   end

   gen.stop_after_n_insts = cfg.trans_cnt ;

   arch.init_sim();
endfunction: build


//-----------------------------------------------------------------------------
// reset_dut() - Reset the DUT
//-----------------------------------------------------------------------------
  
task tb_env::reset_dut();
   bit [1023:0] junk;
   time stamp;

   super.reset_dut();
   $display("pre reset_req_prt"); 
   this.reset_req_prt.send(1'b1);
   $display("pre reset_ack_prt"); 
   this.reset_ack_prt.receive(junk, stamp);
   $display("Done with reset stuff..."); 
endtask:reset_dut


//-----------------------------------------------------------------------------
// cfg_dut() - Configure the DUT
//-----------------------------------------------------------------------------

task tb_env::cfg_dut();
    
   super.cfg_dut() ;

endtask: cfg_dut


//-----------------------------------------------------------------------------
// start() - Start each of the xactors
//-----------------------------------------------------------------------------
    
task tb_env::start();

   super.start();

   mon.start_xactor();                           
   mst.start_xactor();
   gen.start_xactor();
endtask: start


//-----------------------------------------------------------------------------
// wait_for_end() - Wait until the test completes
//-----------------------------------------------------------------------------

task tb_env::wait_for_end();
   super.wait_for_end();

   fork                                 
      gen.notify.wait_for(fifo_trans_atomic_gen::DONE); 
      scb.notify.wait_for(scb.DONE);                 
   join                                              
endtask: wait_for_end
            

//-----------------------------------------------------------------------------
// stop() - Stop each of the xactors
//-----------------------------------------------------------------------------
    
task tb_env::stop();
   super.stop() ;

   gen.stop_xactor();       
   mst.stop_xactor();      
   mon.stop_xactor();     
endtask: stop


//-----------------------------------------------------------------------------
// cleanup() - Cleanup the testbench, report any scoreboard errors etc.
//-----------------------------------------------------------------------------

task tb_env::cleanup();
  super.cleanup() ; 

  scb.cleanup();    
endtask


//-----------------------------------------------------------------------------
// report() - Report Statistics from the testbench
//-----------------------------------------------------------------------------

task tb_env::report() ;
  super.report() ;
endtask

`endif
