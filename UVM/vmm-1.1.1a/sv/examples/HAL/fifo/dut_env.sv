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

//
// Description : FIFO Testbench vmm_environment class
//

class tb_env extends vmm_env ;

  // FIFO Master/Monitor Virtual Interface
  virtual intf  ifc;

  vmm_log log;                                   
  
  fifo_cfg cfg;                                 
                                               
  fifo_trans_channel gen2mas;                 
                                           
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
endfunction


//-----------------------------------------------------------------------------
// gen_cfg() - Generate a randomized testbench configuration
//-----------------------------------------------------------------------------
    
function void tb_env::gen_cfg() ;

  super.gen_cfg() ;

  if (cfg.randomize() == 0)                                              
    `vmm_fatal(log, "Failed to randomize testbench configuration");      

  `vmm_note(log, $psprintf("cfg.trans_cnt = %d", cfg.trans_cnt));        
endfunction


//-----------------------------------------------------------------------------
// build() - Build the testbench, xactors, scoreboard, callbacks
//-----------------------------------------------------------------------------
    
function void tb_env::build() ;

  super.build() ;

  gen2mas = new ("FIFO Trans Channel", "gen2mas") ;                       
  gen = new ("FIFO Atomic Gen", 1, gen2mas) ;                             
  mst = new ("FIFO trans master", 1, ifc, gen2mas );                      
  mon = new ("FIFO trans monitor", 1, ifc, mon2scb);                      

  scb = new(cfg.trans_cnt) ;                                    
  begin                                                                  //LAB6
    fifo_master_sb_callbacks  fifo_mst_sb_cb  = new(scb);                  //LAB6  
    fifo_monitor_sb_callbacks fifo_mon_sb_cb  = new(scb);                  //LAB6  
    mst.append_callback(fifo_mst_sb_cb);                                  //LAB6
    mon.append_callback(fifo_mon_sb_cb);                                  //LAB6
  end                                                                    //LAB6
                                                                         //LAB6

  gen.stop_after_n_insts = cfg.trans_cnt ;                               //LAB3
                                                                         //LAB7
endfunction: build


//-----------------------------------------------------------------------------
// reset_dut() - Reset the DUT
//-----------------------------------------------------------------------------
  
task tb_env::reset_dut();

  super.reset_dut();

  mst.reset();                                                           //LAB4
                                                                         //LAB4
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

  gen.start_xactor();                             
  mst.start_xactor();                            
  mon.start_xactor();                           
                                              
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

