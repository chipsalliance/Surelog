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
// Description : Scoreboard Integration/Callbacks
//
//               This class is DUT specific, and connects the scoreboard
//               to the Testbench.

//-----------------------------------------------------------------------------
// Scoreback Connection via APB Master Callback Class
//-----------------------------------------------------------------------------

typedef class fifo_master;
typedef class dut_sb;
    
class fifo_master_sb_callbacks extends fifo_master_callbacks;

  dut_sb sb;
    
  // Constructor
  function new(dut_sb sb);
    this.sb = sb;
  endfunction: new
    
  // Callbacks before a transaction is started
  virtual task master_pre_tx(fifo_master    xactor,
                             ref fifo_trans trans,
                             ref bit        drop);
   // Empty
  endtask

  // Callback after a transaction is completed
  virtual task master_post_tx(fifo_master xactor,
                              fifo_trans  trans);
    // Lab6 - call the scoreboard task from_master() and pass trans
    sb.from_master(trans);                                               //LAB6
  endtask

endclass: fifo_master_sb_callbacks


//-----------------------------------------------------------------------------
// APB Monitor Callback Class
//-----------------------------------------------------------------------------

typedef class fifo_monitor;
  
class fifo_monitor_sb_callbacks extends fifo_monitor_callbacks;

  dut_sb sb;
    
   // Constructor
  function new(dut_sb sb);
    this.sb = sb;
  endfunction: new

  // Callbacks before a transaction is started
  virtual task monitor_pre_rx(fifo_monitor    xactor,
                              ref fifo_trans trans);
  endtask

  // Callback after a transaction is completed
  virtual task monitor_post_rx(fifo_monitor xactor,
                               fifo_trans  trans);
      this.sb.from_monitor(trans);
  endtask

endclass: fifo_monitor_sb_callbacks
