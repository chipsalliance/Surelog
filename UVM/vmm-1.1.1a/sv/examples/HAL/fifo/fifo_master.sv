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
// Description :  FIFO QuickStart 
//
//               This is a vmm_xactor class for a FIFO Master
//
//   This BFM receives FIFO transactions from a channel, and drives
//   the pins via the SystemVerilog virtual interface.
//
//           |      |          
//           | FIFO |  VMM channel
//           | trans|   
//           |  VV  |
//           |      |
//    +--------------------+
//    |     FIFO-Master    |
//    +--------------------+
//           |||||||
//           |||||||
//           FIFO Bus
//

  
class fifo_master extends vmm_xactor;

    local vmm_hw_in_port _port; 

    // FIFO Transaction channels
    fifo_trans_channel  in_chan ;

    extern function new (string inst,         
                         integer stream_id = -1,
                         vmm_hw_in_port port,
                         fifo_trans_channel in_chan = null);   

    extern virtual task main() ; 
    
    extern protected virtual task fifo_mwrite(ref fifo_trans tr) ; 
    extern protected virtual task fifo_mread(fifo_trans tr) ;
  
endclass: fifo_master

//-----------------------------------------------------------------------------
// FIFO Master Callback Class
//-----------------------------------------------------------------------------

virtual class fifo_master_callbacks extends vmm_xactor_callbacks;

   // Callbacks before a transaction is started
   virtual task master_pre_tx(fifo_master    xactor,
                              ref fifo_trans trans,
                              ref bit        drop);
   endtask

   // Callback after a transaction is completed
   virtual task master_post_tx(fifo_master xactor,
                               fifo_trans  trans);
   endtask

endclass: fifo_master_callbacks
    
//-----------------------------------------------------------------------------
// new() - Constructor
//-----------------------------------------------------------------------------

function fifo_master::new(string inst,
                         integer stream_id = -1,
                         vmm_hw_in_port port,
                         fifo_trans_channel in_chan = null);

  // Call the super task to initialize the xactor    
  super.new("FIFO MASTER", inst, stream_id) ;

  _port = port;

  // Allocate an input channel if needed, save a reference to the channel
  if (in_chan == null) in_chan = new("FIFO MASTER INPUT CHANNEL", inst); 
  this.in_chan       = in_chan;
endfunction: new


//-----------------------------------------------------------------------------
// main() - RVM main
//-----------------------------------------------------------------------------
// Main daemon. Runs forever to switch FIFO transaction to
// corresponding read/write/idle command
//-----------------------------------------------------------------------------

task fifo_master::main();

  fifo_trans tr;
  bit drop;

  // Fork off the super.main() to perform any base-class tasks
  fork
    super.main();
  join_none

  // Main loop to drive the FIFO Bus
  while (1) begin
    
    // Wait if the xactor is stopped on the in_chan is empty
    // Get a transaction from the input channel
    this.wait_if_stopped_or_empty(this.in_chan) ;
    in_chan.get(tr);

    // Pre-Tx callback
    `vmm_callback(fifo_master_callbacks, master_pre_tx(this, tr, drop));
    if (drop == 1) continue;

    `vmm_trace(this.log, tr.psdisplay("Executing: "));
    // Process the transaction
    fifo_mwrite(tr);
    fifo_mread(tr);
    `vmm_callback(fifo_master_callbacks, master_post_tx(this, tr)); 
  end
    
endtask: main


// fifo_mwrite() - Issue a FIFO Write Cycle
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
   
task fifo_master::fifo_mwrite(ref fifo_trans tr);
   _port.send({1'b1, tr.data, tr.wr_data_rate } );            
endtask: fifo_mwrite

      
//-----------------------------------------------------------------------------
// fifo_mread() - Issue an FIFO Read Cycle
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
  
task  fifo_master::fifo_mread(fifo_trans tr);
   _port.send({1'b0, 16'b0, tr.rd_data_rate } );
endtask: fifo_mread 

