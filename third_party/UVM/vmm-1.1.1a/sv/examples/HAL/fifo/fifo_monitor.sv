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


//-----------------------------------------------------------------------------
// FIFO Monitor Transactor Class
//-----------------------------------------------------------------------------
  
class fifo_monitor extends vmm_xactor;
  
  // Factory Object for creating fifo_trans
  fifo_trans randomized_obj;

  local vmm_hw_out_port _portrcv;

  // Output Channel
  fifo_trans_channel out_chan;

  extern function new(string inst,
                      int stream_id = -1,
                      vmm_hw_out_port port,
                      fifo_trans_channel out_chan = null);

  extern virtual task main() ;

  extern virtual task sample_fifo(ref fifo_trans tr);
    
endclass: fifo_monitor


//-----------------------------------------------------------------------------
// FIFO Monitor Callback Class
//-----------------------------------------------------------------------------

typedef class fifo_monitor;
  
virtual class fifo_monitor_callbacks extends vmm_xactor_callbacks;

   // Callbacks before a transaction is started
   virtual task monitor_pre_rx(fifo_monitor    xactor,
                               ref fifo_trans trans);
   endtask

   // Callback after a transaction is completed
   virtual task monitor_post_rx(fifo_monitor xactor,
                                fifo_trans  trans);
   endtask

endclass: fifo_monitor_callbacks
    

//-----------------------------------------------------------------------------
// new() - Constructor
//-----------------------------------------------------------------------------
  
function fifo_monitor::new(string inst,
                          int stream_id = -1,
                           vmm_hw_out_port port,
                          fifo_trans_channel out_chan = null);

  super.new("FIFO TRANS monitor", inst, stream_id) ;

  _portrcv = port;

  // Allocate an output channel if needed, save a reference to the channel
  if (out_chan == null) out_chan = new("FIFO MASTER OUTPUT CHANNEL", inst); 
  this.out_chan       = out_chan;

  // Create the default factory object
  randomized_obj = new();
    
endfunction: new


//-----------------------------------------------------------------------------
// main() - Monitor the FIFO bus, and invoke callbacks
//-----------------------------------------------------------------------------
    
task fifo_monitor::main();

  fifo_trans tr;
    
  // Fork super.main to perform any base-class actions
  fork
    super.main();
  join_none

  // Main Monitor Loop
  while(1) begin

    $cast(tr, randomized_obj.copy()); 

    // Pre-Rx Callback
    `vmm_callback(fifo_monitor_callbacks ,monitor_pre_rx(this, tr));

    // Sample the bus using the fifo_sample() task
    sample_fifo(tr);

    `vmm_callback(fifo_monitor_callbacks ,monitor_post_rx(this, tr));  

    // Printthe transaction in debug mode    
    `vmm_trace(log, tr.psdisplay("Monitor ==>"));

    // Put the trans into the output channel using sneak so it can't block
    out_chan.sneak(tr);
  end

endtask: main


//-----------------------------------------------------------------------------
// sample_fifo() - Monitor and Sample the FIFO bus when a valid transaction occurs
//-----------------------------------------------------------------------------

task fifo_monitor::sample_fifo(ref fifo_trans tr);
   int i;
   bit [1023:0] msg;
   time stamp;

   tr.rd_data_rate  =  0;
   tr.wr_data_rate =   0 ;

   _portrcv.receive(msg, stamp);
   tr.data = msg; 
endtask: sample_fifo
