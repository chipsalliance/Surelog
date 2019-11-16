// $Id: //dvt/vtech/dev/main/ovm-tests/examples/tlm/producer_consumer/fifo.sv#1 $
//----------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------


/* 
About: producer_consumer

this test is the basic simple to illustrates how to create a producer and consumer which are completely independent and connecting them using a tlm_fifo channel


Walk through the test:

two thrads *producer* and *consumer* will use ovm_blocking_put port and ovm_blocking_get port, to transfer an integer from the producer to the consumer through fifo exports at the connection function of an environment class


*/

`include "ovm_macros.svh"

//----------------------------------------------------------------------
// module top
//----------------------------------------------------------------------
module test;

`ifdef INCA
  `include "ovm.svh"
`else 
  import ovm_pkg::*;
`endif
  
  //----------------------------------------------------------------------
  // class producer
  //----------------------------------------------------------------------
  class producer extends ovm_component;

    ovm_blocking_put_port#(int) put_port;
    
    function new(string name, ovm_component p = null);
      super.new(name,p);
      put_port = new("put_port", this);
      
    endfunction
    
    task run;
      
      int randval;
      
      for(int i = 0; i < 10; i++)
        begin
          randval = $random % 100;
	  #10;
          `ovm_info("producer", $sformatf("sending   %4d", randval), OVM_MEDIUM)
          put_port.put(randval);
        end
    endtask
    
  endclass : producer
  
  //----------------------------------------------------------------------
  // class consumer
  //----------------------------------------------------------------------
  class consumer extends ovm_component;

    ovm_blocking_get_port#(int) get_port;
    
    function new(string name, ovm_component p = null);
      super.new(name,p);
      get_port = new("get_port", this);
    endfunction
    
    task run;
      
      int val;
      
      forever
        begin
          get_port.get(val);
          `ovm_info("consumer", $sformatf("receiving %4d", val), OVM_MEDIUM)
        end
      
    endtask
    
  endclass : consumer
  
  //----------------------------------------------------------------------
  // class env
  //----------------------------------------------------------------------
  class env extends ovm_env;
    producer p;
    consumer c;
    tlm_fifo #(int) f;
    
    function new(string name = "env");
      super.new(name);
      p = new("producer", this);
      c = new("consumer", this);
      f = new("fifo", this);
      $display("fifo put_export: %s", f.m_name);
    endfunction
    
    function void connect();
      p.put_port.connect(f.put_export);
      c.get_port.connect(f.get_export);
    endfunction
    
    task run();
      #1000 global_stop_request();
    endtask
    
  endclass
  
  // Main body of module top:
  env e;
  
  initial begin
    e = new();
    e.run_test();
    //$finish;
  end

endmodule // test

