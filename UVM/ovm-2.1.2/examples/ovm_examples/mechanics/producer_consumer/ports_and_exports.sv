// $Id: ports_and_exports.sv,v 1.6 2008/09/02 09:53:45 jlrose Exp $
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
About: ovm_exmples/mechanism/producer_consumer

This test is a basic and simple illustration of how to create a producer and consumer which are completely independent and connecting them using a tlm_fifo channel


Walk through the test:

Two threads *producer* and *consumer* will use ovm_blocking_put port and ovm_blocking_get port, to transefer some transactions from the producer to the consumer through fifo exports at a top component class, without using a connection function.


*/



//----------------------------------------------------------------------
// module top
//----------------------------------------------------------------------
module top;

`ifdef INCA
  `include "ovm.svh"
`else
  import ovm_pkg::*;
`endif

  //----------------------------------------------------------------------
  // class transaction
  //----------------------------------------------------------------------
  class transaction extends ovm_transaction;
  
    rand int data;
    rand int addr;
  
    function void copy( input transaction t );
      data = t.data;
      addr = t.addr;
    endfunction
  
    function bit comp( input transaction a , input transaction b );
      return ((a.data == b.data) && (a.addr == b.addr));
    endfunction
  
    function ovm_object clone();
      transaction t; t = new();
      t.copy(this);
      return t;
    endfunction
  
    function string convert2string();
      string s;
      $sformat(s, "[ addr = %x, data = %x ]", addr, data);
      return s;
    endfunction
  
  endclass
  
  //----------------------------------------------------------------------
  // component producer
  //----------------------------------------------------------------------
  class producer extends ovm_component;
  
    ovm_blocking_put_port #(transaction) put_port;
  
    function new(string name, ovm_component parent);
      super.new(name, parent);
      put_port = new("put_port", this);
    endfunction
  
  
    task run;
      transaction t;
      string msg;
  
      for(int i=0; i < 20; i++) begin
        t = new();
        assert(t.randomize());
        $sformat(msg, "sending  : %s", t.convert2string());
        ovm_report_info("producer", msg);
        put_port.put(t);
      end
    endtask
  
  endclass
  
  //----------------------------------------------------------------------
  // component consumer
  //----------------------------------------------------------------------
  class consumer extends ovm_component;
  
    ovm_blocking_get_port #(transaction) get_port;
  
    function new(string name, ovm_component parent);
      super.new(name, parent);
      get_port = new("get_port", this);
  
    endfunction
  
    task run;
      transaction t;
      string msg;
  
      forever begin
        get_port.get(t);
        $sformat(msg, "receiving: %s", t.convert2string());
        ovm_report_info("consumer", msg);
      end
    endtask
  
  endclass
  
  //----------------------------------------------------------------------
  // component top
  //----------------------------------------------------------------------
  class top extends ovm_component;
  
    producer p;
    consumer c;
    tlm_fifo #(transaction) f;
  
    function new(string name, ovm_component parent);
      super.new(name, parent);
      p = new("producer", this);
      c = new("consumer", this);
      f = new("fifo", this);
  
      p.put_port.connect(f.blocking_put_export);
      c.get_port.connect(f.blocking_get_export);
    endfunction
  
  endclass
  
  //----------------------------------------------------------------------
  // environment env
  //----------------------------------------------------------------------
  class env extends ovm_env;
    top t;
  
    function new();
      t = new("top", this);
    endfunction
  
    task run;
      #1000 global_stop_request();
    endtask
  
  endclass

  env e;

  initial begin
    e = new();
    e.run_test();
  end

endmodule
