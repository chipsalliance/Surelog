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

`include "ovm_macros.svh"

package user_pkg;

`ifdef INCA
  `include "ovm.svh"
`else
  import ovm_pkg::*;
`endif

  typedef enum { BUS_READ, BUS_WRITE } bus_op_t;
  typedef enum { STATUS_OK, STATUS_NOT_OK } status_t;

  //--------------------------------------------------------------------
  // bus_trans
  //--------------------------------------------------------------------
  class bus_trans extends ovm_sequence_item;

    bit [11:0] addr;
    bit [7:0] data;
    bus_op_t op;

    function new();
      super.new();
    endfunction

    function ovm_object clone();
      bus_trans t; t = new();
      t.copy(this);
      return t;
    endfunction

    function void copy (bus_trans t);
      super.copy(t);
      addr = t.addr;
      data = t.data;
      op = t.op;
    endfunction

    function bit compare(bus_trans t);
      return ((op == t.op) && (addr == t.addr) && (data == t.data));
    endfunction

    function string convert2string();
      string s;
      $sformat(s, "op %s: addr=%03x, data=%02x", op.name(), addr, data);
      return s;
    endfunction

  endclass

  //--------------------------------------------------------------------
  // bus_req
  //--------------------------------------------------------------------
  class bus_req extends bus_trans;

    function ovm_object clone();
      bus_req t; t = new();
      t.copy(this);
      return t;
    endfunction

    function void copy (bus_req t);
      super.copy(t);
    endfunction

  endclass

  //--------------------------------------------------------------------
  // bus_rsp
  //--------------------------------------------------------------------
  class bus_rsp extends bus_trans;

    status_t status;

    function ovm_object clone();
      bus_rsp t; t = new();
      t.copy(this);
      return t;
    endfunction

    function void copy (bus_rsp t);
      super.copy(t);
      status = t.status;
    endfunction

    function void copy_req (bus_req t);
      super.copy(t);
    endfunction

    function string convert2string();
      string s;
      $sformat(s, "op %s, status=%s", super.convert2string(), status.name());
      return s;
    endfunction

  endclass

class my_driver #(type REQ = ovm_sequence_item, 
                  type RSP = ovm_sequence_item)  extends ovm_driver #(REQ, RSP);

  int data_array[511:0];

  function new(string name, ovm_component parent);
    super.new(name, parent);
  endfunction

  task run();

    REQ req;
    RSP rsp;

    forever begin
      seq_item_port.get(req);
      rsp = new();
      rsp.set_id_info(req);

      // Actually do the read or write here
      if (req.op == BUS_READ) begin
        rsp.addr = req.addr[8:0];
        rsp.data = data_array[rsp.addr];
        `ovm_info("my_driver",rsp.convert2string(),OVM_MEDIUM);
      end else begin
        data_array[req.addr[8:0]] = req.data;
        `ovm_info("my_driver",req.convert2string(),OVM_MEDIUM);
      end
      seq_item_port.put(rsp);
    end
  endtask
endclass


`define num_loops 10

class sequenceA #(type REQ = ovm_sequence_item,
                  type RSP = ovm_sequence_item) extends ovm_sequence #(REQ, RSP);

  static integer g_my_id = 1;
  integer my_id;
  
  function new(string name);
    super.new(name);
    my_id = g_my_id++;
  endfunction

  task body();
    string prstring;
    int  ret_data;
    REQ  req;
    RSP  rsp;

    `ovm_info("sequenceA", "Starting sequence", OVM_MEDIUM)
    
    `ovm_info("sequenceA", "  sequence %0d", my_id);
    
    for(int unsigned i = 0; i < `num_loops; i++) begin
      req = new();
      req.addr = (my_id * `num_loops) + i;
      req.data = my_id + i + 55;
      req.op   = BUS_WRITE;

      wait_for_grant();
      send_request(req);
      get_response(rsp);
      
      req = new();
      req.addr = (my_id * `num_loops) + i;
      req.data = 0;
      req.op   = BUS_READ;

      wait_for_grant();
      send_request(req);
      get_response(rsp);
      
      if (rsp.data != (my_id + i + 55)) begin
        $sformat(prstring, "Error, addr: %0d, expected data: %0d, actual data: %0d",
                 req.addr, req.data, rsp.data);
        `ovm_error("SequenceA", prstring)
      end
    end
    `ovm_info("sequenceA", "Finishing sequence", OVM_MEDIUM)
  endtask // body

endclass

`define NUM_SEQS 10

class env extends ovm_env;
  int i;
  ovm_sequencer #(bus_req, bus_rsp) sqr;

  sequenceA #(bus_req, bus_rsp) sequence_a[`NUM_SEQS];
  my_driver #(bus_req, bus_rsp) drv ;

  function new(string name, ovm_component parent);
    string str;

    super.new(name, parent);
    sqr = new("sequence_controller", this);

    for (i = 0; i < `NUM_SEQS; i++) begin
      sequence_a[i] = new("sequence");
    end
    
    // create and connect driver
    drv = new("slave", this);
    drv.seq_item_port.connect(sqr.seq_item_export);
  endfunction

task run();
    int i;

    for (i = 0; i < `NUM_SEQS; i++) begin
      fork
        sequence_a[i].start(sqr, null);
      join_none
      #0;
    end
    wait fork;
    report_summarize();
    global_stop_request();
endtask

endclass
endpackage

module top;
  import user_pkg::*;
`ifndef INCA
  import ovm_pkg::*;
`endif
  env e;

  initial begin
    `ovm_info("top","In top initial block",OVM_MEDIUM);
    e = new("env", null);
    e.run_test();
  end
endmodule

