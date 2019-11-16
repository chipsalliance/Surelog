// $Id: hierarchy.sv,v 1.6 2008/09/02 09:53:45 jlrose Exp $
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
About: ovm_exmples/mechanism/hierarchy
This test is supposed to test the hierarchical connection between ports of hierarchical threads using a tlm_fifo exports.


Walk through the test:
A thread *gen* will use an ovm_blocking_put_port to put a transaction.

A *conv* thread will use an ovm_blocking_put_port to put a transaction,an  ovm_blocking_get_port to get a transactions, and an ovm_analysis_ port to a writte a transaction through it.

Another thread *bfm* will use an  ovm_blocking_get_port to only get the transactions that has been sent by the other threads.

A *listener* will extends the ovm_subscriber, to implement the analysis port write function.

A *producer* component will use ovm_blocking_put_port and ovm_analysis_port and a tlm_fifo, to connect the *gen* and *conv* put, get and analysis ports through the fifo exports.

A *consumer* component will use ovm_blocking_put export and connect it directly to a fifo export, also will connect the *bfm*  get port to the fifo export

At *top* env, the *producer*, *consumer*, and the the *listener* will be connected

*/





// $Id: hierarchy.sv,v 1.6 2008/09/02 09:53:45 jlrose Exp $
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
package user_pkg;

import ovm_pkg::*;

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
// component gen
//----------------------------------------------------------------------
class gen extends ovm_component;

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
      ovm_report_info("gen", msg);
      put_port.put(t);
    end
  endtask

endclass


//----------------------------------------------------------------------
// component conv
//----------------------------------------------------------------------
class conv extends ovm_component;

  ovm_blocking_put_port #(transaction) put_port;
  ovm_blocking_get_port #(transaction) get_port;

  function new(string name, ovm_component parent);
    super.new(name, parent);
    put_port = new("put_port", this);
    get_port = new("get_port", this);
  endfunction

  task run;
    transaction t;

    forever begin
      get_port.get(t);
      put_port.put(t);
    end
  endtask

endclass

//----------------------------------------------------------------------
// component bfm
//----------------------------------------------------------------------
class bfm extends ovm_component;

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
      ovm_report_info("bfm", msg);
    end
  endtask

endclass

//----------------------------------------------------------------------
// component producer
//----------------------------------------------------------------------
// begin codeblock producer
class producer extends ovm_component;

  ovm_blocking_put_port #(transaction) put_port;

  gen g;
  conv c;
  tlm_fifo #(transaction) f;

  function new(string name, ovm_component parent);
    super.new(name, parent);
    put_port = new("put_port", this);
    g = new("gen", this);
    c = new("conv", this);
    f = new("fifo", this);
    g.put_port.connect(f.blocking_put_export);  // A
    c.get_port.connect(f.blocking_get_export);  // B
    c.put_port.connect(put_port); // C
  endfunction

endclass
// end codeblock producer

//----------------------------------------------------------------------
// component consumer
//----------------------------------------------------------------------
// begin codeblock consumer
class consumer extends ovm_component;

  ovm_blocking_put_export #(transaction) put_export;

  bfm b;
  tlm_fifo #(transaction) f;

  function new(string name, ovm_component parent);
    super.new(name, parent);
    put_export = new("put_export", this);
    f = new("fifo", this);
    b = new("bfm", this);
    put_export.connect(f.blocking_put_export); // E
    b.get_port.connect(f.blocking_get_export); // F
  endfunction

endclass
// end codeblock consumer

//----------------------------------------------------------------------
// component top
//----------------------------------------------------------------------
// begin codeblock top
class top extends ovm_component;

  producer p;
  consumer c;

  function new(string name, ovm_component parent);
    super.new(name, parent);
    p = new("producer", this);
    c = new("consumer", this);
    p.put_port.connect(c.put_export);  // D
  endfunction

endclass
// end codeblock top


//----------------------------------------------------------------------
// environment env
//----------------------------------------------------------------------
// begin codeblock env
class env extends ovm_env;
  top t;

  function new(string name = "env");
    super.new(name);
    t = new("top", this);
  endfunction

  task run;
    #1000;
	global_stop_request();
  endtask

endclass
// end codeblock env

endpackage

//----------------------------------------------------------------------
// module top
//----------------------------------------------------------------------
// begin codeblock topmod
module top;

  import user_pkg::*;
  env e;

  initial begin
    e = new("e");
    e.run_test();
  end

endmodule
// end codeblock topmod
