
// $Id: interface.sv,v 1.7 2008/09/02 09:53:45 jlrose Exp $
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
About: ovm_exmples/mechanism/interfaces

This example will illustrate how to create a pin interface and mod port interfaces for a simple dut.

Connect a component "driver" to the pin interfaces, then to the dut.
*/



//----------------------------------------------------------------------
// interface mem_pins_if
//----------------------------------------------------------------------
interface pin_if (input clk);
  bit [15:0] address;
  bit [7:0]  wr_data;
  bit [7:0] rd_data;
  bit rst;
  bit rw;
  bit req;
  bit ack;
  bit err;

  modport master_mp(             
   input  clk,
   input  rst,          
   output address,
   output wr_data,  
   input  rd_data,            
   output req,
   output rw,           
   input  ack,
   input  err );         
                                 
  modport slave_mp(              
   input  clk,
   input  rst,          
   input  address,
   input  wr_data,  
   output rd_data,            
   input  req,
   input  rw,           
   output ack,
   output err );         
                                 
  modport monitor_mp(            
   input  clk,
   input  rst,          
   input  address,
   input  wr_data,  
   input  rd_data,            
   input  req,
   input  rw ,
   input  ack,
   input  err );
endinterface

import ovm_pkg::*;

package user_pkg;
import ovm_pkg::*;  
//----------------------------------------------------------------------
// component driver
//----------------------------------------------------------------------
class driver extends ovm_component;

  virtual pin_if pif;

  function new(string name, ovm_component parent = null);
    super.new(name, parent);
  endfunction

  task run;
    forever begin
      @(posedge pif.clk);
      ovm_report_info("driver", "posedge clk");
      //...
    end
  endtask

endclass

//----------------------------------------------------------------------
// environment env
//----------------------------------------------------------------------
class env extends ovm_env;

  local virtual pin_if pif;
  driver d;

  function new(string name, virtual pin_if _p);
    super.new(name);
    pif = _p;
    d = new("driver", this);
    d.pif = pif;
  endfunction

  task run();
    #100 global_stop_request();
  endtask

endclass

endpackage
import user_pkg::*;

//----------------------------------------------------------------------
// module dut
//----------------------------------------------------------------------
module dut(pin_if pif);

  always @(posedge pif.clk) begin
    ovm_report_info("dut", "posedge clk");
    //...
  end
endmodule

//----------------------------------------------------------------------
// module clkgen
//----------------------------------------------------------------------
module clkgen(output bit clk);

  initial begin
    forever begin
      #5 clk = 1;
      #5 clk = 0;
    end
  end

endmodule

//----------------------------------------------------------------------
// module top
//----------------------------------------------------------------------
module top;
  bit clk;
  clkgen ck(clk);
  pin_if pif(clk);

  env e;
  dut d(pif.slave_mp);

  initial begin
    e = new("env", pif);
    e.run_test();
    //$finish;
  end
  
endmodule
