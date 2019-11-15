/******************************************************************************
 * (C) Copyright 2015 AMIQ Consulting
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * NAME:        an_interface.sv
 * PROJECT:     svaunit
 * Description: Example of one interface with a single SVA
 *******************************************************************************/

`ifndef AN_INTERFACE_SV
`define AN_INTERFACE_SV

`include  "another_interface.sv"
`include  "amiq_apb_if.sv"

// Example of one interface with a single SVA
interface an_interface (input clk);
   import uvm_pkg::*;
`include "uvm_macros.svh"

   another_interface a_if(.clk(clock));

   initial begin
   // Register a reference to APB virtual interface to config_db
      uvm_config_db#(virtual another_interface)::set(uvm_root::get(), "*","a_if", a_if);

      // Interface initialization
      a_if.sel    <=    '0;
      a_if.enable <=  1'b0;

      a_if.ready  <=  1'b0;
      a_if.slverr <=  1'b0;
   end


   //Select signal
   logic sel;

   //Enable signal
   logic enable;

   //Ready signal
   logic ready;

   //Error signal
   logic slverr;

   //Property definition for valid slverr value when one of sel, enable, ready signal is de-asserted
   property an_sva_property;
      @(posedge clk)
         !sel || !enable || !ready |-> !slverr;
   endproperty
   //Check that slverr is LOW when one of sel, enable or ready is LOW
   AN_SVA: assert property (an_sva_property) else
      `uvm_error("AN_SVA", "slverr must be LOW when one of sel, enable or ready is LOW.")

endinterface

`endif
