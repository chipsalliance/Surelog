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


`ifndef __ALU_IF__
`define __ALU_IF__

  interface alu_if (input bit clk);
    logic  [6:0]  y ;
    logic  [3:0]  a ;
    logic  [3:0]  b ;
    logic  [2:0]  sel ;
    logic  rst_n ;
    logic  en ;

    clocking cb @(posedge clk);
      input y;
      output a;
      output b;
      output sel;
      output en;
    endclocking

    clocking mon_cb @(posedge clk);
      input y;
      input a;
      input b;
      input sel;
      input en;
    endclocking

    //modport dutprt(output y, input a, input b, input sel, input rst_n, input en);
    modport drvprt(clocking cb, output rst_n);
    modport monprt(clocking mon_cb);

  endinterface

`endif // __ALU_IF__
