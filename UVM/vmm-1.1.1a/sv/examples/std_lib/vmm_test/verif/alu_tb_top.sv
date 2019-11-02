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


`include "alu_if.sv"

module alu_tb_top;
  parameter simulation_cycle = 100 ;
  
  reg  SystemClock ;
  wire  [6:0]  y ;
  wire  [3:0]  a ;
  wire  [3:0]  b ;
  wire  [2:0]  sel ;
  wire  clk ;
  wire  en ;
  assign  clk = SystemClock ;

  alu_if aluif(clk);
  alu_test tb (aluif.drvprt, aluif.monprt);

  alu dut(
    .y ( aluif.y ),
    .a ( aluif.a ),
    .b ( aluif.b ),
    .sel ( aluif.sel ),
    .clk ( clk ),
    .rst_n ( aluif.rst_n ),
    .en ( aluif.en )
  );

  initial begin
//    $vcdpluson;
    SystemClock = 0 ;
    forever begin
      #(simulation_cycle/2) 
        SystemClock = ~SystemClock ;
    end
  end
  
endmodule  
