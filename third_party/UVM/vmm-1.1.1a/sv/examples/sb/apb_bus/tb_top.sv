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


`include "soc_bus.sv"

module tb_top;
   bit clk = 0;

   apb_if m(clk);
   apb_if s0(clk);
   apb_if s1(clk);
   apb_if s2(clk);

   soc_bus dut_slv(.m  (m  ),
                   .s0 (s0 ),
                   .s1 (s1 ),
                   .s2 (s2 ),
                   .clk(clk));

   always #10 clk = ~clk;
endmodule: tb_top
