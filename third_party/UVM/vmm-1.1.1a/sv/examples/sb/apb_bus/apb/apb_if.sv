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


`ifndef APB_IF__SV
`define APB_IF__SV

interface apb_if(input bit pclk);
   wire [31:0] paddr;
   wire        psel;
   wire        penable;
   wire        pwrite;
   wire [31:0] prdata;
   wire [31:0] pwdata;

   clocking mck @(posedge pclk);
      output paddr, psel, penable, pwrite, pwdata;
      input  prdata;

      sequence at_posedge;
         1;
      endsequence

   endclocking: mck

   clocking sck @(posedge pclk);
      input  paddr, psel, penable, pwrite, pwdata;
      output prdata;

      sequence at_posedge_sck;
         1;
      endsequence

   endclocking: sck

   clocking pck @(posedge pclk);
      input paddr, psel, penable, pwrite, prdata, pwdata;
   endclocking: pck

   modport master(clocking mck);
   modport slave(clocking sck);
   modport passive(clocking pck);

endinterface: apb_if

`endif
