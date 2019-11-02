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

//
// 1-master, 3-slave SoC Bus
//
module soc_bus(apb_if m,
               apb_if s0,
               apb_if s1,
               apb_if s2,
               input  clk);

// Feed-throughs
assign s0.paddr   = m.paddr[7:0];
assign s0.penable = m.penable;
assign s0.pwrite  = m.pwrite;
assign s0.pwdata  = m.pwdata;

assign s1.paddr   = m.paddr[7:0];
assign s1.penable = m.penable;
assign s1.pwrite  = m.pwrite;
assign s1.pwdata  = m.pwdata;

assign s2.paddr   = m.paddr[7:0];
assign s2.penable = m.penable;
assign s2.pwrite  = m.pwrite;
assign s2.pwdata  = m.pwdata;

// Address decoder
// paddr[31..10|9..8|7..0]
//       Ignore  s#  addr

assign s0.psel = (m.paddr[9:8] == 2'b00 && m.psel);
assign s1.psel = (m.paddr[9:8] == 2'b01 && m.psel);
assign s2.psel = (m.paddr[9:8] == 2'b10 && m.psel);

assign m.prdata = (s0.psel) ? s0.prdata :
                   ((s1.psel) ? s1.prdata :
                    ((s2.psel) ? s2.prdata : 'z));

endmodule: soc_bus
