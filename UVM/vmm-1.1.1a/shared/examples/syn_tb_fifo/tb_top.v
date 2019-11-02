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

`include "vmm_hw_rtl.sv"

`include "hw_reset.v"
`include "bfm.v"
`include "dut.v"

module tb_top;

wire [15:0] data_in,data_out; 
wire pop_req_n;
wire push_req_n;

wire cclk, crst, crstn;
wire rst;

bfm_write bfm_write(push_req_n,pop_req_n,data_in,data_out,rst); 

vmm_hw_clock tb_clk(cclk, crst, crstn);

hw_reset hw_rst(rst);

`ifdef VMM_HW_INCL_DUT
dut dut(.clk(cclk),
        .rst(rst),
        .push_req_n(push_req_n),
        .data_in(data_in),
        .pop_req_n(pop_req_n),
        .data_out(data_out));
`endif
endmodule
