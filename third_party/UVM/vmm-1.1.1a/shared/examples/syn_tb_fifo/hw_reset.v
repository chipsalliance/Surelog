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

`timescale 1 ns / 1 ns 
`include "vmm_hw_rtl.sv"

module hw_reset(output rst);

hw_reset1 bfm(rst);

endmodule



module hw_reset1(output rst);


//
// Clock control
//
wire uclk, urst, posedge_en;

vmm_hw_clock_control tb_ctl(uclk, urst, 1'b1, posedge_en, 1'b1, );


//
// Reset request messages
// The content of the message is ignored, only the fact that it is issued
// is enough to know that HW reset must be applied.
//
wire msg;
wire rst_req;
reg  rst_req_ack;

vmm_hw_in_if  #(1) reset_req_if(rst_req_ack, rst_req, msg, uclk, urst);

//
// Reset done feedback messages
// The content of the message is irrelevant, only the fact that it is issued
// is enough to know that HW reset has completed.
//
wire rst_done;
reg  rst_done_ack;

// Note: the input message is recirculated into the output to prevent the
//       ynthesis tool from leaving the 'msg' port unconnected if it was
//       not used -- and since the same module is also used in "bfm_write",
//       that caused its message port to be unconnected too.
vmm_hw_out_if  #(1) reset_ack_if(rst_done, rst_done_ack, msg, uclk, urst);

reg [1:0] state;
parameter WAIT   = 0;
parameter APPLY1 = 1;
parameter APPLY2 = 2;
parameter DONE   = 3;

assign rst = (state == APPLY1 || state == APPLY2);

assign rst_req_ack = state == WAIT && !urst;
assign rst_done    = state == DONE;


always @(posedge uclk)
begin
   if (urst) begin 
      state <= WAIT;
   end
   else begin
      case (state)
       WAIT: if (rst_req) begin 
          state <= APPLY1;
       end
       // Apply reset for 2 cycles
       APPLY1: begin
          if (posedge_en) begin
             state <= APPLY2;
          end
       end
       APPLY2: begin
          if (posedge_en) begin
             state <= DONE;
          end
       end
       DONE: begin
          if (rst_done_ack) begin
             state <= WAIT;
          end
       end
      endcase
   end
end

endmodule 
