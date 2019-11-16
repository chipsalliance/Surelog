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

module bfm_write(output reg push_req_n, pop_req_n,
                 output reg [15:0] data_in,
                 input [15:0] data_out,
                 input rst ); 

//
// Clock control
//
wire uclk, ureset, posedge_en, negedge_en; 
wire posedge_rdy = 1;
wire negedge_rdy = 1;

vmm_hw_clock_control clk1(uclk, urst,
                          posedge_rdy, posedge_en,
                          negedge_rdy, negedge_en);


// Interpret 33-bit messages as push/pop, data and data rate
// and apply to DUT

wire [32:0] drv_msg; 
reg         drv_rx_rdy;
wire        drv_tx_rdy;

vmm_hw_in_if #(33) msg1(drv_rx_rdy, drv_tx_rdy, drv_msg, uclk, urst);


reg [15:0] datarate, data; 
reg command; 

reg [1:0] drv_state;
parameter WAIT       = 0; 
parameter DATARATING = 1; 
parameter PUSHPOP    = 2; 

reg [7:0] counter; 

always @(posedge uclk)
begin
   if (urst || rst) begin
      drv_state  <= WAIT; 
      drv_rx_rdy <= 1;
      push_req_n <= 1; 
      pop_req_n  <= 1; 
   end
   else begin
      case (drv_state)
       WAIT: begin
          if (drv_tx_rdy) begin
             data_in      <= drv_msg[31:16];
             datarate     <= drv_msg[15:0]; 
             command      <= drv_msg[32];

             drv_rx_rdy   <= 0; 
             drv_state    <= DATARATING;
             
             // synopsys translate_off
             $write("Command is %s %h@%0d", (drv_msg[32]) ? "PSH" : "POP" ,
                    drv_msg[31:16], drv_msg[15:0]); 
             // synopsys translate_on
          end
       end
       DATARATING: begin
          if (posedge_en) begin
             if (datarate == 0) begin
                drv_state <= PUSHPOP;
                if (command) push_req_n <= 0;
                else         pop_req_n <= 0;
             end
             else datarate <= datarate - 1; 
          end
       end
       PUSHPOP: begin
          if (posedge_en) begin
             drv_rx_rdy <= 1;
             push_req_n <= 1; 
             pop_req_n  <= 1; 
	     drv_state  <= WAIT; 
          end
       end
      endcase
   end
end


// Send an observed POP operation back to the testbench as a 32-bit message

reg [31:0] mon_msg; 
reg mon_tx_rdy;
wire mon_rx_rdy;

vmm_hw_out_if #(32) msg2(mon_tx_rdy, mon_rx_rdy, mon_msg, uclk, urst);

reg mon_state;

parameter WAIT4POP = 0;
parameter XFER_MSG = 1;
   
   
always @(posedge uclk)
begin
   if (urst || rst) begin
      mon_tx_rdy <= 0;
      mon_state  <= WAIT4POP;
   end
   else begin
      case (mon_state)
       WAIT4POP: begin
          if (!pop_req_n && posedge_en) begin
             mon_msg    <= data_out;
             mon_tx_rdy <= 1;
             mon_state  <= XFER_MSG;  
             // synopsys translate_off
             $display("Sending Message %h from bfm ", data_out); 
             // synopsys translate_on
          end
       end
       XFER_MSG: begin
          if (mon_rx_rdy) begin
             mon_tx_rdy <= 0;
             mon_state  <= WAIT4POP;
          end
       end
      endcase
   end
end

endmodule
