///////////////////////////////////////////////////////
//     Copyright (c) 1995/2006 Xilinx Inc.
// 
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
///////////////////////////////////////////////////////
//
//   ____   ___
//  /   /\/   / 
// /___/  \  /     Vendor      : Xilinx 
// \  \    \/      Version     : 13.i (O.51)
//  \  \           Description : 
//  /  /                      
// /__/   /\       Filename    : ICAPE2.v
// \  \  /  \ 
//  \__\/\__ \                    
//                                 
//  Revision:		
//  04/30/10 - Initial version.
//  09/03/10 - Change to bus timing.
//  02/18/11 - Change DEVICE_ID default (CR593951)
//  02/10/14 - Fixed GSR deassertion (CR 772626).
//  End Revision
///////////////////////////////////////////////////////

`timescale 1 ps / 1 ps 

`celldefine

module ICAPE2 (
  O,
  CLK,
  CSIB,
  I,
  RDWRB
);
  parameter [31:0] DEVICE_ID = 32'h03651093;
  parameter ICAP_WIDTH = "X32";
  parameter SIM_CFG_FILE_NAME = "NONE";

  `ifdef XIL_TIMING

  parameter LOC = "UNPLACED";

  `endif //

  output [31:0] O;

  input CLK;
  input CSIB;
  input RDWRB;
  input [31:0] I;

  wire cso_b;
  reg  prog_b;
  reg  init_b;
  reg [3:0] bw = 4'b0000;
  wire busy_out;
  reg cs_bi = 0, rdwr_bi = 0;
  wire cs_b_t;
  wire clk_in;
  wire rdwr_b_t;
  wire [31:0] dix;
  reg [31:0] di;
  reg [31:0] data_rbt;
  reg [7:0] tmp_byte0;
  reg [7:0] tmp_byte1;
  reg [7:0] tmp_byte2;
  reg [7:0] tmp_byte3;
  reg icap_idone = 0;
  reg clk_osc = 0;
  reg sim_file_flag;
  integer icap_fd;
  reg notifier;
  wire delay_CLK;
  wire delay_CSIB;
  wire delay_RDWRB;
  wire [31:0] delay_I;
  tri1 p_up; 
  tri init_tri = (icap_idone == 0) ? init_b : p_up;
  tri (weak1, strong0) done_o = p_up;
  tri (pull1, supply0) [31:0] di_t = (icap_idone == 1 && delay_RDWRB == 1)? 32'bz : dix;
 
  `ifndef XIL_TIMING
   assign delay_I = I;
   assign delay_RDWRB = RDWRB;
   assign delay_CLK = CLK;
   assign delay_CSIB = CSIB;
  `endif

  assign dix = (icap_idone == 1) ? delay_I : di;
  assign cs_b_t = (icap_idone == 1) ? delay_CSIB : cs_bi;
  assign clk_in = (icap_idone == 1) ? delay_CLK : clk_osc;
  assign rdwr_b_t = (icap_idone == 1) ? delay_RDWRB : rdwr_bi;
  assign O = (icap_idone == 1 && delay_RDWRB == 1) ? di_t : 32'b0;

  always 
//    if (icap_idone == 0) 
       #1000 clk_osc <= ~clk_osc;
  
  always @(delay_CSIB or delay_RDWRB)
    if ($time > 1 && icap_idone == 0) begin
          $display (" Warning : ICAPE2 on instance %m at time %t has not finished initialization. A message will be printed after the initialization. User need start read/write operation after that.", $time);
    end


  SIM_CONFIGE2 #(
      .DEVICE_ID(DEVICE_ID),
      .ICAP_SUPPORT("TRUE"),
      .ICAP_WIDTH(ICAP_WIDTH)
    )
    SIM_CONFIGE2_INST (
      .CSOB(cso_b),
      .DONE(done_o),
      .CCLK(clk_in),
      .CSB(cs_b_t),
      .D(di_t),
      .INITB(init_tri),
      .M(3'b110),
      .PROGB(prog_b),
      .RDWRB(rdwr_b_t)
  );


  initial begin

    case (ICAP_WIDTH)
      "X8" : bw = 4'b0000;
      "X16" : bw = 4'b0010;
      "X32" : bw = 4'b0011;
      default : begin
        $display("Attribute Syntax Error : The Attribute ICAP_WIDTH on ICAPE2 instance %m is set to %s.  Legal values for this attribute are X8, X16 or X32.", ICAP_WIDTH);
      end
    endcase
 
    icap_idone = 0;
    sim_file_flag = 0;
    if (SIM_CFG_FILE_NAME == "NONE") begin
       sim_file_flag = 1;
    end
    else begin
      icap_fd = $fopen(SIM_CFG_FILE_NAME, "r");
      if  (icap_fd == 0)
      begin
         $display(" Error: The configure rbt data file %s for ICAPE2 instance %m was not found. Use the SIM_CFG_FILE_NAME parameter to pass the file name.\n", SIM_CFG_FILE_NAME);
         sim_file_flag = 1;
      end
    end

      init_b = 1;
      prog_b = 1;
      rdwr_bi = 0;
      cs_bi = 1;
      #600000;
      @(posedge clk_in)
       prog_b = 0;
      @(negedge clk_in)
       init_b = 0;
     #600000;
      @(posedge clk_in)
       prog_b = 1;
      @(negedge clk_in) begin
       init_b = 1;
       cs_bi = 0;
      end
      if (sim_file_flag == 0) begin
        while ($fscanf(icap_fd, "%b", data_rbt) != -1) begin
         if (done_o == 0) begin
          tmp_byte3 = bit_revers8(data_rbt[31:24]);
          tmp_byte2 = bit_revers8(data_rbt[23:16]);
          tmp_byte1 = bit_revers8(data_rbt[15:8]);
          tmp_byte0 = bit_revers8(data_rbt[7:0]);
          if (bw == 4'b0000) begin
            @(negedge clk_in)
               di = {24'b0, tmp_byte3};
            @(negedge clk_in)
               di = {24'b0, tmp_byte2};
            @(negedge clk_in)
               di = {24'b0, tmp_byte1};
            @(negedge clk_in)
               di = {24'b0, tmp_byte0};
           end
           else if (bw == 4'b0010) begin
            @(negedge clk_in)
               di = {16'b0, tmp_byte3, tmp_byte2};
            @(negedge clk_in)
               di = {16'b0, tmp_byte1, tmp_byte0};
           end
           else if (bw == 4'b0011) begin
            @(negedge clk_in)
               di = {tmp_byte3, tmp_byte2, tmp_byte1, tmp_byte0};
           end
        end
        else begin
          @(negedge clk_in);
          di = 32'hFFFFFFFF;
          @(negedge clk_in);
          @(negedge clk_in);
          @(negedge clk_in);
          if (icap_idone == 0) begin 
            $display (" Message: ICAPE2 on instance %m at time %t has finished initialization. User can start read/write operation.", $time);
            icap_idone = 1;
          end
        end
      end
      $fclose(icap_fd);
      #1000;
    end
    else begin
       @(negedge clk_in)
          di = 32'hFFFFFFFF;
       @(negedge clk_in)
          di = 32'hFFFFFFFF;
       @(negedge clk_in)
          di = 32'hFFFFFFFF;
       @(negedge clk_in)
          di = 32'hFFFFFFFF;
       @(negedge clk_in)
          di = 32'hFFFFFFFF;
       @(negedge clk_in)
          di = 32'hFFFFFFFF;
       @(negedge clk_in)
          di = 32'hFFFFFFFF;
       @(negedge clk_in)
          di = 32'hFFFFFFFF;
       @(negedge clk_in)
          di = 32'hFFFFFFFF;
       @(negedge clk_in)
          di = 32'h000000DD;
       @(negedge clk_in) begin
        if (bw == 4'b0000)
           di = 32'h00000088;
        else if (bw == 4'b0010)
           di = 32'h00000044;
        else if (bw == 4'b0011)
           di = 32'h00000022;
       end
      rbt_data_wr(32'hFFFFFFFF);
      rbt_data_wr(32'hFFFFFFFF);
      rbt_data_wr(32'hAA995566);
      rbt_data_wr(32'h30008001);
      rbt_data_wr(32'h00000005);
       @(negedge clk_in);
       @(negedge clk_in);
       @(negedge clk_in);
       @(negedge clk_in);
       @(negedge clk_in);
       @(negedge clk_in);
       @(negedge clk_in);
       @(negedge clk_in);
       @(negedge clk_in);
       if (icap_idone == 0) begin 
            $display (" Message: ICAPE2 on instance %m at time %t has finished initialization. User can start read/write operation.", $time);
          icap_idone = 1;
       end
      #1000;
      end
  end
  

  task rbt_data_wr;
    input [31:0] dat_rbt;
    reg [7:0] tp_byte3;
    reg [7:0] tp_byte2;
    reg [7:0] tp_byte1;
    reg [7:0] tp_byte0;
  begin
    tp_byte3 = bit_revers8(dat_rbt[31:24]);
    tp_byte2 = bit_revers8(dat_rbt[23:16]);
    tp_byte1 = bit_revers8(dat_rbt[15:8]);
    tp_byte0 = bit_revers8(dat_rbt[7:0]);
    if (bw == 4'b0000) begin
      @(negedge clk_in)
         di = {24'b0, tp_byte3};
      @(negedge clk_in)
         di = {24'b0, tp_byte2};
      @(negedge clk_in)
         di = {24'b0, tp_byte1};
      @(negedge clk_in)
         di = {24'b0, tp_byte0};
     end
     else if (bw == 4'b0010) begin
      @(negedge clk_in)
         di = {16'b0, tp_byte3, tp_byte2};
      @(negedge clk_in)
         di = {16'b0, tp_byte1, tp_byte0};
     end
     else if (bw == 4'b0011) begin
      @(negedge clk_in)
         di = {tp_byte3, tp_byte2, tp_byte1, tp_byte0};
     end
   end
   endtask

  function [7:0] bit_revers8;
        input [7:0] din8;
        begin
            bit_revers8[0] = din8[7];
            bit_revers8[1] = din8[6];
            bit_revers8[2] = din8[5];
            bit_revers8[3] = din8[4];
            bit_revers8[4] = din8[3];
            bit_revers8[5] = din8[2];
            bit_revers8[6] = din8[1];
            bit_revers8[7] = din8[0];
        end
  endfunction

specify
    ( CLK => O) = (100:100:100, 100:100:100);

  `ifdef XIL_TIMING

    $period (posedge CLK, 0:0:0, notifier);
    $setuphold (posedge CLK, negedge CSIB, 0:0:0, 0:0:0, notifier,,, delay_CLK, delay_CSIB);
    $setuphold (posedge CLK, posedge CSIB, 0:0:0, 0:0:0, notifier,,, delay_CLK, delay_CSIB);
    $setuphold (posedge CLK, negedge I, 0:0:0, 0:0:0, notifier,,, delay_CLK, delay_I);
    $setuphold (posedge CLK, posedge I, 0:0:0, 0:0:0, notifier,,, delay_CLK, delay_I);
    $setuphold (posedge CLK, negedge RDWRB, 0:0:0, 0:0:0, notifier,,, delay_CLK, delay_RDWRB);
    $setuphold (posedge CLK, posedge RDWRB, 0:0:0, 0:0:0, notifier,,, delay_CLK, delay_RDWRB);

  `endif //

    specparam PATHPULSE$ = 0;
endspecify

endmodule

`endcelldefine
