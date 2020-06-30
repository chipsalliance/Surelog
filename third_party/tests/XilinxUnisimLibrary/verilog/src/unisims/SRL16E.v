///////////////////////////////////////////////////////////////////////////////
//    Copyright (c) 1995/2016 Xilinx, Inc.
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
///////////////////////////////////////////////////////////////////////////////
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor      : Xilinx
// \   \   \/     Version     : 2017.1
//  \   \         Description : Xilinx Unified Simulation Library Component
//  /   /                  16-Bit Shift Register Look-Up-Table with Clock Enable
// /___/   /\     Filename    : SRL16E.v
// \   \  /  \
//  \___\/\___\
//
///////////////////////////////////////////////////////////////////////////////
// Revision
//    03/23/04 - Initial version.
//    03/11/05 - Add LOC paramter;
//    05/07/08 - 468872 - Add negative setup/hold support
//    12/13/11 - 524859 - Added `celldefine and `endcelldefine
//    04/16/13 - 683925 - add invertible pin support.
// End Revision
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps/1 ps

`celldefine

module SRL16E #(
  `ifdef XIL_TIMING
  parameter LOC = "UNPLACED",
  `endif
  parameter [15:0] INIT = 16'h0000,
  parameter [0:0] IS_CLK_INVERTED = 1'b0
)(
  output Q,
  
  input A0,
  input A1,
  input A2,
  input A3,
  input CE,
  input CLK,
  input D
);

`ifdef XIL_TIMING
  wire CE_dly;
  wire CLK_dly;
  wire D_dly;
`endif

  reg  [15:0] data = INIT;
  reg first_time = 1'b1;

  initial
  begin
    assign  data = INIT;
    first_time <= #100000 1'b0;
`ifdef XIL_TIMING
    while ((((CLK_dly !== 1'b0) && (IS_CLK_INVERTED == 1'b0)) ||
            ((CLK_dly !== 1'b1) && (IS_CLK_INVERTED == 1'b1))) &&
           (first_time == 1'b1)) #1000;
`else
    while ((((CLK !== 1'b0) && (IS_CLK_INVERTED == 1'b0)) ||
            ((CLK !== 1'b1) && (IS_CLK_INVERTED == 1'b1))) &&
           (first_time == 1'b1)) #1000;
`endif
    deassign data;
  end

`ifdef XIL_TIMING
generate
if (IS_CLK_INVERTED == 1'b0) begin : generate_block1
  always @(posedge CLK_dly) begin
    if (CE_dly == 1'b1 || CE_dly === 1'bz) begin // rv 1
      data[15:0] <= {data[14:0], D_dly};
    end
  end
end else begin : generate_block1
  always @(negedge CLK_dly) begin
    if (CE_dly == 1'b1 || CE_dly === 1'bz) begin //rv 1
      data[15:0] <= {data[14:0], D_dly};
    end
  end
end
endgenerate
`else
generate
if (IS_CLK_INVERTED == 1'b0) begin : generate_block1
  always @(posedge CLK) begin
    if (CE == 1'b1 || CE === 1'bz) begin //rv 1
      data[15:0] <= {data[14:0], D};
    end
  end
end else begin : generate_block1
  always @(negedge CLK) begin
    if (CE == 1'b1 || CE === 1'bz) begin //rv 1
      data[15:0] <= {data[14:0], D};
    end
  end
end
endgenerate
`endif

  assign Q = data[{A3, A2, A1, A0}];

`ifdef XIL_TIMING

  reg notifier;

  wire sh_clk_en_p;
  wire sh_clk_en_n;
  wire sh_ce_clk_en_p;
  wire sh_ce_clk_en_n;

  always @(notifier) 
    data[0] = 1'bx;

  assign sh_clk_en_p = ~IS_CLK_INVERTED;
  assign sh_clk_en_n = IS_CLK_INVERTED;
  assign sh_ce_clk_en_p = CE && ~IS_CLK_INVERTED;
  assign sh_ce_clk_en_n = CE && IS_CLK_INVERTED;
`endif

  specify
    (A0 => Q) = (0:0:0, 0:0:0);
    (A1 => Q) = (0:0:0, 0:0:0);
    (A2 => Q) = (0:0:0, 0:0:0);
    (A3 => Q) = (0:0:0, 0:0:0);
    (CLK => Q) = (100:100:100, 100:100:100);
`ifdef XIL_TIMING
    $period (negedge CLK, 0:0:0, notifier);
    $period (posedge CLK, 0:0:0, notifier);
    $setuphold (negedge CLK, negedge CE, 0:0:0, 0:0:0, notifier,sh_clk_en_n,sh_clk_en_n,CLK_dly,CE_dly);
    $setuphold (negedge CLK, negedge D, 0:0:0, 0:0:0, notifier,sh_ce_clk_en_n,sh_ce_clk_en_n,CLK_dly,D_dly);
    $setuphold (negedge CLK, posedge CE, 0:0:0, 0:0:0, notifier,sh_clk_en_n,sh_clk_en_n,CLK_dly,CE_dly);
    $setuphold (negedge CLK, posedge D, 0:0:0, 0:0:0, notifier,sh_ce_clk_en_n,sh_ce_clk_en_n,CLK_dly,D_dly);
    $setuphold (posedge CLK, negedge CE, 0:0:0, 0:0:0, notifier,sh_clk_en_p,sh_clk_en_p,CLK_dly,CE_dly);
    $setuphold (posedge CLK, negedge D, 0:0:0, 0:0:0, notifier,sh_ce_clk_en_p,sh_ce_clk_en_p,CLK_dly,D_dly);
    $setuphold (posedge CLK, posedge CE, 0:0:0, 0:0:0, notifier,sh_clk_en_p,sh_clk_en_p,CLK_dly,CE_dly);
    $setuphold (posedge CLK, posedge D, 0:0:0, 0:0:0, notifier,sh_ce_clk_en_p,sh_ce_clk_en_p,CLK_dly,D_dly);
    $width (negedge CLK, 0:0:0, 0, notifier);
    $width (posedge CLK, 0:0:0, 0, notifier);
`endif
    specparam PATHPULSE$ = 0;
  endspecify

endmodule

`endcelldefine
