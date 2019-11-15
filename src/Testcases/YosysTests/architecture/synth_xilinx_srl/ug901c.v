// https://www.xilinx.com/support/documentation/sw_manuals/xilinx2018_3/ug901-vivado-synthesis.pdf

// 32-bit dynamic shift register.
// Download:
// File: dynamic_shift_registers_1.v
(* top *)
module dynamic_shift_register_1 (CLK, CE, SEL, SI, DO);
parameter SELWIDTH = 5;
input CLK, CE, SI;
input [SELWIDTH-1:0] SEL;
output DO;
localparam DATAWIDTH = 2**SELWIDTH;
reg [DATAWIDTH-1:0] data;
assign DO = data[SEL];
always @(posedge CLK)
 begin
 if (CE == 1'b1)
 data <= {data[DATAWIDTH-2:0], SI};
 end
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd dynamic_shift_register_1; select t:SRLC32E -assert-count 1; select t:BUFG t:SRLC32E %% %n t:* %i -assert-none";
endmodule
`endif
