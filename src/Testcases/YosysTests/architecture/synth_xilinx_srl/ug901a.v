// https://www.xilinx.com/support/documentation/sw_manuals/xilinx2018_3/ug901-vivado-synthesis.pdf

// 8-bit Shift Register
// Rising edge clock
// Active high clock enable
// Concatenation-based template
// File: shift_registers_0.v
(* top *)
module shift_registers_0 (clk, clken, SI, SO);
parameter WIDTH = 32;
input clk, clken, SI;
output SO;
reg [WIDTH-1:0] shreg;
always @(posedge clk)
begin
	if (clken)
		shreg <= {shreg[WIDTH-2:0], SI};
end
assign SO = shreg[WIDTH-1];
endmodule

`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd shift_registers_0; select t:SRLC32E -assert-count 1; select t:BUFG t:SRLC32E %% %n t:* %i -assert-none";
endmodule
`endif
