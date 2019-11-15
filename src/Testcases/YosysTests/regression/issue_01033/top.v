module dram(input [3:0] i, output [4:0] o);
`ifdef UNPACKED
reg val [0:0];
`else
reg [0:0] val;
`endif
initial val[0] = 1'h1;
assign o = i + val[0];
endmodule
