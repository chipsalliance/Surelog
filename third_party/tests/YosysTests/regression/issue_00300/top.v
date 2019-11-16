module top(input clk, input [7:0] addr, wdata, output [7:0] rdata);
reg [7:0] memory [255:0];
assign rdata = memory[addr];
always @(posedge clk) memory[addr] <= wdata;
endmodule
