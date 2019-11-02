`define TEST_1
module top (
   input [1:0] adr,
   input clk,
   input [1:0] din,
   output reg [1:0] q
);
   reg [1:0] ram [3:0];
   always@(posedge clk)
   begin
`ifdef TEST_1
     {ram[adr],q} <= {din, ram[adr]};
`elsif TEST_2
      ram[adr] <= din;
      q <= ram[adr];
`endif
   end
endmodule
