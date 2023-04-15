
module top(input [1:0] inp);
  bus_conn  u1 [1:0] (.datain(inp));
endmodule

module bus_conn (
input datain = 1'b1);
endmodule
