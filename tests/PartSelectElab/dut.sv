module test(output reg state, input clk);
reg [15:0] data;

always @(posedge clk) begin
  data[7:0] <= data[7:0] + 2;
end

endmodule // test

