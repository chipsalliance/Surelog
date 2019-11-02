module top(input clk, a, b);
  always @(posedge clk)
    if (a) begin :scope
      reg b_inv = ~b;
    end
endmodule
