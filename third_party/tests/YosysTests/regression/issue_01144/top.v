module top(input clk, d, output q);
specify
  // Fails:
  (posedge clk => (q +: d)) = (3,1);
  (/*posedge*/ clk => (q +: d)) = (3,1);
  (posedge clk *> (q +: d)) = (3,1);
  (/*posedge*/ clk *> (q +: d)) = (3,1);

  // Works:
  (/*posedge*/ clk => q) = (3,1);
  (/*posedge*/ clk *> q) = (3,1);
endspecify
endmodule
