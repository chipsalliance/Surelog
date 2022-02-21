module GOOD();
endmodule

module top ();

  parameter [2:1] a = 10;
  parameter  high = $high(a);
  parameter  low = $low(a);
  parameter  left = $left(a);
  parameter  right = $right(a);

  assign ccc = $high(a);

  if (high == 2) begin
    GOOD good1();
  end
  if (low == 1) begin
    GOOD good2();
  end
  if (left == 2) begin
    GOOD good3();
  end
  if (right == 1) begin
    GOOD good4();
  end
endmodule
