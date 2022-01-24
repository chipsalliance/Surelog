module GOOD();
endmodule

module top();
  localparam signed [63:0] n = 32'h8000_0000;
  localparam signed [63:0] n2 = n + 1'b1;
  localparam signed [63:0] n3 = 64'h8FFF_FFFF_FFFF_0000;
  localparam signed [63:0] n4 = n3 + 64'h0000_0000_0000_FFFF;
  if (n4 == 10376293541461622783) begin
   GOOD good();
  end
endmodule

