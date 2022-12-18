module GOOD();
endmodule

module top();
  parameter logic [2:0] P1 = 3'b111;
  parameter logic [2:0] P2 = 3'b110;
  if ( 3'b111 == '1) begin 
    GOOD good1();
  end

  if ( P1 == '1) begin 
    GOOD good2();
  end

  if ( 3'b101 == '1) begin 
    BAD bad();
  end

  if ( P2 == '1) begin 
    BAD bad();
  end

endmodule // top
