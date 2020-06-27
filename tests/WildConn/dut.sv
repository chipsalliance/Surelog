module MOD (input logic 
  a, 
  b
  );
endmodule

module top(input logic 
  a, 
  b
  );

  MOD u1 
  (
    .*
  );

endmodule
