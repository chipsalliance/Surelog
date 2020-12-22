module t;
  localparam int unsigned I = 9;
  logic [I-4:0] sig;
  assign sig[I-7] = 3;
endmodule
