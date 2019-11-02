module graphtest(A, Y, Z);
  input [3:0] A;
  output [2:0] Y;
  output [1:0] Z;
  assign Y = { A[2:0] & 3'h2 };
  assign Z = A[2:1];
endmodule
