module top();
   struct {
  int A;
  struct {
    logic B;
    real C;
  } BC1, BC2;
} ABC = '{BC1: '{1'b1, 1.0}, int: 0, BC2: '{default: 0}};

endmodule : top
