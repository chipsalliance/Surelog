module dut();                                                                                                                                                                                                      
typedef struct {                                                                                         
  int A;
  struct {
    logic B;
    int C;
  } BC1, BC2;
} ABC;

ABC test;

assign test = '{BC1: '{1'b1, 1}, int: 0, BC2: '{default: 0}};
endmodule

