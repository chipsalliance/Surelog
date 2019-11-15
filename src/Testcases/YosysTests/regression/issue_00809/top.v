module top(C, O, A, B);
   input  [3:0] A;
   input  [3:0] B;
   output [3:0] O;
   output       C;
   assign {C, O} = A + B;
endmodule
