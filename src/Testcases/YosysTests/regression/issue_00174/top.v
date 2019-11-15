module top
(
   input [5:0] ptr,
   output [5:0] wave_out
);
   wire [31:0] w = 1-ptr;
   assign wave_out = w/2;
endmodule
