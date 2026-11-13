// An instance-array member's port actual stays WHOLE (LRM 23.3.3.5): each
// member takes the whole actual when its width matches the port, slice k when
// it is N times wider -- a choice that depends on the PORT width.  Selecting
// bit <member index> gave every member one bit of the 8-bit `allbits`, one
// bit of the 2-bit-per-member `onebit`, and an out-of-range bit of
// `bitout[17:10]` (povik/sv-elab tests/various/regress.sv r15).
module r15sub(input [7:0] allbits, input [1:0] onebit, output bitout);
  assign bitout = allbits[onebit];
endmodule

module top(input [7:0] allbits, input [15:0] onebit, output [17:10] bitout);
  r15sub sub [7:0] (allbits, onebit, bitout);
endmodule
