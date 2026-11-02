// A struct member with a `rand` / `randc` qualifier (LRM 18.4) is still a
// member: the qualifier was taken for the member's data type and the member
// skipped, so this struct had NO members and measured 1 bit instead of 321.
parameter K = 9;
typedef struct {
  rand bit i;
  randc integer b[K:0];
  bit [7:0] plain;
} randstruct;
module top(output logic signed [31:0] nbits, output logic signed [31:0] nplain);
  randstruct s;
  assign nbits = $bits(randstruct);
  assign nplain = $bits(s.plain);
endmodule
