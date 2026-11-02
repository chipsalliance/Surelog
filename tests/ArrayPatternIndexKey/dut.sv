// An INDEX key in an array assignment pattern (LRM 10.9.1): `'{1: v, default:
// d}`.  The key was compiled as a TYPE (an integer_typespec) and lost; it is
// now the tagged_pattern's name, `default` stays a string_typespec tag.
module top(output logic [31:0] b1, output logic [31:0] b2, output logic [31:0] b3,
           output logic [7:0] c0, output logic [7:0] c2);
  typedef int triple [1:3];
  triple b = '{1: 1, default: 0};
  logic [7:0] c [0:2] = '{2: 8'h22, 0: 8'h00, 1: 8'h11};
  assign b1 = b[1];
  assign b2 = b[2];
  assign b3 = b[3];
  assign c0 = c[0];
  assign c2 = c[2];
endmodule
