// Ranged enum members (LRM 6.19.1) on an ANONYMOUS enum: `step[10]` expands to
// step0..step9 (11..20 after start=10) and `stop[11:13]` to stop11..stop13.
// The typedef path already expanded them; the anonymous `enum {...} e;` path
// read the range bound as the member VALUE and emitted one constant `step`.
// Also: an implicit member FOLLOWS an explicit value (b = 11, not 1).
module top(output logic [31:0] s0, output logic [31:0] s9, output logic [31:0] t12,
           output logic [31:0] b_o);
  enum {start=10, step[10]} e;
  enum {first=10, stop[11:13]} f;
  enum {a=10, b} g;
  assign s0 = step0;
  assign s9 = step9;
  assign t12 = stop12;
  assign b_o = b;
endmodule
