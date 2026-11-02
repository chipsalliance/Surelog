// `struct packed signed { ... }` (LRM 7.2.1): the signing keyword follows
// `packed` in the struct header and is recorded as vpiSigned on the
// struct_typespec (UHDM #1175); the unsigned and unqualified forms stay
// unsigned.
module top(input logic [7:0] x, output logic signed [31:0] o_s,
           output logic signed [31:0] o_u, output logic signed [31:0] o_n);
  struct packed signed { bit [3:0] lo; bit [3:0] hi; } ps;
  struct packed unsigned { bit [3:0] lo; bit [3:0] hi; } pu;
  struct packed { bit [3:0] lo; bit [3:0] hi; } pn;
  typedef struct packed signed { logic [7:0] v; } ts_t;
  ts_t tv;
  always_comb begin ps = x; pu = x; pn = x; tv = x; end
  assign o_s = ps;   // -56 at x = 200
  assign o_u = pu;   // 200
  assign o_n = pn + tv;
endmodule
