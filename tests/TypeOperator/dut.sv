// IEEE 1800-2023 6.23: the type operator.  type(expr) names the type of an
// expression or variable; it can declare a variable, cast, and be compared in
// a generate condition.
module dut(input logic [5:0] a, input logic signed [3:0] s,
           output logic [5:0] y, output logic [7:0] z, output logic [3:0] w);
  var type(a) t;
  localparam type ST = type(s);
  ST sv;
  assign t  = a ^ 6'h2a;
  assign y  = t;
  assign sv = s;
  assign z  = 8'(sv);                 // sign-extends: ST is signed
  if (type(a) == type(logic [5:0])) begin : g_match
    assign w = a[3:0];
  end else begin : g_nomatch
    assign w = 4'hf;
  end
endmodule
