// Tagged unions and pattern matching (IEEE 1800-2017 7.3.2, 12.6):
// tagged values, matches in ?: / if / case (with &&& guards), .* and .v
// pattern variables, and a structure pattern.
module dut(input  logic [1:0] sel,
           input  logic [7:0] d,
           output logic [7:0] y,
           output logic       m,
           output logic [7:0] z,
           output logic [3:0] s,
           output logic [9:0] t_o,
           output logic [7:0] k,
           output logic       g);
  typedef struct packed { logic [3:0] hi, lo; } pair_t;
  typedef union tagged packed {
    logic [3:0] a;
    logic [7:0] b;
    void        n;
    pair_t      p;
  } u_t;
  u_t t;
  always_comb begin
    case (sel)
      2'd0:    t = tagged a d[3:0];
      2'd1:    t = tagged b d;
      2'd2:    t = tagged n;
      default: t = tagged p '{hi: d[7:4], lo: d[3:0]};
    endcase
  end
  assign t_o = t;
  // conditional operator over a match, `.*` wildcard
  assign m = t matches tagged b .* ? 1'b1 : 1'b0;
  // conditional operator with &&& guards, with and without a pattern
  assign k = t matches tagged b .w &&& (w > 8'd3) &&& d[0] ? w : 8'd0;
  assign g = sel[0] &&& d[1] ? 1'b1 : 1'b0;
  // case matches: bindings, a guard, a default
  always_comb begin
    case (t) matches
      tagged a .v:                 y = {4'b0, v};
      tagged b .w &&& (w > 8'd3):  y = w;
      default:                     y = 8'hff;
    endcase
  end
  // if matches with a binding
  always_comb begin
    if (t matches tagged b .q) z = q + 8'd1;
    else z = 8'd0;
  end
  // structure pattern: a constant field and a bound field
  always_comb begin
    if (t matches tagged p '{4'h5, .l}) s = l;
    else s = 4'hf;
  end
endmodule
