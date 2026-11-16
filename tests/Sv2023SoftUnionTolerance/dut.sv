// IEEE 1800-2023 additions:
//  7.3.1   `union soft`: a packed union whose members may differ in width,
//          each right-justified (packed is implied).
//  11.4.13 tolerance ranges in `inside`: [A +/- B] is [A-B : A+B] and
//          [A +%- B] is [A - A*B/100.0 : A + A*B/100.0].
module dut(input logic [7:0] a, input logic [15:0] w, input logic [3:0] b,
           output logic abs_in, rel_in, both,
           output logic [15:0] y, output logic [3:0] z);
  typedef union soft { logic [15:0] w; logic [3:0] n; } u_t;
  u_t u, v;
  always_comb begin
    u.w = w;
    z   = u.n;
    v.w = '0;
    v.n = b;
    y   = v.w ^ w;
  end
  assign abs_in = a inside {[8'd100 +/- 8'd5]};
  assign rel_in = a inside {[8'd50 +%- 8'd3]};
  assign both   = a inside {[8'd10 +/- 8'd2], [8'd200 : 8'd210]};
endmodule
