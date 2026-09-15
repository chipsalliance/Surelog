// A size cast of a struct localparam built with an assignment pattern, used
// as a child parameter whose bits steer a per-bit generate (OpenTitan
// lc_ctrl: `prim_const #(.ConstVal(HwRevWidth'(HwRev)))` with prim_generic's
// `if (ConstVal[i])` generate).  Both the literal-width cast `16'(S)` and the
// parameter-width cast `W'(S)` must fold the pattern: before the fix every
// bit took the `gen_lo` branch.
module k #(parameter int Width = 1, parameter logic [Width-1:0] ConstVal = '0) (
  output logic [Width-1:0] out_o
);
  for (genvar i = 0; i < Width; i++) begin : gen_bits
    if (ConstVal[i]) begin : gen_hi
      assign out_o[i] = 1'b1;
    end else begin : gen_lo
      assign out_o[i] = 1'b0;
    end
  end
endmodule

module ip #(parameter logic [7:0] A = '0, parameter logic [7:0] B = '0) (
  output logic [15:0] o_lit,
  output logic [15:0] o_par
);
  typedef struct packed { logic [7:0] a; logic [7:0] b; } s_t;
  localparam int W = $bits(s_t);
  localparam s_t S = '{a: A, b: B};
  k #(.Width(16), .ConstVal(16'(S))) u_lit (.out_o(o_lit));
  k #(.Width(W),  .ConstVal(W'(S)))  u_par (.out_o(o_par));
endmodule

module top (output logic [15:0] o_lit, output logic [15:0] o_par);
  ip #(.A(8'h81), .B(8'h42)) u_ip (.o_lit, .o_par);
endmodule
