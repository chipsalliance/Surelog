// PULP axi_lite_mailbox, reduced: the slave builds `r_chan_lite_t` over its
// own `parameter type data_t`, hands it to cc_spill_register as `.data_t(...)`,
// which relays `.data_t(data_t)` one hop further into cc_spill_register_flushable.
// At that SECOND hop the bare name `data_t` was resolved in the wrong scope --
// it picked the grandparent's `data_t` (the 64-bit word) instead of the parent's
// (the 66-bit struct) -- so the inner register was 64 bits wide and the two
// top bits of every stored response were lost (bit 65: r.data[63]).  Renaming
// the struct member's type (variant without the name clash) or removing the
// middle hop made it correct, which is what pinned it to name capture.
module leaf #(parameter type data_t = logic) (input logic clk, input data_t d_i, output data_t d_o);
  data_t q;
  always_ff @(posedge clk) q <= d_i;
  assign d_o = q;
endmodule
module mid #(parameter type data_t = logic) (input logic clk, input data_t d_i, output data_t d_o);
  leaf #(.data_t(data_t)) u (.clk(clk), .d_i(d_i), .d_o(d_o));
endmodule
module slave #(parameter int unsigned W = 32, parameter type data_t = logic [W-1:0]) (
  input logic clk, input logic [W-1:0] x, input logic [1:0] r, output logic [W+1:0] y);
  typedef struct packed { data_t data; logic [1:0] resp; } r_t;
  r_t in_s, out_s;
  assign in_s = '{data: x, resp: r};
  mid #(.data_t(r_t)) u (.clk(clk), .d_i(in_s), .d_o(out_s));
  assign y = out_s;
endmodule
module dut (input logic clk, input logic [63:0] x, input logic [1:0] r, output logic [65:0] y);
  typedef logic [63:0] word_t;
  slave #(.W(64), .data_t(word_t)) u (.clk(clk), .x(x), .r(r), .y(y));
endmodule
