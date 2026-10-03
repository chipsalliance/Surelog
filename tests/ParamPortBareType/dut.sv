module leaf #(parameter type addr_t = logic) (input addr_t a, output addr_t b);
  assign b = ~a;
endmodule
module mid #(
  parameter int unsigned W = 0,
  type addr_t = logic [W-1:0]
) (input addr_t a_i, output addr_t b_o, output logic [7:0] y);
  leaf #(.addr_t(addr_t)) u (.a(a_i), .b(b_o));
  assign y = a_i[7:0];
endmodule
module dut (input logic [31:0] a_i, output logic [31:0] b_o, output logic [7:0] y);
  mid #(.W(32)) u (.a_i(a_i), .b_o(b_o), .y(y));
endmodule
