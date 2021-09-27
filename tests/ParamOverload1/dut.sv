module dut(output int x);
   parameter int P [5] = '{1, 2, 3, 4, 5};
   assign x = P[2];
endmodule

module top(output int o);
   dut #(.P('{1000, 2000})) u_dut1(.x(o));
   dut u_dut2(.x(o));
   dut #(.P(3000)) u_dut3(.x(o));
endmodule // top

