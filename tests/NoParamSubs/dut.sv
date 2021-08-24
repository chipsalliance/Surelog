module dut(output logic [1:0] a);
   parameter logic [1:0] P = 0;
   assign a = P;
endmodule // dut

module top(output logic [1:0] o);
   parameter logic [1:0] X = '{0, 1};
   dut #(
      .P(~X)
   ) u_dut(
      .a(o)
   );
endmodule // top
