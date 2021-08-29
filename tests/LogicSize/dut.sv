module dut(output logic a);
   parameter logic P = 0;
   assign a = P;
endmodule // dut

module top(output logic o);
   parameter logic X = 0;
   dut #(
      .P(~X)
   ) u_dut(
      .a(o)
   );
endmodule // top
