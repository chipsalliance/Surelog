module dut;
   parameter logic [1:0] RESVAL;
endmodule

module top;
   dut #(
      .RESVAL(~(2'h0))
   ) u_dut();
endmodule // top
