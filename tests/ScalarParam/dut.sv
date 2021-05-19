module GOOD ();
endmodule

module param_test #(
parameter bit [3:0]     DRspDepth = 4'h2
) ();
   if (DRspDepth == 0) begin 
     GOOD good();
   end
endmodule;

module dut ();

  param_test #(
   .DRspDepth (4'h0)
  ) t1 ();

endmodule // dut
