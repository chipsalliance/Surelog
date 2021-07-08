module dut (output logic o);
   assign o = 1'b1;
endmodule

module top (output logic o);
  
   dut d(.o(15'b0));

endmodule
