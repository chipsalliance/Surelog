module top (
	input clk
);

  default clocking @(posedge clk); 
    default input #1step output negedge;
  endclocking

  global clocking cb @(posedge clk); endclocking
 
  clocking cb1 @(posedge clk);
    default input #1 output #2;
    input #1 from_Dut;
    output posedge to_Dut = top.to;
  endclocking

endmodule

