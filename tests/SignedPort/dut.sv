
module dut (input logic signed [2:0] a, output logic unsigned [2:0] b);
  logic signed [2:0] c;
   assign b = $unsigned(a);
endmodule  

  
