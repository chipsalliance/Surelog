
module dut (input logic signed [2:0] a, output logic unsigned [2:0] b);
	assign b = $unsigned(a);
endmodule  

  
