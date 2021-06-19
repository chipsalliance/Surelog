module other
  #(parameter int Width = 1)
  (input logic[Width-1:0] in, output logic[Width-1:0] out);
   assign out = in;
endmodule;

module dut (input logic[7:0] in, output logic[7:0] out);
   other #(.Width($bits({in}))) oth(.in(in), .out(out));
endmodule
