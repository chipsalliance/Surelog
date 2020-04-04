
module dut(input logic clk, output logic div); 

  always @(posedge clk)
    begin
      div <= !div;
    end
  
endmodule


