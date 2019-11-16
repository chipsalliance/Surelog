// Generate a simple 8-bit latch
// Author: Niels A. Moseley
//         Moseley Instruments / Symbiotic EDA
//         02-11-2018
// 

module latch(input [7:0] din, input gate, output reg [7:0] dout);

  reg [7:0] state;

  always @(gate or din)
  begin
    if (gate == 1'b1)
    begin
      dout <= din;
    end
  end

endmodule