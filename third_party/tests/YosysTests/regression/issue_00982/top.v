module lfsr_24 (input clk, output dout);
  reg [24:1] state = 24'b0;
  always @(posedge clk)
    state <= { state[24-1:1], state[24] ~^ state[23] ~^ state[22] ~^ state[17] };
  assign dout = state[24];
endmodule
