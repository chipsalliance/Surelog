
module mod_param_dec_1
  #(parameter    DATA_WIDTH    = 8,
                 ADDRESS_WIDTH = 4,
                 FIFO_DEPTH    = (1 << ADDRESS_WIDTH));
endmodule


module mod_param_dec_2
  #(parameter    DATA_WIDTH    = 8,
                 ADDRESS_WIDTH = 4,
                 FIFO_DEPTH    = (1 << ADDRESS_WIDTH))
 (input wire clk,
  output wire half_clk);
endmodule
