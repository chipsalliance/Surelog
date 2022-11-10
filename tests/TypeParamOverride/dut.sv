package ariane_axi_soc;

typedef struct packed {
    logic         w_ready;
    logic         b_valid;
} resp_slv_t;

endpackage

module axi_err_slv #(
  parameter type  resp_t      = logic        
);
  
  resp_t  err_resp;

  always_comb begin : proc_w_channel
    err_resp.w_ready  = 1'b0;
    
  end
endmodule


module  ariane_testharness();

axi_err_slv #(
  .resp_t     ( ariane_axi_soc::resp_slv_t )
) i_gpio_err_slv (
);


endmodule
