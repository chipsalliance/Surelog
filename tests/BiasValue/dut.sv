module bp_be_rec_to_fp();
  localparam sp_exp_width_gp   = 8;
  localparam dp_exp_width_gp   = 11;
  localparam bias_adj_lp = (1 << sp_exp_width_gp) - (1 << dp_exp_width_gp);

  wire [sp_exp_width_gp:0] adjusted_exp = 2000 + bias_adj_lp;
  
  logic [bias_adj_lp: 0] wrong_range;
 
endmodule
