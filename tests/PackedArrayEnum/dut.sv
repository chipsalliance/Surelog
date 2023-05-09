module top();
  

  typedef enum logic [13:0] {
    DecLcStTestUnlocked0 = 1,
    DecLcStTestLocked0 = 2
  } dec_lc_state_e;
  typedef dec_lc_state_e [17:0] ext_dec_lc_state_t;
  ext_dec_lc_state_t transition_target_d;
  
endmodule
