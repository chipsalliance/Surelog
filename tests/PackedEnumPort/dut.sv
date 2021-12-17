
package lc_ctrl_pkg;
   typedef enum logic [3:0] {
      On = 4'b1010
   } lc_tx_e;

   typedef lc_tx_e lc_tx_t;
endpackage : lc_ctrl_pkg


module lc_ctrl_fsm(
   //input lc_ctrl_pkg::lc_tx_t lc_clk_byp_ack_i,
  input logic lc_clk_byp_ack_i
);
 //  assign o = int'(lc_clk_byp_ack_i);
endmodule : lc_ctrl_fsm
/*
module prim_lc_sync(
   output lc_ctrl_pkg::lc_tx_t [0:0] lc_en_o
);
   assign lc_en_o = 4'b1011;
endmodule : prim_lc_sync
*/
module top(output int o, output int p);
  lc_ctrl_pkg::lc_tx_t [0:0] lc_clk_byp_ack;

  //logic [1:0] lc_clk_byp_ack;

  // prim_lc_sync u_prim_lc_sync_clk_byp_ack (
 //     .lc_en_o(lc_clk_byp_ack)
   //);
 //  assign p = int'(lc_clk_byp_ack[0]);

   lc_ctrl_fsm u_lc_ctrl_fsm (
      .lc_clk_byp_ack_i( lc_clk_byp_ack[0])
   );
endmodule : top
