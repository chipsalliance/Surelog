package lc_ctrl_pkg;

   parameter int TxWidth = 4;
   typedef enum logic [TxWidth-1:0] {
      On  = 4'b1010,
     Off = 4'b0101
    } lc_tx_e;
 
    typedef lc_tx_e lc_tx_t;
 
    parameter lc_tx_t LC_TX_DEFAULT = Off;

endpackage

module top();
import lc_ctrl_pkg::*;


endmodule
