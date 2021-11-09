module GOOD();
endmodule

package lc_ctrl_pkg;
   parameter int TxWidth = 4;
   typedef logic [TxWidth-1:0] unused_type_t;
endpackage : lc_ctrl_pkg

module top;
   import lc_ctrl_pkg::unused_type_t;
   parameter int TxWidth = 1;
   int           o;
   assign o = TxWidth;

  if (TxWidth == 1) begin
     GOOD good();
  end
   
endmodule
