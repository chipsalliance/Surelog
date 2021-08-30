package my_pkg;
   typedef struct packed {
      logic p;
   } ast_dif_t;

   typedef struct packed {
      ast_dif_t [1:0] alerts_ack;
   } ast_alert_rsp_t;
endpackage // my_pkg

module top(output o);
   my_pkg::ast_alert_rsp_t ast_alert_o;
   always_comb begin
      ast_alert_o.alerts_ack[0].p = 1'b1;
   end
   assign o = ast_alert_o.alerts_ack[0].p;
endmodule // top
