module dut (output logic o);
   assign o = 1'b1;
endmodule

module top (output logic o);
   typedef struct packed {
      logic 	  ping_p;
   } alert_rx_t;

   alert_rx_t  alert_rx_i;

   dut d(.o(alert_rx_i.ping_p));

   assign o = alert_rx_i.ping_p;
endmodule
