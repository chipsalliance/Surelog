module adc_ctrl_core;
   typedef struct packed {
      logic [9:0] min_v;
   } filter_ctl_t;

   filter_ctl_t [1:0][2:0] a;
   logic [9:0] x = a[0][0].min_v;
endmodule // adc_ctrl_core
