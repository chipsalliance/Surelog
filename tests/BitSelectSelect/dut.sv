
module top(output int o);
   typedef struct packed {
      logic [9:0] min_v;
   } filter_ctl_t;

   filter_ctl_t [1:0][2:0] a;
   assign a[0][0].min_v = '1;
endmodule
