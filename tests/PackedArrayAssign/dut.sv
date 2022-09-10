module top(output logic [9:0] o);
   typedef struct packed {
      logic [9:0] min_v;
   } filter_ctl_t;

   filter_ctl_t [1:0] a = '{10'd15, 10'd0};
   assign o = a[1];
endmodule
