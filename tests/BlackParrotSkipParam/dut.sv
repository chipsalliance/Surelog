
module bsg_counter_set_en
  #(parameter max_val_p="inv"
    , parameter lg_max_val_lp=($clog2(max_val_p+1))
    , parameter reset_val_p=0
  ) ();
endmodule

module top ();
bsg_counter_set_en
 #(.lg_max_val_lp(10)
   ,.reset_val_p(0)
   )
 mtime_counter();

     
endmodule
