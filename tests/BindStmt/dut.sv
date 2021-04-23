module bp_lce #(parameter sets_p = "inv")();
assign c =d;
endmodule

module bp_me_nonsynth_lce_tracer #(parameter sets_p = "inv")();
  assign a =b;
endmodule

module testbench ();

  bind bp_lce
            bp_me_nonsynth_lce_tracer
              #(.sets_p(sets_p))
              lce_tracer1();

  bind bp_lce:u1
            bp_me_nonsynth_lce_tracer
              #(.sets_p(sets_p))
              lce_tracer2();            


  bp_lce #(.sets_p(1)) u1 ();

endmodule
