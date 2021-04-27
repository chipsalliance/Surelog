module bp_lce #(parameter sets_p = "inv")(input logic a, output logic b);
assign c =d;
endmodule

module bp_me_nonsynth_lce_tracer #(parameter sets_p = "inv")(input logic c, output logic d);
  assign a =b;
endmodule

module bp_me_nonsynth_lce_tracer2 #(parameter sets_p = "inv")(input logic a, output logic b, input logic clk);
  assign a =b;
endmodule

module testbench (input logic clk);

  bind bp_lce
            bp_me_nonsynth_lce_tracer
              #(.sets_p(sets_p + 1))
              lce_tracer1(.c(a), .d(b));


  bind bp_lce:u1
            bp_me_nonsynth_lce_tracer2
              #(.sets_p(sets_p))
              lce_tracer2(.*);            

  bind bp_lce:u1
            bp_me_nonsynth_lce_tracer_bad
              #(.sets_p(sets_p))
              lce_tracer3();  


  bp_lce #(.sets_p(1)) u1 ();

endmodule
