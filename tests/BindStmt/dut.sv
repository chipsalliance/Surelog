module bp_lce #(parameter sets_p = "inv")(input logic a, output logic b);
assign c =d;
endmodule

module sub();
endmodule

module bp_me_nonsynth_lce_tracer #(parameter sets_p = "inv")(input logic c, output logic d);
  assign a =b;
  sub sub1();
endmodule

module bp_me_nonsynth_lce_tracer2 #(parameter sets_p = "inv")(input logic a, output logic b, input logic clk);
  assign a =b;
  sub sub1();
endmodule


module inter ();

 bp_lce #(.sets_p(1)) u1 ();

endmodule

module testbench (input logic clk);

  bp_lce #(.sets_p(1)) u1 ();
  inter tt ();

  parameter p = 0;
  if (p == 0) begin : do_bind

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

  end

 
endmodule

