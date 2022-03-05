
module bar(clk);
  input  wire clk;

endmodule


module foo(clk);
(* this_is_clock *) input  wire clk;

  bar bar_instance_1 ( (* this_is_clock *) .clk(clk));
endmodule
