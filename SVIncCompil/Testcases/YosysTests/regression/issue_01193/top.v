module test (input e, a, output reg b);
  always_comb
  	if (e)
  		b = a;
endmodule
