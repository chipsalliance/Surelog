module GOOD();
endmodule

module hierdefparam_top();
  generate begin:foo
    hierdefparam_a mod_a();
  end endgenerate
  defparam foo.mod_a.bar[0].mod_b.addvalue = 42;
  defparam foo.mod_a.bar[1].mod_b.addvalue = 43;
endmodule

module hierdefparam_a();
  genvar i;
  generate
    for (i = 0; i < 2; i=i+1) begin:bar
      hierdefparam_b mod_b();
    end
  endgenerate
  
endmodule

module hierdefparam_b();
  parameter [7:0] addvalue = 44;
  if (addvalue == 42) begin
	GOOD good0();
  end
  if (addvalue == 43) begin
     GOOD good1();
  end
  if (addvalue == 44) begin
	BAD bad();
  end
endmodule
