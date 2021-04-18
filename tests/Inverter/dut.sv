module top(input wire a,
	output wire b);
  inverter i1(a,tmp);
  inverter i2(tmp,b);
endmodule

module inverter(
	input wire a,
	output wire b
	);
assign b=~a;   
endmodule // inverter
