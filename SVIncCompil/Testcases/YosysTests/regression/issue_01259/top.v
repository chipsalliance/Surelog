module top();
	parameter W = 10;
	wire [W-1:0] x;
	empty #(.W(W)) empty_inst(.x(x));
endmodule

module empty#(parameter W = 0)(output wire [W-1:0] x);
endmodule
