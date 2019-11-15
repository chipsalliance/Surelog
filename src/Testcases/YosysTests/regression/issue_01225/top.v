module top(inout pin, input dout, sel, output din);
assign pin = sel ? dout : 1'bz;
assign din = pin;
endmodule
