module top();
wire o;
wire a;
wire b;
wire [3:0] i;
assign o = i == 4'hb ? a:b;
endmodule
