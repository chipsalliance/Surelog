function f(input i);
reg [1:0] mem0 [1:0];
f = i;
endfunction

module top(in,out);
input in;
output out;
assign out = f(in);
endmodule
