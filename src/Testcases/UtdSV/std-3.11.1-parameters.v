module test;
parameter msb = 7;
parameter e = 25, f = 9;
parameter r = 5.7;
parameter byte_size = 8;
parameter byte_mask = byte_size -1;
parameter average_delay = (r + f)/2;
parameter signed [3:0] mux_selector = 0;
parameter real r1 = 3.5e17;
parameter p1 = 13'h7e;
parameter [31:0] dec_const = 1'b1;
parameter newconst = 3'h4;
parameter newconst = 4;
endmodule
