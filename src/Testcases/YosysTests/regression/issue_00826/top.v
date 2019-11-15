`default_nettype none

module A;
parameter P = 0;
endmodule

module top;
A inst_i();
defparam inst_i.P = 1;
endmodule
