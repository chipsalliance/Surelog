module select_bus(busout, bus0, bus1, bus2, bus3, enable, s);
parameter n = 16;
parameter Zee = 16'bz;
output [1:n] busout;
input [1:n] bus0, bus1, bus2, bus3;
input enable;
input [1:2] s;
tri [1:n] data;
// net declaration
// net declaration with continuous assignment
tri [1:n] busout = enable ? data : Zee;
// assignment statement with four continuous assignments
assign
data = (s == 0) ? bus0 : Zee,
data = (s == 1) ? bus1 : Zee,
data = (s == 2) ? bus2 : Zee,
data = (s == 3) ? bus3 : Zee;
endmodule
