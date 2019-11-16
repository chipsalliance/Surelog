module adder (sum_out, carry_out, carry_in, ina, inb);
output carry_out;
output [3:0] sum_out;
input [3:0] ina, inb;
input carry_in;
wire carry_out, carry_in;
wire [3:0] sum_out, ina, inb;
assign {carry_out, sum_out} = ina + inb + carry_in;
endmodule
