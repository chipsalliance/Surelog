
module top #(parameter int W = 4) (input [31:0] rand_i);

typedef logic      [4:0][W:0] sheet_t;   // << Parameterized typespec

logic [$bits(sheet_t)-1:0] c0;
assign c0 = rand_i[1*$bits(sheet_t)+:$bits(sheet_t)];

endmodule

