module dut();

typedef struct packed {
  logic a;
  logic b;
} typedef_struct;

typedef_struct c;
logic test = 1'b1;
assign c = '{
  a : test == 1'b1 ? 1'b0 : 1'b1,
  b : 1'b1 ? 1'b1 : 1'b0
};

endmodule
