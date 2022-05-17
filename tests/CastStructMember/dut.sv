
typedef struct {
  int WIDTH;
} width_t;

module Foo ();
  localparam width_t w = width_t'{32};
  wire [31:0] t1 = w.WIDTH'(0);
  wire [31:0] t2 = w'(0);
endmodule


