module top(/*output [3:0] b*/);
  typedef struct packed {
    logic [1:0] addr;
    logic sel;
    logic rd;
  } complex_t;

  parameter complex_t RSP_DEFAULT = '{
    addr: '{default: '1},
    sel: 1'b0,
    rd: 1'b1
  };
 // assign b = RSP_DEFAULT;

endmodule
