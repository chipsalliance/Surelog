// A PART-SELECT of a struct-parameter field must select those bits, including
// in a GENERATE CONDITION: `P.SIZE` is 16, so `P.SIZE[3:0]` is 0 and
// `if (|P.SIZE[3:0])` is FALSE -- the `else` arm is the one to elaborate.
//
// The member walk carried only names and single indices, so the range was
// dropped and the whole member (16) came back: the `if` arm was elaborated and
// its guard `Sum >= P.SIZE[3:0]` degenerated to `Sum >= 0`, always true.
// openhwgroup/cvw's RASPredictor is written exactly this way
// (`if(|P.RAS_SIZE[Depth-1:0])`), and taking the wrong arm pinned its
// return-stack pointer at 0.
package pk;
  typedef struct packed { logic [31:0] SIZE; } cfg_t;
endpackage

module dut import pk::*; #(parameter cfg_t P = '{SIZE: 32'd16}) (
  input  logic [3:0] s,
  output logic [3:0] o,
  output logic [3:0] sel,
  output logic       red
);
  localparam D = 4;
  // Not a generate condition: these were already folded correctly.
  assign sel = P.SIZE[D-1:0];
  assign red = |P.SIZE[D-1:0];

  if (|P.SIZE[D-1:0]) begin : g
    assign o = 4'd0;
  end else begin : g
    assign o = s;
  end
endmodule
