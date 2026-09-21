// An assignment pattern under a CAST must stay an assignment pattern.
//
// `type'{field: value, default: value}` parses as a Concatenation, not an
// Assignment_pattern -- the parser only builds the latter for a BARE `'{...}`.
// Compiled as an ordinary expression its named field labels become operands in
// their own right, so the field NAMES came out as ref_objs and the result was
// a concat of the wrong width.
//
// PULP common_cells cc_id_queue hits this in an FF reset argument:
//
//     `FFARNC(linked_data_q[i], linked_data_d[i], clr_i,
//             linked_data_t'{free: 1'b1, default: '0}, clk_i, rst_ni)
//
// which produced signals literally named `free` and `default` (`default` is a
// SystemVerilog keyword), left them undriven, and reset the flop to the wrong
// value.  Downstream that made the module non-equivalent to the read_slang
// reference with 4 undriven nets.
//
// The pattern must come out as vpiAssignmentPatternOp with tagged_patterns,
// carrying the cast's typespec so a consumer can tell which member each tag
// names -- without the typespec `free: 1'b1` is lost to the `default: '0` and
// the reset value is all-zeros instead of free=1.
//
// `bare` below is the control: the same pattern with no cast always worked.
module dut (
  input  logic       clk_i,
  input  logic       rst_ni,
  input  logic [3:0] d_i,
  output logic [5:0] o_cast,
  output logic [5:0] o_bare
);
  typedef struct packed {
    logic       free;
    logic [3:0] data;
    logic       tail;
  } ent_t;

  ent_t q_cast, q_bare, d;

  assign d = '{free: 1'b0, data: d_i, tail: 1'b1};

  // cast + assignment pattern as an async reset value
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) q_cast <= ent_t'{free: 1'b1, default: '0};
    else         q_cast <= d;
  end

  // control: no cast
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) q_bare <= '{free: 1'b1, default: '0};
    else         q_bare <= d;
  end

  assign o_cast = q_cast;
  assign o_bare = q_bare;
endmodule
