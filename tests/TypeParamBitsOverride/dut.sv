// `$bits(id_t)` of the instantiating module's TYPE PARAMETER, written as a
// child's parameter override actual.  Resolving the bare type-parameter name
// consulted the definition's data types and the instance netlist's
// param_assigns (built only by the later netlist elaboration), never the
// instance's own type-parameter binding, so `$bits` stayed an unfolded call:
// the child's IdWidth never became a constant, HtCapacity stayed an
// expression tree and the generate loop bounded by it elaborated ZERO
// scopes (common_cells id_queue under PULP axi_burst_splitter).  With the
// binding consulted, IdWidth folds to 4, HtCapacity to 4 and gen_ht has
// four scopes -- the same tree as the literal `.IdWidth(4)`.
module child #(
  parameter int unsigned IdWidth  = 0,
  parameter int unsigned Capacity = 0
) (
  input  logic               clk_i, rst_ni,
  input  logic [IdWidth-1:0] id_i,
  output logic [Capacity-1:0] hit_o
);
  localparam type id_t = logic [IdWidth-1:0];
  localparam int unsigned HtCapacity = (2**IdWidth <= Capacity) ? 2**IdWidth : Capacity;
  id_t ids_q [HtCapacity-1:0];
  for (genvar i = 0; i < HtCapacity; i++) begin : gen_ht
    always_ff @(posedge clk_i or negedge rst_ni)
      if (!rst_ni) ids_q[i] <= '0; else ids_q[i] <= id_i + i;
    assign hit_o[i] = (ids_q[i] == id_i);
  end
endmodule

module mid #(parameter type id_t = logic) (
  input  logic       clk_i, rst_ni,
  input  id_t        id_i,
  output logic [3:0] hit_o
);
  child #(.IdWidth($bits(id_t)), .Capacity(4)) u_child (.*);
endmodule

// The real shape (axi_burst_splitter_gran_counters): the type parameter is
// NOT overridden -- its DEFAULT `logic [IdWidth-1:0]` depends on the module's
// own value parameter, overridden by the parent.  That default arrives as a
// Constant_param_expression wrapping the Data_type, which compileTypespec
// rejected as an unsupported data type, so `id_t` had no typespec at all.
module counters #(
  parameter int unsigned IdWidth = 0,
  parameter type         id_t    = logic [IdWidth-1:0]
) (
  input  logic       clk_i, rst_ni,
  input  id_t        id_i,
  output logic [3:0] hit_o
);
  child #(.IdWidth($bits(id_t)), .Capacity(4)) u_child (.*);
endmodule

module dut (
  input  logic       clk_i, rst_ni,
  input  logic [3:0] id_i,
  output logic [3:0] hit_bound_o,
  output logic [3:0] hit_default_o
);
  mid      #(.id_t(logic [3:0])) u_mid (.clk_i, .rst_ni, .id_i, .hit_o(hit_bound_o));
  counters #(.IdWidth(4))        u_cnt (.clk_i, .rst_ni, .id_i, .hit_o(hit_default_o));
endmodule
