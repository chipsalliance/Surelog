// A `var` port with an unpacked dimension:
//   output var logic [XLEN-1:0] o [NUM_HARTS-1:0]
// is parsed through variable_port_header, whose dimension is a
// Variable_dimension wrapping the Unpacked_dimension.  The port compiler only
// captured the bare Unpacked_dimension form, so the port lost its unpacked
// dimension and elaborated as a scalar logic_var (CVW trickbox_apb's
// HGEIP_OUT read undriven on every element).  Both forms must elaborate the
// same array_var of NUM_HARTS elements.
module dut #(parameter XLEN = 64, parameter NUM_HARTS = 2) (
  input  logic              sel,
  input  logic [XLEN-1:0]   a[NUM_HARTS-1:0],
  input  logic [XLEN-1:0]   b[NUM_HARTS-1:0],
  output var logic [XLEN-1:0] o_var[NUM_HARTS-1:0],
  output logic [XLEN-1:0]   o_net[NUM_HARTS-1:0]
);
  genvar i;
  for (i = 0; i < NUM_HARTS; i++) begin : g
    assign o_var[i] = sel ? a[i] : b[i];
    assign o_net[i] = sel ? b[i] : a[i];
  end
endmodule
