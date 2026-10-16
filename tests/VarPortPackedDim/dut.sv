// Ports declared with the `var` keyword and a packed range
// (rggen_bit_field_counter): `input var [W-1:0] i_up`.
module top #(
  parameter int UP_PORT_WIDTH   = 3,
  parameter int DOWN_PORT_WIDTH = 2,
  parameter int WIDTH           = 8
)(
  input   var                       i_clk,
  input   var                       i_rst_n,
  input   var                       i_clear,
  input   var [UP_PORT_WIDTH-1:0]   i_up,
  input   var [DOWN_PORT_WIDTH-1:0] i_down,
  output  var [WIDTH-1:0]           o_count
);
  logic [WIDTH-1:0] count;
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)      count <= '0;
    else if (i_clear)  count <= '0;
    else               count <= count + WIDTH'(i_up) - WIDTH'(i_down);
  end
  assign o_count = count;
endmodule
