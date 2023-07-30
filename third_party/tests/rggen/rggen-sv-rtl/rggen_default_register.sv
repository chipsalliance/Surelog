module rggen_default_register #(
  parameter bit                     READABLE        = 1,
  parameter bit                     WRITABLE        = 1,
  parameter int                     ADDRESS_WIDTH   = 8,
  parameter bit [ADDRESS_WIDTH-1:0] OFFSET_ADDRESS  = '0,
  parameter int                     BUS_WIDTH       = 32,
  parameter int                     DATA_WIDTH      = BUS_WIDTH,
  parameter int                     VALUE_WIDTH     = BUS_WIDTH
)(
  input logic                 i_clk,
  input logic                 i_rst_n,
  rggen_register_if.register  register_if,
  rggen_bit_field_if.register bit_field_if
);
  rggen_register_common #(
    .READABLE       (READABLE       ),
    .WRITABLE       (WRITABLE       ),
    .ADDRESS_WIDTH  (ADDRESS_WIDTH  ),
    .OFFSET_ADDRESS (OFFSET_ADDRESS ),
    .BUS_WIDTH      (BUS_WIDTH      ),
    .DATA_WIDTH     (DATA_WIDTH     ),
    .VALUE_WIDTH    (VALUE_WIDTH    )
  ) u_register_common (
    .i_clk              (i_clk        ),
    .i_rst_n            (i_rst_n      ),
    .register_if        (register_if  ),
    .i_additional_match (1'b1         ),
    .bit_field_if       (bit_field_if )
  );
endmodule
