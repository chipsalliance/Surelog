module rggen_external_register
  import  rggen_rtl_pkg::*;
#(
  parameter int                     ADDRESS_WIDTH = 8,
  parameter int                     BUS_WIDTH     = 32,
  parameter int                     VALUE_WIDTH   = BUS_WIDTH,
  parameter bit [ADDRESS_WIDTH-1:0] START_ADDRESS = '0,
  parameter int                     BYTE_SIZE     = 0
)(
  input logic                 i_clk,
  input logic                 i_rst_n,
  rggen_register_if.register  register_if,
  rggen_bus_if.master         bus_if
);
  //  Decode address
  logic match;
  rggen_address_decoder #(
    .READABLE       (1'b1           ),
    .WRITABLE       (1'b1           ),
    .WIDTH          (ADDRESS_WIDTH  ),
    .BUS_WIDTH      (BUS_WIDTH      ),
    .START_ADDRESS  (START_ADDRESS  ),
    .BYTE_SIZE      (BYTE_SIZE      )
  ) u_decoder (
    .i_address          (register_if.address  ),
    .i_access           (register_if.access   ),
    .i_additional_match (1'b1                 ),
    .o_match            (match                )
  );

  //  Request
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      bus_if.valid  <= '0;
    end
    else if (bus_if.valid && bus_if.ready) begin
      bus_if.valid  <= '0;
    end
    else if (register_if.valid && match) begin
      bus_if.valid  <= '1;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      bus_if.address  <= '0;
      bus_if.access   <= RGGEN_READ;
    end
    else if (register_if.valid && match) begin
      bus_if.address  <= get_bus_address(register_if.address);
      bus_if.access   <= register_if.access;
    end
  end

  function automatic logic [ADDRESS_WIDTH-1:0] get_bus_address(
    logic [ADDRESS_WIDTH-1:0] address
  );
    return address - START_ADDRESS;
  endfunction

  always_ff @(posedge i_clk) begin
    if (register_if.valid && match) begin
      bus_if.write_data <= register_if.write_data;
      bus_if.strobe     <= register_if.strobe;
    end
  end

  //  Response
  assign  register_if.active    = match;
  assign  register_if.ready     = (bus_if.valid) ? bus_if.ready : '0;
  assign  register_if.status    = bus_if.status;
  assign  register_if.read_data = bus_if.read_data;
  assign  register_if.value     = VALUE_WIDTH'(bus_if.read_data);
endmodule
