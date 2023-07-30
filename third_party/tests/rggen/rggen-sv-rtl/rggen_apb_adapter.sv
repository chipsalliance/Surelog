module rggen_apb_adapter
  import  rggen_rtl_pkg::*;
#(
  parameter int                     ADDRESS_WIDTH       = 8,
  parameter int                     LOCAL_ADDRESS_WIDTH = 8,
  parameter int                     BUS_WIDTH           = 32,
  parameter int                     REGISTERS           = 1,
  parameter bit                     PRE_DECODE          = 0,
  parameter bit [ADDRESS_WIDTH-1:0] BASE_ADDRESS        = '0,
  parameter int                     BYTE_SIZE           = 256,
  parameter bit                     ERROR_STATUS        = 0,
  parameter bit [BUS_WIDTH-1:0]     DEFAULT_READ_DATA   = '0,
  parameter bit                     INSERT_SLICER       = 0
)(
  input logic             i_clk,
  input logic             i_rst_n,
  rggen_apb_if.slave      apb_if,
  rggen_register_if.host  register_if[REGISTERS]
);
  rggen_bus_if #(ADDRESS_WIDTH, BUS_WIDTH)  bus_if();

  assign  bus_if.valid      = (apb_if.psel && (!apb_if.pready)) ? '1 : '0;
  assign  bus_if.access     = (apb_if.pwrite) ? RGGEN_WRITE : RGGEN_READ;
  assign  bus_if.address    = apb_if.paddr[ADDRESS_WIDTH-1:0];
  assign  bus_if.write_data = apb_if.pwdata;
  assign  bus_if.strobe     = apb_if.pstrb;

  always_ff @(posedge i_clk , negedge i_rst_n) begin
    if (!i_rst_n) begin
      apb_if.pready <= '0;
    end
    else if (bus_if.valid && bus_if.ready) begin
      apb_if.pready <= '1;
    end
    else begin
      apb_if.pready <= '0;
    end
  end

  always_ff @(posedge i_clk) begin
    if (bus_if.valid && bus_if.ready) begin
      apb_if.prdata   <= bus_if.read_data;
      apb_if.pslverr  <= bus_if.status[1];
    end
  end

  rggen_adapter_common #(
    .ADDRESS_WIDTH        (ADDRESS_WIDTH        ),
    .LOCAL_ADDRESS_WIDTH  (LOCAL_ADDRESS_WIDTH  ),
    .BUS_WIDTH            (BUS_WIDTH            ),
    .REGISTERS            (REGISTERS            ),
    .PRE_DECODE           (PRE_DECODE           ),
    .BASE_ADDRESS         (BASE_ADDRESS         ),
    .BYTE_SIZE            (BYTE_SIZE            ),
    .ERROR_STATUS         (ERROR_STATUS         ),
    .DEFAULT_READ_DATA    (DEFAULT_READ_DATA    ),
    .INSERT_SLICER        (INSERT_SLICER        )
  ) u_adapter_common (
    .i_clk        (i_clk        ),
    .i_rst_n      (i_rst_n      ),
    .bus_if       (bus_if       ),
    .register_if  (register_if  )
  );
endmodule
