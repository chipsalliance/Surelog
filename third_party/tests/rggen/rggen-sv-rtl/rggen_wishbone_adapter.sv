module rggen_wishbone_adapter
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
  parameter bit                     INSERT_SLICER       = 0,
  parameter bit                     USE_STALL           = '1
)(
  input logic             i_clk,
  input logic             i_rst_n,
  rggen_wishbone_if.slave wishbone_if,
  rggen_register_if.host  register_if[REGISTERS]
);
  rggen_bus_if #(ADDRESS_WIDTH, BUS_WIDTH)  bus_if();
  logic [1:0]                               request_valid;
  logic [ADDRESS_WIDTH-1:0]                 wb_adr;
  logic                                     wb_we;
  logic [BUS_WIDTH-1:0]                     wb_dat_w;
  logic [BUS_WIDTH/8-1:0]                   wb_sel;
  logic [1:0]                               response_valid;
  logic [BUS_WIDTH-1:0]                     response_data;

  always_comb begin
    wishbone_if.stall = request_valid[1];
    wishbone_if.ack   = response_valid[0];
    wishbone_if.err   = response_valid[1];
    wishbone_if.rty   = '0;
    wishbone_if.dat_r = response_data;
  end

  always_comb begin
    bus_if.valid  = (request_valid != '0) && (response_valid == '0);
    if (request_valid[1]) begin
      bus_if.access     = (wb_we) ? RGGEN_WRITE : RGGEN_READ;
      bus_if.address    = wb_adr;
      bus_if.write_data = wb_dat_w;
      bus_if.strobe     = wb_sel;
    end
    else begin
      bus_if.access     = (wishbone_if.we) ? RGGEN_WRITE : RGGEN_READ;
      bus_if.address    = ADDRESS_WIDTH'(wishbone_if.adr);
      bus_if.write_data = wishbone_if.dat_w;
      bus_if.strobe     = wishbone_if.sel;
    end
  end

  always_comb begin
    request_valid[0]  = wishbone_if.cyc && wishbone_if.stb;
  end

  generate
    if (USE_STALL) begin : g_stall
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          request_valid[1]  <= '0;
        end
        else if (response_valid != '0) begin
          request_valid[1]  <= '0;
        end
        else if (request_valid == 2'b01) begin
          request_valid[1]  <= '1;
        end
      end

      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          wb_adr    <= '0;
          wb_we     <= '0;
          wb_dat_w  <= '0;
        end
        else if (request_valid == 2'b01) begin
          wb_adr    <= ADDRESS_WIDTH'(wishbone_if.adr);
          wb_we     <= wishbone_if.we;
          wb_dat_w  <= wishbone_if.dat_w;
        end
      end
    end
    else begin : g_no_stall
      always_comb begin
        request_valid[1]  = '0;
        wb_adr            = '0;
        wb_we             = '0;
        wb_dat_w          = '0;
      end
    end
  endgenerate

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      response_valid  <= '0;
    end
    else if (response_valid != '0) begin
      response_valid  <= '0;
    end
    else if (bus_if.valid && bus_if.ready) begin
      if (bus_if.status[1]) begin
        response_valid  <= 2'b10;
      end
      else begin
        response_valid  <= 2'b01;
      end
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      response_data <= '0;
    end
    else if (bus_if.valid && bus_if.ready) begin
      response_data <= bus_if.read_data;
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
