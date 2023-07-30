module rggen_apb_bridge
  import  rggen_rtl_pkg::*;
#(
  parameter int ADDRESS_WIDTH = 16
)(
  input logic         i_clk,
  input logic         i_rst_n,
  rggen_bus_if.slave  bus_if,
  rggen_apb_if.master apb_if
);
`ifndef SYNTHESIS
  initial begin
    assume (ADDRESS_WIDTH == apb_if.ADDRESS_WIDTH);
  end
`endif

  logic busy;

  //  Request
  assign  apb_if.psel     = bus_if.valid;
  assign  apb_if.penable  = (busy) ? bus_if.valid : '0;
  assign  apb_if.paddr    = ADDRESS_WIDTH'(bus_if.address);
  assign  apb_if.pprot    = '0;
  assign  apb_if.pwrite   = bus_if.access[RGGEN_ACCESS_DATA_BIT];
  assign  apb_if.pstrb    = bus_if.strobe;
  assign  apb_if.pwdata   = bus_if.write_data;

  //  Response
  assign  bus_if.ready      = (busy) ? apb_if.pready : '0;
  assign  bus_if.status     = (apb_if.pslverr) ? RGGEN_SLAVE_ERROR : RGGEN_OKAY;
  assign  bus_if.read_data  = apb_if.prdata;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      busy  <= '0;
    end
    else if (apb_if.penable && apb_if.pready) begin
      busy  <= '0;
    end
    else if (apb_if.psel) begin
      busy  <= '1;
    end
  end
endmodule
