module rggen_axi4lite_bridge
  import  rggen_rtl_pkg::*;
#(
  parameter int ADDRESS_WIDTH = 16
)(
  input logic               i_clk,
  input logic               i_rst_n,
  rggen_bus_if.slave        bus_if,
  rggen_axi4lite_if.master  axi4lite_if
);
`ifndef SYNTHESIS
  initial begin
    assume (ADDRESS_WIDTH == axi4lite_if.ADDRESS_WIDTH);
  end
`endif

  logic       write_access;
  logic [2:0] request_done;

  //  Request
  assign  write_access        = bus_if.access[RGGEN_ACCESS_DATA_BIT];
  assign  axi4lite_if.awvalid = ((!request_done[0]) && write_access) ? bus_if.valid : '0;
  assign  axi4lite_if.awid    = '0;
  assign  axi4lite_if.awaddr  = ADDRESS_WIDTH'(bus_if.address);
  assign  axi4lite_if.awprot  = '0;
  assign  axi4lite_if.wvalid  = ((!request_done[1]) && write_access) ? bus_if.valid : '0;
  assign  axi4lite_if.wdata   = bus_if.write_data;
  assign  axi4lite_if.wstrb   = bus_if.strobe;
  assign  axi4lite_if.arvalid = (!(request_done[2] || write_access)) ? bus_if.valid : '0;
  assign  axi4lite_if.arid    = '0;
  assign  axi4lite_if.araddr  = ADDRESS_WIDTH'(bus_if.address);
  assign  axi4lite_if.arprot  = '0;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      request_done  <= '0;
    end
    else if (bus_if.ready) begin
      request_done  <= '0;
    end
    else begin
      if (axi4lite_if.awvalid && axi4lite_if.awready) begin
        request_done[0] <= '1;
      end
      if (axi4lite_if.wvalid && axi4lite_if.wready) begin
        request_done[1] <= '1;
      end
      if (axi4lite_if.arvalid && axi4lite_if.arready) begin
        request_done[2] <= '1;
      end
    end
  end

  //  Response
  assign  axi4lite_if.bready  = request_done[0] & request_done[1];
  assign  axi4lite_if.rready  = request_done[2];

  assign  bus_if.ready
    = (request_done[0] && request_done[1]) ? axi4lite_if.bvalid
    : (request_done[2]                   ) ? axi4lite_if.rvalid : '0;
  assign  bus_if.status
    = (request_done[0] && request_done[1]) ? rggen_status'(axi4lite_if.bresp)
    : (request_done[2]                   ) ? rggen_status'(axi4lite_if.rresp) : RGGEN_OKAY;
  assign  bus_if.read_data  = axi4lite_if.rdata;
endmodule
