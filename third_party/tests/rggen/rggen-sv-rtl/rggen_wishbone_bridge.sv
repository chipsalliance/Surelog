module rggen_wishbone_bridge
  import  rggen_rtl_pkg::*;
#(
  parameter int ADDRESS_WIDTH = 16,
  parameter bit USE_STALL     = '1
)(
  input var                 i_clk,
  input var                 i_rst_n,
  rggen_bus_if.slave        bus_if,
  rggen_wishbone_if.master  wishbone_if
);
`ifndef SYNTHESIS
  initial begin
    assume (ADDRESS_WIDTH == wishbone_if.ADDRESS_WIDTH);
  end
`endif

  logic request_done;

  always_comb begin
    wishbone_if.cyc   = bus_if.valid;
    wishbone_if.stb   = bus_if.valid && (!request_done);
    wishbone_if.adr   = ADDRESS_WIDTH'(bus_if.address);
    wishbone_if.we    = bus_if.access != RGGEN_READ;
    wishbone_if.dat_w = bus_if.write_data;
    wishbone_if.sel   = bus_if.strobe;
  end

  always_comb begin
    bus_if.ready      = wishbone_if.ack || wishbone_if.err || wishbone_if.rty;
    bus_if.status     = (wishbone_if.ack) ? RGGEN_OKAY : RGGEN_SLAVE_ERROR;
    bus_if.read_data  = wishbone_if.dat_r;
  end

  generate
    if (USE_STALL) begin : g_stall
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          request_done  <= '0;
        end
        else if (bus_if.valid && bus_if.ready) begin
          request_done  <= '0;
        end
        else if (wishbone_if.stb && (!wishbone_if.stall)) begin
          request_done  <= '1;
        end
      end
    end
    else begin : g_no_stall
      always_comb begin
        request_done  = '0;
      end
    end
  endgenerate
endmodule
