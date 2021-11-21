module tnoc_bfm_flit_if_connector
  import  tnoc_pkg::*,
          tnoc_bfm_types_pkg::*;
#(
  parameter   tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter   tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT,
  parameter   bit                 MONITOR_MODE  = 1,
  localparam  int                 CHANNELS      = PACKET_CONFIG.virtual_channels
)(
  tnoc_types        types,
  input var logic   i_clk,
  input var logic   i_rst_n,
  tnoc_flit_if      dut_if,
  tnoc_bfm_flit_if  bfm_if[CHANNELS]
);
  typedef types.tnoc_flit tnoc_flit;

  function automatic tnoc_flit convert_to_dut_flit(
    tnoc_bfm_flit bfm_flit
  );
    tnoc_flit dut_flit  = '{
      flit_type:  tnoc_flit_type'(bfm_flit.flit_type),
      head:       bfm_flit.head,
      tail:       bfm_flit.tail,
      data:       bfm_flit.data
    };
    return dut_flit;
  endfunction

  function automatic tnoc_bfm_flit convert_to_bfm_flit(
    tnoc_flit dut_flit
  );
    tnoc_bfm_flit bfm_flit  = '{
      flit_type:  tnoc_bfm_flit_type'(dut_flit.flit_type),
      head:       dut_flit.head,
      tail:       dut_flit.tail,
      data:       dut_flit.data
    };
    return bfm_flit;
  endfunction

  if (is_local_port(PORT_TYPE)) begin : g_local_port
    if (MONITOR_MODE) begin : g_monitor
      for (genvar i = 0;i < CHANNELS;++i) begin : g
        always_comb begin
          bfm_if[i].valid     = dut_if.valid[i];
          bfm_if[i].ready     = dut_if.ready[i];
          bfm_if[i].flit      = convert_to_bfm_flit(dut_if.flit[i]);
          bfm_if[i].vc_ready  = dut_if.vc_ready[i];
        end
      end
    end
    else begin : g_driver
      for (genvar i = 0;i < CHANNELS;++i) begin : g
        always_comb begin
          dut_if.valid[i]     = bfm_if[i].valid;
          bfm_if[i].ready     = dut_if.ready[i];
          dut_if.flit[i]      = convert_to_dut_flit(bfm_if[i].flit);
          bfm_if[i].vc_ready  = dut_if.vc_ready[i];
        end
      end
    end
  end
  else begin : g_internal_port
    if (MONITOR_MODE) begin : g_monitor
      for (genvar i = 0;i < CHANNELS;++i) begin : g
        always_comb begin
          bfm_if[i].valid     = dut_if.valid[i];
          bfm_if[i].ready     = dut_if.ready[i];
          bfm_if[i].flit      = convert_to_bfm_flit(dut_if.flit[0]);
          bfm_if[i].vc_ready  = dut_if.vc_ready[i];
        end
      end
    end
    else begin : g_driver
      logic [CHANNELS-1:0]          request;
      logic [CHANNELS-1:0]          grant;
      logic [CHANNELS-1:0]          free;
      tnoc_bfm_flit [CHANNELS-1:0]  bfm_flit;

      tbcm_round_robin_arbiter #(CHANNELS, 1) u_vc_arbiter (
        .clk        (i_clk    ),
        .rst_n      (i_rst_n  ),
        .i_request  (request  ),
        .o_grant    (grant    ),
        .i_free     (free     )
      );

      for (genvar i = 0;i < CHANNELS;++i) begin : g
        always_comb begin
          request[i]  = bfm_if[i].valid & bfm_if[i].vc_ready;
          free[i]     = bfm_if[i].ready;
          bfm_flit[i] = bfm_if[i].flit;
        end

        always_comb begin
          dut_if.valid[i] = bfm_if[i].valid & grant[i];
        end

        always_comb begin
          bfm_if[i].ready     = dut_if.ready[i] & grant[i];
          bfm_if[i].vc_ready  = dut_if.vc_ready[i];
        end
      end

      tbcm_selector #(
        .DATA_TYPE    (tnoc_bfm_flit  ),
        .ENTRIES      (CHANNELS       ),
        .ONE_HOT      (1              )
      ) u_selector();

      always_comb begin
        dut_if.flit[0]  = convert_to_dut_flit(
          u_selector.mux(grant, bfm_flit)
        );
      end
    end
  end
endmodule
