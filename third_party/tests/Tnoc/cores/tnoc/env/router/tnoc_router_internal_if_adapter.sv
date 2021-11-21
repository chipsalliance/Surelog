module tnoc_rounter_internal_if_adapter
  `include  "tnoc_default_imports.svh"
#(
  parameter tnoc_config CONFIG  = TNOC_DEFAULT_CONFIG
)(
  input logic             clk,
  input logic             rst_n,
  tnoc_flit_if.target     flit_in_if,
  tnoc_flit_if.initiator  flit_out_if,
  tnoc_flit_if.target     flit_internal_in_if,
  tnoc_flit_if.initiator  flit_internal_out_if
);
  `include  "tnoc_macros.svh"
  localparam  int CHANNELS  = CONFIG.virtual_channels;

  if (1) begin : g_local_to_internal
    logic [CHANNELS-1:0]      request;
    logic [CHANNELS-1:0]      grant;
    logic [CHANNELS-1:0]      free;
    `tnoc_internal_flit_if(1) vc_if[CHANNELS]();

    assign  request = flit_in_if.valid & flit_in_if.vc_available;
    assign  free    = flit_in_if.ready;
    tbcm_round_robin_arbiter #(CHANNELS, 1) u_arbiter (
      .clk        (clk      ),
      .rst_n      (rst_n    ),
      .i_request  (request  ),
      .o_grant    (grant    ),
      .i_free     (free     )
    );

    tnoc_vc_demux #(
      CONFIG, TNOC_LOCAL_PORT
    ) u_vc_demux (
      flit_in_if, vc_if
    );

    tnoc_vc_mux #(
      CONFIG, TNOC_INTERNAL_PORT
    ) u_vc_mux (
      grant, vc_if, flit_internal_out_if
    );
  end

  if (1) begin : g_internal_to_local
    logic [CHANNELS-1:0]      request;
    logic [CHANNELS-1:0]      grant;
    logic [CHANNELS-1:0]      free;
    `tnoc_internal_flit_if(1) vc_if[CHANNELS]();

    assign  request = flit_internal_in_if.valid & flit_internal_in_if.vc_available;
    assign  free    = flit_internal_in_if.ready;
    tbcm_round_robin_arbiter #(CHANNELS, 1) u_arbiter (
      .clk        (clk      ),
      .rst_n      (rst_n    ),
      .i_request  (request  ),
      .o_grant    (grant    ),
      .i_free     (free     )
    );

    tnoc_vc_demux #(
      CONFIG, TNOC_INTERNAL_PORT
    ) u_vc_demux (
      flit_internal_in_if, vc_if
    );

    tnoc_vc_mux #(
      CONFIG, TNOC_LOCAL_PORT
    ) u_vc_mux (
      grant, vc_if, flit_out_if
    );
  end
endmodule
