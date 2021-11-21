module tnoc_flit_if_mux
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter int                 CHANNELS      = PACKET_CONFIG.virtual_channels,
  parameter int                 ENTRIES       = 2,
  parameter tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT
)(
  tnoc_types                    types,
  input var logic [ENTRIES-1:0] i_select,
  tnoc_flit_if.receiver         receiver_if[ENTRIES],
  tnoc_flit_if.sender           sender_if
);
//--------------------------------------------------------------
//  Control signals
//--------------------------------------------------------------
  if (1) begin : g_control_signals
    logic [ENTRIES-1:0][CHANNELS-1:0] valid;
    logic [ENTRIES-1:0][CHANNELS-1:0] ready;
    logic [ENTRIES-1:0][CHANNELS-1:0] vc_ready;

    for (genvar i = 0;i < ENTRIES;++i) begin : g
      assign  valid[i]                = receiver_if[i].valid;
      assign  receiver_if[i].ready    = ready[i];
      assign  receiver_if[i].vc_ready = vc_ready[i];
    end

    tbcm_selector #(
      .WIDTH    (CHANNELS ),
      .ENTRIES  (ENTRIES  ),
      .ONE_HOT  (1        )
    ) u_selector();

    assign  sender_if.valid = u_selector.mux(i_select, valid);
    assign  ready           = u_selector.demux(i_select, sender_if.ready);
    assign  vc_ready        = u_selector.demux(i_select, sender_if.vc_ready);
  end

//--------------------------------------------------------------
//  Flit
//--------------------------------------------------------------
  typedef types.tnoc_flit tnoc_flit;

  if (1) begin : g_flit
    tnoc_flit [ENTRIES-1:0] flit;

    for (genvar i = 0;i < ENTRIES;++i) begin : g
      assign  flit[i] = receiver_if[i].flit;
    end

    tbcm_selector #(
      .DATA_TYPE  (tnoc_flit  ),
      .ENTRIES    (ENTRIES    ),
      .ONE_HOT    (1          )
    ) u_selector();

    assign  sender_if.flit  = u_selector.mux(i_select, flit);
  end
endmodule
