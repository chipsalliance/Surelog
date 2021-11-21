module tnoc_flit_if_demux
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter int                 CHANNELS      = PACKET_CONFIG.virtual_channels,
  parameter int                 ENTRIES       = 2,
  parameter tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT
)(
  tnoc_types                    types,
  input var logic [ENTRIES-1:0] i_select,
  tnoc_flit_if.receiver         receiver_if,
  tnoc_flit_if.sender           sender_if[ENTRIES]
);
//--------------------------------------------------------------
//  Control signals
//--------------------------------------------------------------
  if (1) begin : g_control_signals
    logic [ENTRIES-1:0][CHANNELS-1:0] valid;
    logic [ENTRIES-1:0][CHANNELS-1:0] ready;
    logic [ENTRIES-1:0][CHANNELS-1:0] vc_ready;

    for (genvar i = 0;i < ENTRIES;++i) begin : g
      assign  sender_if[i].valid  = valid[i];
      assign  ready[i]            = sender_if[i].ready;
      assign  vc_ready[i]         = sender_if[i].vc_ready;
    end

    tbcm_selector #(
      .WIDTH    (CHANNELS ),
      .ENTRIES  (ENTRIES  ),
      .ONE_HOT  (1        )
    ) u_selector();

    assign  valid                 = u_selector.demux(i_select, receiver_if.valid);
    assign  receiver_if.ready     = u_selector.mux(i_select, ready);
    assign  receiver_if.vc_ready  = u_selector.mux(i_select, vc_ready);
  end

//--------------------------------------------------------------
//  Flit
//--------------------------------------------------------------
  for (genvar i = 0;i < ENTRIES;++i) begin : g_flit
    assign  sender_if[i].flit = receiver_if.flit;
  end
endmodule
