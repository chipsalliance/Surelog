module tnoc_vc_mux
  import  tnoc_pkg::*;
#(
  parameter   tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter   tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT,
  localparam  int                 CHANNELS      = PACKET_CONFIG.virtual_channels
)(
  tnoc_types                      types,
  input var logic [CHANNELS-1:0]  i_vc_grant,
  tnoc_flit_if.receiver           receiver_if[CHANNELS],
  tnoc_flit_if.sender             sender_if
);
  typedef types.tnoc_flit tnoc_flit;

  if (is_local_port(PORT_TYPE)) begin : g_local_port
    for (genvar i = 0;i < CHANNELS;++i) begin : g
      always_comb begin
        sender_if.valid[i]      = receiver_if[i].valid;
        receiver_if[i].ready    = sender_if.ready[i];
        sender_if.flit[i]       = receiver_if[i].flit[0];
        receiver_if[i].vc_ready = sender_if.vc_ready[i];
      end
    end
  end
  else begin : g_internal_port
    tnoc_flit [CHANNELS-1:0]  flit;

    for (genvar i = 0;i < CHANNELS;++i) begin : g
      always_comb begin
        if (i_vc_grant[i]) begin
          sender_if.valid[i]    = receiver_if[i].valid;
          receiver_if[i].ready  = sender_if.ready[i];
        end
        else begin
          sender_if.valid[i]    = '0;
          receiver_if[i].ready  = '0;
        end

        flit[i]                 = receiver_if[i].flit[0];
        receiver_if[i].vc_ready = sender_if.vc_ready[i];
      end
    end

    tbcm_selector #(
      .DATA_TYPE  (tnoc_flit  ),
      .ENTRIES    (CHANNELS   ),
      .ONE_HOT    (1          )
    ) u_selector();

    always_comb begin
      sender_if.flit[0] = u_selector.mux(i_vc_grant, flit);
    end
  end
endmodule
