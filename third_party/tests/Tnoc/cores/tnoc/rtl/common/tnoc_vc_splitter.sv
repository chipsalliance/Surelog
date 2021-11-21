module tnoc_vc_splitter
  import  tnoc_pkg::*;
#(
  parameter   tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter   tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT,
  localparam  int                 CHANNELS      = PACKET_CONFIG.virtual_channels
)(
  tnoc_types            types,
  tnoc_flit_if.receiver receiver_if,
  tnoc_flit_if.sender   sender_if[CHANNELS]
);
  for (genvar i = 0;i < CHANNELS;++i) begin : g
    always_comb begin
      sender_if[i].valid      = receiver_if.valid[i];
      receiver_if.ready[i]    = sender_if[i].ready;
      receiver_if.vc_ready[i] = sender_if[i].vc_ready;
    end

    if (is_local_port(PORT_TYPE)) begin : g
      always_comb begin
        sender_if[i].flit = receiver_if.flit[i];
      end
    end
    else begin : g
      always_comb begin
        sender_if[i].flit = receiver_if.flit;
      end
    end
  end
endmodule

