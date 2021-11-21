module tnoc_flit_if_dummy_receiver_array
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter int                 CHANNELS      = PACKET_CONFIG.virtual_channels,
  parameter int                 ENTRIES       = 1,
  parameter bit                 READY         = '0,
  parameter bit                 VC_READY      = '0
)(
  tnoc_flit_if.receiver receiver_if[ENTRIES]
);
  for (genvar i = 0;i < ENTRIES;++i) begin : g
    assign  receiver_if[i].ready    = {CHANNELS{READY}};
    assign  receiver_if[i].vc_ready = {CHANNELS{VC_READY}};
  end
endmodule
