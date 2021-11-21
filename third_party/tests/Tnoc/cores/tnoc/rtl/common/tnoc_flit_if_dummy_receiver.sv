module tnoc_flit_if_dummy_receiver
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter int                 CHANNELS      = PACKET_CONFIG.virtual_channels,
  parameter bit                 READY         = '0,
  parameter bit                 VC_READY      = '0
)(
  tnoc_flit_if.receiver receiver_if
);
  assign  receiver_if.ready     = {CHANNELS{READY}};
  assign  receiver_if.vc_ready  = {CHANNELS{VC_READY}};
endmodule
