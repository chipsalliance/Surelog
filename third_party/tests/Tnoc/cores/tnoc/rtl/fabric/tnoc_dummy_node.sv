module tnoc_dummy_node
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG
)(
  tnoc_flit_if.receiver receiver_if,
  tnoc_flit_if.sender   sender_if
);
  tnoc_flit_if_dummy_receiver #(
    .PACKET_CONFIG  (PACKET_CONFIG  )
  ) u_dummy_receiver (receiver_if);

  tnoc_flit_if_dummy_sender u_dummy_sender (sender_if);
endmodule
