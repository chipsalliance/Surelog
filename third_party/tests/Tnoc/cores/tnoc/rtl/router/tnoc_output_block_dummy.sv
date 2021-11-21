module tnoc_output_block_dummy
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG
)(
  tnoc_flit_if.receiver           receiver_if[5],
  tnoc_flit_if.sender             sender_if,
  tnoc_port_control_if.controller port_control_if[5]
);
  tnoc_flit_if_dummy_receiver_array #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .ENTRIES        (5              )
  ) u_dummy_receiver (receiver_if);

  tnoc_flit_if_dummy_sender u_dummy_sender (
    sender_if
  );

  for (genvar i = 0;i < 5;++i) begin : g
    always_comb begin
      port_control_if[i].grant  = '0;
    end
  end
endmodule
