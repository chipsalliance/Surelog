module tnoc_output_switch
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT,
  parameter int                 CHANNELS      = PACKET_CONFIG.virtual_channels
)(
  tnoc_types              types,
  input   var logic       i_clk,
  input   var logic       i_rst_n,
  tnoc_flit_if.receiver   receiver_if[5],
  tnoc_flit_if.sender     sender_if,
  input   var logic [4:0] i_output_grant,
  output  var             o_output_free
);
  logic [4:0] port_ack;

  always_comb begin
    o_output_free = |port_ack;
  end

  for (genvar i = 0;i < 5;++i) begin : g
    always_comb begin
      port_ack[i] = (receiver_if[i].get_ack() != '0) ? '1 : '0;
    end
  end

  tnoc_flit_if #(
    PACKET_CONFIG, CHANNELS, PORT_TYPE
  ) flit_if(types);

  tnoc_flit_if_mux #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .CHANNELS       (CHANNELS       ),
    .ENTRIES        (5              ),
    .PORT_TYPE      (PORT_TYPE      )
  ) u_mux (
    .types        (types          ),
    .i_select     (i_output_grant ),
    .receiver_if  (receiver_if    ),
    .sender_if    (flit_if        )
  );

  tnoc_flit_if_slicer #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .CHANNELS       (CHANNELS       ),
    .PORT_TYPE      (PORT_TYPE      )
  ) u_slicer (
    .types        (types      ),
    .i_clk        (i_clk      ),
    .i_rst_n      (i_rst_n    ),
    .receiver_if  (flit_if    ),
    .sender_if    (sender_if  )
  );
endmodule
