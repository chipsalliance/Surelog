module tnoc_input_fifo
  import  tnoc_pkg::*;
#(
  parameter   tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter   tnoc_port_type      PORT_TYPE     = TNOC_LOCAL_PORT,
  parameter   int                 DEPTH         = 4,
  localparam  int                 CHANNELS      = PACKET_CONFIG.virtual_channels
)(
  tnoc_types            types,
  input var logic       i_clk,
  input var logic       i_rst_n,
  tnoc_flit_if.receiver receiver_if,
  tnoc_flit_if.sender   sender_if[CHANNELS]
);
  tnoc_types #(PACKET_CONFIG) types_temp(); //  Workaround for VCS's bug
  tnoc_flit_if #(PACKET_CONFIG, 1)  flit_vc_if[CHANNELS](types_temp);

  tnoc_vc_splitter #(
    .PACKET_CONFIG  (PACKET_CONFIG  ),
    .PORT_TYPE      (PORT_TYPE      )
  ) u_vc_splitter (
    .types        (types        ),
    .receiver_if  (receiver_if  ),
    .sender_if    (flit_vc_if   )
  );

  for (genvar i = 0;i < CHANNELS;++i) begin : g
    tnoc_flit_if_fifo #(
      .PACKET_CONFIG  (PACKET_CONFIG  ),
      .CHANNELS       (1              ),
      .DEPTH          (DEPTH          ),
      .THRESHOLD      (DEPTH -2       ),
      .DATA_FF_OUT    (0              ),
      .PORT_TYPE      (PORT_TYPE      )
    ) u_fifo (
      .types          (types          ),
      .i_clk          (i_clk          ),
      .i_rst_n        (i_rst_n        ),
      .i_clear        ('0             ),
      .o_empty        (),
      .o_almost_full  (),
      .o_full         (),
      .receiver_if    (flit_vc_if[i]  ),
      .sender_if      (sender_if[i]   )
    );
  end
endmodule
